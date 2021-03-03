//! # Sett-Swap
//! A substrate pallet for atomically swapping funds from an origin to a target in SettCurrencies.
//!
//! ## Overview
//! 
//! A module for atomically swapping funds from an origin to a target. A proof
//! is used to allow the target to approve (claim) the swap. If the swap is not
//! claimed within a specified duration of time, the sender may cancel it.
//! 
//! ## Interface
//! 
//! ### Dispatchable Functions
//! 
//! * `create_swap` - called by a sender to register a new atomic swap
//! * `claim_swap` - called by the target to approve a swap
//! * `cancel_swap` - may be called by a sender after a specified duration

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::unused_unit)]

use codec::Codec;
use sp_std::{
	prelude::*, marker::PhantomData, 
	ops::{Deref, DerefMut}, fmt::Debug,
	convert::{TryFrom, TryInto}, result,
};
use sp_io::hashing::blake2_256;
use frame_support::{
	pallet_prelude::*,
	Parameter, ensure,
	traits::Get,
	weights::Weight,
};
 
use serp_traits::{
	account::MergeAccount,
	arithmetic::{Signed, SimpleArithmetic},
	BalanceStatus, BasicCurrency, BasicCurrencyExtended, 
	BasicLockableCurrency, BasicReservableCurrency,
	LockIdentifier, SettCurrency, SettCurrencyExtended, 
	SettCurrencyLockable, SettCurrencyReservable, 
	SettCurrencySwappable,
};
use sp_runtime::{
	traits::{CheckedSub, MaybeSerializeDeserialize, StaticLookup, Zero},
	RuntimeDebug,
	DispatchError, 
	DispatchResult,
};


}

mod tests;

pub use module::*;
pub use double_map::StorageDoubleMap;

#[frame_support::pallet]
pub mod module {
	use super::*;

	/// Hashed proof type.
	pub type HashedProof = [u8; 32];

	/// Definition of a pending sett swap action. It contains the following three phrases:
	///
	/// - **Reserve**: reserve the resources needed for a swap. This is to make sure that **Claim**
	/// succeeds with best efforts.
	/// - **Claim**: claim any resources reserved in the first phrase.
	/// - **Cancel**: cancel any resources reserved in the first phrase.
	pub trait SwapAction<AccountId, T: Config> {
		/// Reserve the resources needed for the swap, from the given `source`. The reservation is
		/// allowed to fail. If that is the case, the the full swap creation operation is cancelled.
		fn reserve(&self, source: &AccountId) -> DispatchResult;
		/// Claim the reserved resources, with `source` and `target`. Returns whether the claim
		/// succeeds.
		fn claim(&self, source: &AccountId, target: &AccountId) -> bool;
		/// Weight for executing the operation.
		fn weight(&self) -> Weight;
		/// Cancel the resources reserved in `source`.
		fn claim(&self, source: &AccountId);
	}

	/// SettSwap's pallet configuration trait.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;
		/// Swap action.
		type SwapAction: SwapAction<Self::AccountId, Self> + Parameter;
		/// Limit of proof size.
		///
		/// An atomic swap is only atomic if once the proof is revealed, both parties can submit the proofs
		/// on-chain. If A is the one that generates the proof, then it requires that either:
		/// - A's blockchain has the same proof length limit as B's blockchain.
		/// - Or A's blockchain has shorter proof length limit as B's blockchain.
		///
		/// If B sees A is on a blockchain with larger proof length limit, then it should kindly refuse
		/// to accept the atomic swap request if A generates the proof, and asks that B generates the
		/// proof instead.
		type ProofLimit: Get<u32>;
	}

	#[pallet::error]
	pub enum Error for Module<T: Config> {
		/// Swap already exists.
		AlreadyExist,
		/// Swap proof is invalid.
		InvalidProof,
		/// Proof is too large.
		ProofTooLarge,
		/// Source does not match.
		SourceMismatch,
		/// Swap has already been claimed.
		AlreadyClaimed,
		/// Swap does not exist.
		NotExist,
		/// Claim action mismatch.
		ClaimActionMismatch,
		/// Duration has not yet passed for the swap to be cancelled.
		DurationNotPassed,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	#[pallet::metadata(T::AccountId = "AccountId")]
	#[pallet::metadata(T::PendingSwap = "PendingSwap")]
	/// Event of SettSwap pallet.
	pub enum Event<T: Config> {
		/// Swap created. \[account, proof, swap\]
		NewSwap(AccountId, HashedProof, PendingSwap),
		/// Swap claimed. The last parameter indicates whether the execution succeeds. 
		/// \[account, proof, success\]
		SwapClaimed(AccountId, HashedProof, bool),
		/// Swap cancelled. \[account, proof\]
		SwapCancelled(AccountId, HashedProof),
	}

	#[pallet::storage]
	#[pallet::getter(fn pending_swaps)]
	pub type PendingSwaps<T: Config> = StorageDoubleMap<
		_,
		hasher(twox_64_concat) T::AccountId,
		hasher(blake2_128_concat) HashedProof,
		ValueQuery,
	>;

	/// Module definition of atomic swap pallet.
	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);
	
	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {}

	#[pallet::call]
	#[pallet::metadata(T::Error = "Error")]
	impl<T: Config> Pallet<T> {
		/// The pallet's dispatchable functions.
		fn deposit_event() = default;

		/// Register a new atomic swap, declaring an intention to send funds from origin to target
		/// on the current blockchain. The target can claim the fund using the revealed proof. If
		/// the fund is not claimed after `duration` blocks, then the sender can cancel the swap.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `target`: Receiver of the atomic swap.
		/// - `hashed_proof`: The blake2_256 hash of the secret proof.
		/// - `balance`: Funds to be sent from origin.
		/// - `duration`: Locked duration of the atomic swap. For safety reasons, it is recommended
		///   that the revealer uses a shorter duration than the counterparty, to prevent the
		///   situation where the revealer reveals the proof too late around the end block.
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1).saturating_add(40_000_000))]
		fn create_swap(
			origin,
			target: T::AccountId,
			hashed_proof: HashedProof,
			action: T::SwapAction,
			duration: T::BlockNumber,
		) {
			let source = ensure_signed(origin)?;
			ensure!(
				!PendingSwaps::<T>::contains_key(&target, hashed_proof),
				Error::<T>::AlreadyExist
			);

			action.reserve(&source)?;

			let swap = PendingSwap {
				source,
				action,
				end_block: frame_system::Module::<T>::block_number() + duration,
			};
			PendingSwaps::<T>::insert(target.clone(), hashed_proof.clone(), swap.clone());

			Self::deposit_event(
				RawEvent::NewSwap(target, hashed_proof, swap)
			);
		}

		/// Claim an atomic swap.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `proof`: Revealed proof of the claim.
		/// - `action`: Action defined in the swap, it must match the entry in blockchain. Otherwise
		///   the operation fails. This is used for weight calculation.
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1)
		.saturating_add(40_000_000)
		.saturating_add((proof.len() as Weight).saturating_mul(100))
		.saturating_add(action.weight()))
		]
		fn claim_swap(
			origin,
			proof: Vec<u8>,
			action: T::SwapAction,
		) -> DispatchResult {
			ensure!(
				proof.len() <= T::ProofLimit::get() as usize,
				Error::<T>::ProofTooLarge,
			);

			let target = ensure_signed(origin)?;
			let hashed_proof = blake2_256(&proof);

			let swap = PendingSwaps::<T>::get(&target, hashed_proof)
				.ok_or(Error::<T>::InvalidProof)?;
			ensure!(swap.action == action, Error::<T>::ClaimActionMismatch);

			let succeeded = swap.action.claim(&swap.source, &target);

			PendingSwaps::<T>::remove(target.clone(), hashed_proof.clone());

			Self::deposit_event(
				RawEvent::SwapClaimed(target, hashed_proof, succeeded)
			);

			Ok(())
		}

		/// Cancel an atomic swap. Only possible after the originally set duration has passed.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `target`: Target of the original atomic swap.
		/// - `hashed_proof`: Hashed proof of the original atomic swap.
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1).saturating_add(40_000_000))]
		fn cancel_swap(
			origin,
			target: T::AccountId,
			hashed_proof: HashedProof,
		) {
			let source = ensure_signed(origin)?;

			let swap = PendingSwaps::<T>::get(&target, hashed_proof)
				.ok_or(Error::<T>::NotExist)?;
			ensure!(
				swap.source == source,
				Error::<T>::SourceMismatch,
			);
			ensure!(
				frame_system::Module::<T>::block_number() >= swap.end_block,
				Error::<T>::DurationNotPassed,
			);

			swap.action.cancel(&swap.source);
			PendingSwaps::<T>::remove(&target, hashed_proof.clone());

			Self::deposit_event(
				RawEvent::SwapCancelled(target, hashed_proof)
			);
		}
	}
}	
/// A swap action that only allows transferring balances.
#[derive(Clone, RuntimeDebug, Eq, PartialEq, Encode, Decode)]
pub struct BalanceSwapAction<AccountId, C: ReservableCurrency<AccountId>> {
	value: <C as Currency<AccountId>>::Balance,
	_marker: PhantomData<C>,
}

/// Pending atomic swap operation.
#[derive(Clone, Eq, PartialEq, RuntimeDebug, Encode, Decode)]
pub struct PendingSwap<T: Config> {
	/// Source of the swap.
	pub source: T::AccountId,
	/// Action of this swap.
	pub action: T::SwapAction,
	/// End block of the lock.
	pub end_block: T::BlockNumber,
}

impl<AccountId, C> BalanceSwapAction<AccountId, C> where C: ReservableCurrency<AccountId> {
	/// Create a new swap action value of balance.
	pub fn new(value: <C as Currency<AccountId>>::Balance) -> Self {
		Self { value, _marker: PhantomData }
	}
}

impl<AccountId, C> Deref for BalanceSwapAction<AccountId, C> where C: ReservableCurrency<AccountId> {
	type Target = <C as Currency<AccountId>>::Balance;

	fn deref(&self) -> &Self::Target {
		&self.value
	}
}

impl<AccountId, C> DerefMut for BalanceSwapAction<AccountId, C> where C: ReservableCurrency<AccountId> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.value
	}
}

impl<T: Config, AccountId, C> SwapAction<AccountId, T> for BalanceSwapAction<AccountId, C>
	where C: ReservableCurrency<AccountId>
{
	fn reserve(&self, source: &AccountId) -> DispatchResult {
		C::reserve(&source, self.value)
	}

	fn claim(&self, source: &AccountId, target: &AccountId) -> bool {
		C::repatriate_reserved(source, target, self.value, BalanceStatus::Free).is_ok()
	}

	fn weight(&self) -> Weight {
		T::DbWeight::get().reads_writes(1, 1)
	}

	fn cancel(&self, source: &AccountId) {
		C::unreserve(source, self.value);
	}
}