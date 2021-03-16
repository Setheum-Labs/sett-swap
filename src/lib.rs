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

mod tests;


use sp_std::{prelude::*, marker::PhantomData, ops::{Deref, DerefMut}};
use sp_io::hashing::blake2_256;
use frame_support::{
	Parameter, decl_module, decl_storage, decl_event, decl_error, ensure,
	traits::{Get, ReservableCurrency as PalletReservableCurrency},
	weights::Weight,
	dispatch::DispatchResult,
};
use frame_system::{self as system, ensure_signed};
use codec::{Encode, Decode};
use sp_runtime::RuntimeDebug;

use serp_traits::{SettCurrencyReservable, BasicReservableCurrency, BalanceStatus};

/// Pending atomic swap operation.
#[derive(Clone, Eq, PartialEq, RuntimeDebug, Encode, Decode)]
pub struct PendingSwap<T: Config> {
	/// CurrencyId of the swap.
	pub currency_id: T::CurrencyId,
	/// Value of the swap.
	pub value: Self::Balance,
	/// Source of the swap.
	pub source: T::AccountId,
	/// Action of this swap.
	pub action: T::SettSwap,
	/// End block of the lock.
	pub end_block: T::BlockNumber,
}

/// Hashed proof type.
pub type HashedProof = [u8; 32];

/// Definition of a pending sett swap action. It contains the following three phrases:
///
/// - **Reserve**: reserve the resources needed for a swap. This is to make sure that **Claim**
/// succeeds with best efforts.
/// - **Claim**: claim any resources reserved in the first phrase.
/// - **Cancel**: cancel any resources reserved in the first phrase.
pub trait SettSwap<AccountId, T: Config> {
	/// Reserve the resources needed for the swap, from the given `source`. The reservation is
	/// allowed to fail. If that is the case, the the full swap creation operation is cancelled.
	fn reserve(currency_id: Self::CurrencyId, source: &AccountId, value: Self::Balance) -> DispatchResult;

	/// Claim the reserved resources, with `source` and `target`. Returns whether the claim
	/// succeeds.
	fn claim(currency_id: Self::CurrencyId, source: &AccountId, target: &AccountId, value: Self::Balance) -> bool;
	
	/// Weight for executing the operation.
	fn weight(&self) -> Weight;

	/// Cancel the resources reserved in `source`.
	fn cancel(currency_id: Self::CurrencyId, source: &AccountId, value: Self::Balance) -> Self::Balance;
}





/// SettSwap for SettCurrencySwappable
///
impl<T, GetCurrencyId> SettSwap<T::AccountId> for SettCurrencySettSwap<T, GetCurrencyId>
	where
	T: Config,
	GetCurrencyId: Get<T::CurrencyId>,
{
	/// Reserve the resources needed for the swap, from the given `source`. The reservation is
	/// allowed to fail. If that is the case, the the full swap creation operation is cancelled.
	fn reserve(currency_id: Self::CurrencyId, source: &AccountId, value: Self::Balance) -> DispatchResult {
		SettCurrencyReservable::reserve(
			currency_id: Self::CurrencyId, 
			source: &AccountId, 
			value: Self::Balance)
	}

	fn claim(currency_id: Self::CurrencyId, source: &AccountId, target: &AccountId, value: Self::Balance) -> bool {
		SettCurrencyReservable::repatriate_reserved(
		currency_id: Self::CurrencyId,
		source: &AccountId,
		target: &AccountId,
		value: Self::Balance,
		status: BalanceStatus::Free
		).is_ok()
	}

	fn weight(&self) -> Weight {
		T::DbWeight::get().reads_writes(1, 1)
	}

	fn cancel(currency_id: Self::CurrencyId, &self, source: &AccountId, value: Self::Balance) -> Self::Balance {
		SettCurrencyReservable::unreserve(
			currency_id: Self::CurrencyId, 
			source: &AccountId, 
			value: Self::Balance)
	}
}

/// A swap action that only allows transferring balances.
#[derive(Clone, RuntimeDebug, Eq, PartialEq, Encode, Decode)]
pub struct BasicSettSwap<AccountId, C: BasicReservableCurrency<AccountId>> {
	value: <C as BasicCurrency<AccountId>>::Balance,
	_marker: PhantomData<C>,
}

/// SettSwap for BasicReservableCurrency
///
impl<T, GetCurrencyId> SettSwap<T::AccountId> for BasicSettSwap<T, GetCurrencyId>
where
	Currency: BasicReservableCurrency<AccountId>,
	T: Config,
{
	/// Reserve the resources needed for the swap, from the given `source`. The reservation is
	/// allowed to fail. If that is the case, the the full swap creation operation is cancelled.
	fn reserve(source: &AccountId, value: Self::Balance -> DispatchResult {
		BasicReservableCurrency::reserve(
			who: &AccountId, 
			value: Self::Balance)
	}

	fn claim(source: &AccountId, target: &AccountId, value: Self::Balance) -> bool {
		BasicReservableCurrency::repatriate_reserved(
		source: &AccountId,
		target: &AccountId,
		value: Self::Balance,
		status: BalanceStatus::Free
		).is_ok()
	}

	fn weight(&self) -> Weight {
		T::DbWeight::get().reads_writes(1, 1)
	}

	fn cancel(source: &AccountId, value: Self::Balance) -> Self::Balance {
		BasicReservableCurrency::unreserve(
			source: &AccountId, 
			value: Self::Balance)
	}
}






/// SettSwap's pallet configuration trait.
pub trait Config: frame_system::Config {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;
	/// Swap action.
	type SettSwap: SettSwap<Self::AccountId, Self> + Parameter;
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

decl_storage! {
	trait Store for Module<T: Config> as SettSwap {
		pub PendingSwaps: double_map
			hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) HashedProof
			=> Option<PendingSwap<T>>;
	}
}


decl_error! {
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
}

decl_event!(
	/// Event of atomic swap pallet.
	pub enum Event<T> where
		AccountId = <T as system::Config>::AccountId,
		CurrencyId = <T as system::Config>::AccountId,
		Value = T::Balance,
		PendingSwap = PendingSwap<T>,
	{
		/// Swap created. \[account, proof, swap\]
		NewSwap(AccountId, CurrencyId, Value, HashedProof, PendingSwap),
		/// Swap claimed. The last parameter indicates whether the execution succeeds. 
		/// \[account, proof, success\]
		SwapClaimed(AccountId, CurrencyId, Value, HashedProof, bool),
		/// Swap cancelled. \[account, proof\]
		SwapCancelled(AccountId, CurrencyId, Value, HashedProof),
	}
);
	
/// Module definition of atomic swap pallet.
decl_module! {
	/// Module definition of atomic swap pallet.
	pub struct Module<T: Config> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Register a new atomic swap, declaring an intention to send funds from origin to target
		/// on the current blockchain. The target can claim the fund using the revealed proof. If
		/// the fund is not claimed after `duration` blocks, then the sender can cancel the swap.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `currency_id`: Currency of the atomic swap.
		/// - `value`: Funds to be sent from origin.
		/// - `target`: Receiver of the atomic swap.
		/// - `hashed_proof`: The blake2_256 hash of the secret proof.
		/// - `duration`: Locked duration of the atomic swap. For safety reasons, it is recommended
		///   that the revealer uses a shorter duration than the counterparty, to prevent the
		///   situation where the revealer reveals the proof too late around the end block.
		#[weight = T::DbWeight::get().reads_writes(1, 1).saturating_add(40_000_000)]
		fn create_swap(
			origin,
			target: T::AccountId,
			currency_id: T::CurrencyId,
			value: Self::Balance,
			hashed_proof: HashedProof,
			action: T::SettSwap,
			duration: T::BlockNumber,
		) {
			let source = ensure_signed(origin)?;
			ensure!(
				!PendingSwaps::<T>::contains_key(&target, currency_id: T::CurrencyId, value: Self::Balance, hashed_proof),
				Error::<T>::AlreadyExist
			);

			action.reserve(&source, currency_id: T::CurrencyId, value: Self::Balance,)?;

			let swap = PendingSwap {
				source,
				action,
				currency_id: T::CurrencyId, 
				value: Self::Balance,
				end_block: frame_system::Module::<T>::block_number() + duration,
			};
			PendingSwaps::<T>::insert(target.clone(), currency_id: T::CurrencyId.clone(), value: Self::Balance.clone(), hashed_proof.clone(), swap.clone());

			Self::deposit_event(
				RawEvent::NewSwap(target, currency_id: T::CurrencyId, value: Self::Balance, hashed_proof, swap)
			);
		}

		/// Claim an atomic swap.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `currency_id`: Currency of the atomic swap.
		/// - `value`: Funds to be sent from origin.
		/// - `proof`: Revealed proof of the claim.
		/// - `action`: Action defined in the swap, it must match the entry in blockchain. Otherwise
		///   the operation fails. This is used for weight calculation.
		#[weight = T::DbWeight::get().reads_writes(1, 1)
		  .saturating_add(40_000_000)
		  .saturating_add((proof.len() as Weight).saturating_mul(100))
		  .saturating_add(action.weight())
		]
		fn claim_swap(
			origin,
			proof: Vec<u8>,
			action: T::SettSwap,
			currency_id: T::CurrencyId,
			value: Self::Balance,
		) -> DispatchResult {
			ensure!(
				proof.len() <= T::ProofLimit::get() as usize,
				Error::<T>::ProofTooLarge,
			);

			let target = ensure_signed(origin)?;
			let hashed_proof = blake2_256(&proof);

			let swap = PendingSwaps::<T>::get(&target, currency_id: T::CurrencyId, value: Self::Balance, hashed_proof)
				.ok_or(Error::<T>::InvalidProof)?;
			ensure!(swap.action == action, Error::<T>::ClaimActionMismatch);

			let succeeded = swap.action.claim(&swap.source, currency_id: T::CurrencyId, value: Self::Balance, &target);

			PendingSwaps::<T>::remove(target.clone(), currency_id: T::CurrencyId.clone(), value: Self::Balance.clone(), hashed_proof.clone());

			Self::deposit_event(
				RawEvent::SwapClaimed(target, currency_id: T::CurrencyId, value: Self::Balance, hashed_proof, succeeded)
			);

			Ok(())
		}

		/// Cancel an atomic swap. Only possible after the originally set duration has passed.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `currency_id`: Currency of the atomic swap.
		/// - `value`: Funds to be sent from origin.
		/// - `target`: Target of the original atomic swap.
		/// - `hashed_proof`: Hashed proof of the original atomic swap.
		#[weight = T::DbWeight::get().reads_writes(1, 1).saturating_add(40_000_000)]
		fn cancel_swap(
			origin,
			target: T::AccountId,
			currency_id: T::CurrencyId,
			value: Self::Balance,
			hashed_proof: HashedProof,
		) {
			let source = ensure_signed(origin)?;

			let swap = PendingSwaps::<T>::get(&target, currency_id: T::CurrencyId, value: Self::Balance, hashed_proof)
				.ok_or(Error::<T>::NotExist)?;
			ensure!(
				swap.source == source,
				Error::<T>::SourceMismatch,
			);
			ensure!(
				frame_system::Module::<T>::block_number() >= swap.end_block,
				Error::<T>::DurationNotPassed,
			);

			swap.action.cancel(&swap.source, currency_id: T::CurrencyId, value: Self::Balance,);
			PendingSwaps::<T>::remove(&target, currency_id: T::CurrencyId.clone(), value: Self::Balance.clone(), hashed_proof.clone());

			Self::deposit_event(
				RawEvent::SwapCancelled(target, currency_id: T::CurrencyId, value: Self::Balance, hashed_proof)
			);
		}
	}
}	
