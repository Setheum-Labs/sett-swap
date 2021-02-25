# Sett-Swap
A substrate pallet for atomically swapping funds from an origin to a target in SettCurrencies.

- [`atomic_swap::Trait`](https://docs.rs/pallet-atomic-swap/latest/pallet_atomic_swap/trait.Trait.html)
- [`Call`](https://docs.rs/pallet-atomic-swap/latest/pallet_atomic_swap/enum.Call.html)
- [`Module`](https://docs.rs/pallet-atomic-swap/latest/pallet_atomic_swap/struct.Module.html)

## Overview

A module for atomically sending funds from an origin to a target. A proof
is used to allow the target to approve (claim) the swap. If the swap is not
claimed within a specified duration of time, the sender may cancel it.

## Interface

### Dispatchable Functions

* `create_swap` - called by a sender to register a new atomic swap
* `claim_swap` - called by the target to approve a swap
* `cancel_swap` - may be called by a sender after a specified duration

## Acknowledgement

This Pallet is inspired by the [atomic-swap](https://github.com/paritytech/substrate/tree/master/frame/atomic-swap) pallet originally developed by [Parity Tech](https://github.com/paritytech), for reference check [The Substrate Frame Repo](https://github.com/paritytech/substrate/tree/master/frame).