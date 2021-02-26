# Sett-Swap
A substrate pallet for atomically swapping funds from an origin to a target in SettCurrencies.
## Overview

A module for atomically swapping funds from an origin to a target. A proof
is used to allow the target to approve (claim) the swap. If the swap is not
claimed within a specified duration of time, the sender may cancel it.

## Interface

### Dispatchable Functions

* `create_swap` - called by a sender to register a new atomic swap
* `claim_swap` - called by the target to approve a swap
* `cancel_swap` - may be called by a sender after a specified duration

## Acknowledgement

This Pallet is inspired by the [atomic-swap](https://github.com/paritytech/substrate/tree/master/frame/atomic-swap) pallet originally developed by [Parity Tech](https://github.com/open-web3-stack/), for reference check [The Substrate Frame Repo](https://github.com/paritytech/substrate/tree/master/frame).