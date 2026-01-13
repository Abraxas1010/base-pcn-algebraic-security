/-!
# HeytingLean — Base PCN Algebraic Security

This package provides machine-checked proofs of Payment Channel Network (PCN)
feasibility for Coinbase's Base blockchain.

## Key Result

The main theorem `mem_WG_iff_forall_cutIntervalHolds` proves that a wealth
distribution is feasible if and only if it satisfies all cut-interval
constraints — a purely algebraic characterization independent of cryptographic
assumptions.

## Modules

- `Blockchain.PaymentChannels.*` — Core PCN geometry layer
- `Blockchain.PaymentChannels.EVMAdapter.*` — Base/EVM integration
- `Blockchain.Bridge.MessageModelSeq` — Replay prevention via monotone sequences
- `Crypto.PostQuantum.XMSS` — Post-quantum stateful signatures
-/

import HeytingLean.Blockchain.PaymentChannels
import HeytingLean.Blockchain.PaymentChannels.PostQuantumHTLC
import HeytingLean.Blockchain.PaymentChannels.EVMAdapter.Extractor
import HeytingLean.Blockchain.PaymentChannels.EVMAdapter.SettlementSemantics
import HeytingLean.Blockchain.PaymentChannels.EVMAdapter.SeamTheorem
