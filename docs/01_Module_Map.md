# Module Map

This document maps Lean modules to their mathematical concepts.

## Core PCN Geometry

### `HeytingLean.Blockchain.PaymentChannels.Graph`

**Concept**: Undirected channel graph with per-edge capacities.

**Key Types**:
- `ChannelGraph V` — Graph structure with edges, capacities, loopless invariant
- `ne_of_mem_edges` — Endpoints are distinct

---

### `HeytingLean.Blockchain.PaymentChannels.Liquidity`

**Concept**: Feasible liquidity assignments satisfying conservation laws.

**Key Types**:
- `LiquidityFn V` — Type alias for `Sym2 V → V → Cap`
- `LiquidityFn.LG` — Set of feasible liquidity states
- `Conservation`, `NonIncidentZero`, `OffGraphZero` — Constraint predicates

---

### `HeytingLean.Blockchain.PaymentChannels.Wealth`

**Concept**: Wealth projection from liquidity to per-vertex totals.

**Key Types**:
- `Wealth.pi` — Projection function `λ ↦ (v ↦ Σ_e λ(e,v))`
- `Wealth.WG` — Feasible wealth set (image of LG under π)

---

### `HeytingLean.Blockchain.PaymentChannels.Cuts`

**Concept**: Cut capacities and interval constraints.

**Key Types**:
- `internalCapacity G S` — Sum of capacities inside cut S
- `cutCapacity G S` — Sum of capacities crossing cut S
- `cutIntervalHolds G w S` — The cut constraint predicate

---

### `HeytingLean.Blockchain.PaymentChannels.CutCompleteness`

**Concept**: Main feasibility theorem via Hall's marriage theorem.

**Key Theorems**:
- `mem_WG_iff_forall_cutIntervalHolds` — **THE MAIN RESULT**
- `mem_WG_of_forall_cutIntervalHolds` — Sufficiency (Hall construction)

---

### `HeytingLean.Blockchain.PaymentChannels.Rebalancing`

**Concept**: Circulations preserve wealth distribution.

**Key Theorems**:
- `pi_eq_of_circulation` — Rebalancing invariance

---

### `HeytingLean.Blockchain.PaymentChannels.Quotient`

**Concept**: LG quotiented by wealth equivalence equals WG.

**Key Theorems**:
- `quotientKer_piLG_equiv_WG` — Quotient isomorphism

---

## EVM Adapter Layer

### `HeytingLean.Blockchain.PaymentChannels.EVMAdapter.State`

**Concept**: EVM state model with balances and storage.

**Key Types**:
- `EVMState` — Blockchain state snapshot
- `ChannelRecord` — On-chain channel data

---

### `HeytingLean.Blockchain.PaymentChannels.EVMAdapter.Extractor`

**Concept**: Extract channel graph from EVM state.

**Key Functions**:
- `extractChannelGraph` — Max capacity per endpoint pair
- `extractChannelGraphSumCap` — Sum capacity (parallel-channel correct)

---

### `HeytingLean.Blockchain.PaymentChannels.EVMAdapter.SettlementSemantics`

**Concept**: Channel operations as state transitions.

**Key Functions**:
- `settlementStep` — Apply one settlement operation

---

## Security Infrastructure

### `HeytingLean.Blockchain.Bridge.MessageModelSeq`

**Concept**: Replay prevention via monotone sequence numbers.

**Key Types**:
- `Message` — Payload with sequence number
- `State` — Sent/delivered tracking
- `Invariants` — No replay, freshness bounds

**Key Theorems**:
- `deliver_preserves_invariants` — Monotone delivery

---

### `HeytingLean.Blockchain.PaymentChannels.PostQuantumHTLC`

**Concept**: Hash-locked contracts with PQ signature hooks.

**Key Types**:
- `HTLC` — Hash time-locked contract
- `Signed.Bundle` — XMSS-signed message

---

### `HeytingLean.Crypto.PostQuantum.XMSS`

**Concept**: XMSS stateful signature specification.

**Key Types**:
- `XMSSScheme` — Sign/verify with epoch tracking
- `EpochAdvances` — No key reuse property

---

## Dependency Graph

```
Graph.lean
    ↓
Liquidity.lean
    ↓
Wealth.lean
    ↓
Cuts.lean → AlgorithmicCuts.lean → Algorithmic.lean
    ↓
CutCompleteness.lean ←── Rebalancing.lean
    ↓                         ↓
Quotient.lean          PostQuantumHTLC.lean
                              ↑
                    MessageModelSeq.lean + XMSS.lean

EVMAdapter/State.lean → FromEVMState.lean → Extractor.lean
                                    ↓
                        SettlementSemantics.lean → SeamTheorem.lean
```
