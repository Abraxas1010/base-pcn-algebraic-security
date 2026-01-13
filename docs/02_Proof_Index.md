# Proof Index

This document catalogs all theorems and lemmas in the formalization.

---

## Core Feasibility Theorems

### `mem_WG_iff_forall_cutIntervalHolds`

**Location**: `CutCompleteness.lean:778`

**Statement**:
```lean
theorem mem_WG_iff_forall_cutIntervalHolds {G : ChannelGraph V} {w : V → Cap} :
    w ∈ Wealth.WG ↔ ∀ S : Finset V, cutIntervalHolds G w S
```

**Significance**: The main characterization theorem. Proves wealth feasibility is equivalent to satisfying all cut constraints.

**Proof Method**: Necessity by counting argument; sufficiency by Hall's marriage theorem.

---

### `cutIntervalHolds_of_mem_WG`

**Location**: `AlgorithmicCuts.lean`

**Statement**: If `w ∈ WG`, then `cutIntervalHolds G w S` for all `S`.

**Proof Method**: Direct calculation using liquidity conservation.

---

### `mem_WG_of_forall_cutIntervalHolds`

**Location**: `CutCompleteness.lean:105`

**Statement**: If all cuts satisfy constraints, then `w ∈ WG`.

**Proof Method**: Hall's theorem construction (copy/token matching).

---

## Rebalancing Theorems

### `pi_eq_of_circulation`

**Location**: `Rebalancing.lean`

**Statement**:
```lean
theorem pi_eq_of_circulation (hλ : λ ∈ LG G) (hf : IsBoundedCirculation G λ f) :
    Wealth.pi G (applyFlow λ f) = Wealth.pi G λ
```

**Significance**: Circulations (flows in cycles) preserve wealth.

**Proof Method**: Flow conservation at each vertex.

---

### `applyFlow_mem_LG`

**Location**: `Rebalancing.lean`

**Statement**: Applying a bounded circulation to a feasible state yields a feasible state.

---

## Quotient Theorems

### `quotientKer_piLG_equiv_WG`

**Location**: `Quotient.lean`

**Statement**:
```lean
theorem quotientKer_piLG_equiv_WG : (LG G) / WealthEquiv ≃ WG G
```

**Significance**: WG is exactly the quotient of LG by wealth equivalence.

---

## Replay Prevention Theorems

### `deliver_preserves_invariants`

**Location**: `MessageModelSeq.lean`

**Statement**:
```lean
theorem deliver_preserves_invariants (hinv : st.Invariants) (hsent : m ∈ st.sent) :
    (deliver st m).Invariants
```

**Significance**: Delivery operation preserves all state invariants.

**Proof Method**: Case split on message freshness.

---

### `runDeliveries_preserves_invariants`

**Location**: `MessageModelSeq.lean`

**Statement**: Iterated delivery preserves invariants.

**Proof Method**: Induction on message list.

---

### `replayPreventionStatement_holds`

**Location**: `MessageModelSeq.lean`

**Statement**: No duplicate keys in delivered set after any run.

---

## EVM Adapter Theorems

### `extractedEdges_loopless`

**Location**: `Extractor.lean:67`

**Statement**: Extracted graph has no self-loops.

---

### `extractChannelGraph_loopless`

**Location**: `Extractor.lean:106`

**Statement**: Full extraction produces loopless graph.

---

## Algorithmic Theorems

### `wgBool_eq_true_iff_mem_WG`

**Location**: `Algorithmic.lean`

**Statement**: The decidable check agrees with the specification.

---

### `paymentFeasibleBool_correct`

**Location**: `Algorithmic.lean`

**Statement**: Payment feasibility check is correct.

---

## Supporting Lemmas

### Cut Capacity Lemmas

| Lemma | Location | Description |
|-------|----------|-------------|
| `sum_edgeBound_eq` | Cuts.lean | Edge bounds sum correctly |
| `cutCapacity_incidentVerts_eq_zero` | CutCompleteness.lean | Full vertex set has zero cut |
| `internalCapacity_incidentVerts_eq_sum_cap` | CutCompleteness.lean | Full set has total capacity |

### Liquidity Lemmas

| Lemma | Location | Description |
|-------|----------|-------------|
| `le_cap_of_mem_LG` | Liquidity.lean | Per-endpoint balance ≤ capacity |

### Hall Construction Lemmas

| Lemma | Location | Description |
|-------|----------|-------------|
| `tokensWith_card` | CutCompleteness.lean | Token count equals capacity |
| `copiesWith_card` | CutCompleteness.lean | Copy count equals wealth |
| `hall` | CutCompleteness.lean | Hall's condition holds |

---

## Prop Assumptions (Not Axioms)

These are stated as properties, not axioms. Implementations must satisfy them.

| Property | Module | Description |
|----------|--------|-------------|
| `XMSSScheme.Correct` | XMSS.lean | Valid signatures verify |
| `XMSSScheme.EpochAdvances` | XMSS.lean | Signing increments epoch |
| `claimable` | PostQuantumHTLC.lean | Preimage satisfies hash-lock |

---

## Axiom Audit

**Standard axioms only**:
- `propext` (propositional extensionality)
- `Classical.choice` (choice principle)
- `Quot.sound` (quotient soundness)

**Verified via**: `#print axioms mem_WG_iff_forall_cutIntervalHolds`
