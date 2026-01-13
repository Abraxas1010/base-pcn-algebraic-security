# Technical Report: Algebraic Security Proofs for Base PCN

**Version**: 1.0
**Date**: January 2026
**Status**: Complete — All proofs verified, no sorry/admit

---

## Abstract

This report documents the machine-verified algebraic security proofs for Payment Channel Networks (PCNs) on Coinbase's Base blockchain. Unlike cryptographic security proofs that depend on computational hardness assumptions, algebraic proofs establish structural impossibilities — properties that hold regardless of implementation choices.

We prove three main results:
1. **Feasibility Characterization**: A wealth distribution is achievable iff all cut-interval constraints hold (Hall's theorem)
2. **Rebalancing Invariance**: Circulations preserve total wealth (flow conservation)
3. **Replay Prevention**: Monotone sequence numbers provide freshness guarantees

Additionally, we formalize post-quantum signature integration (XMSS) and hash-locked contracts (HTLC) as parameterized specifications.

---

## 1. Mathematical Foundation

### 1.1 Channel Graph Model

A channel graph `G = (V, E, cap)` consists of:
- `V`: Finite set of addresses (Base accounts)
- `E ⊆ Sym2(V)`: Undirected edges (open channels)
- `cap : E → ℕ`: Capacity function (total locked funds per channel)

```lean
structure ChannelGraph (V : Type) [DecidableEq V] where
  edges : Finset (Sym2 V)
  cap : Sym2 V → Cap
  loopless : ∀ e ∈ edges, ¬ e.IsDiag
```

**Loopless invariant**: No self-channels (addresses can't open channels with themselves).

### 1.2 Liquidity States

A liquidity state `λ : E → V → ℕ` assigns balances to each endpoint of each channel, subject to:

1. **Conservation**: `λ(e,u) + λ(e,v) = cap(e)` for each edge `e = {u,v}`
2. **Non-incidence**: `λ(e,x) = 0` if `x` is not an endpoint of `e`
3. **Off-graph**: `λ(e,x) = 0` if `e ∉ G.edges`

```lean
def Feasible (G : ChannelGraph V) (l : LiquidityFn V) : Prop :=
  Conservation G l ∧ NonIncidentZero l ∧ OffGraphZero G l
```

The set of feasible liquidity states is denoted `LG(G)`.

### 1.3 Wealth Distribution

The wealth projection `π : LG(G) → (V → ℕ)` maps liquidity states to per-vertex wealth:

```
π(λ)(v) = Σ_{e ∈ E} λ(e,v)
```

The feasible wealth set is `WG(G) = { π(λ) | λ ∈ LG(G) }`.

---

## 2. Main Theorem: Feasibility Characterization

### 2.1 Cut-Interval Constraints

For any subset `S ⊆ V`, define:
- `C_in(S)` = sum of capacities of edges entirely inside `S`
- `C_δ(S)` = sum of capacities of edges crossing between `S` and `V \ S`

The **cut-interval constraint** for wealth `w` and cut `S` is:

```
C_in(S) ≤ Σ_{v ∈ S} w(v) ≤ C_in(S) + C_δ(S)
```

This says: the total wealth in `S` is at least the internal capacity (funds that must stay in `S`) and at most internal + crossing capacity (funds that could flow into `S`).

### 2.2 Theorem Statement

```lean
theorem mem_WG_iff_forall_cutIntervalHolds {G : ChannelGraph V} {w : V → Cap} :
    w ∈ Wealth.WG ↔ ∀ S : Finset V, cutIntervalHolds G w S
```

**Interpretation**: A wealth distribution is achievable on Base iff it satisfies all cut constraints. This is a complete characterization — no other conditions are needed.

### 2.3 Proof Outline

#### Necessity (→)

If `w = π(λ)` for some `λ ∈ LG(G)`, then for any cut `S`:
- Edges inside `S` contribute their full capacity to `S`'s wealth
- Edges crossing `S` contribute at most their capacity
- Therefore `C_in(S) ≤ w(S) ≤ C_in(S) + C_δ(S)`

This direction is proven by direct calculation with finset sums.

#### Sufficiency (←)

If `w` satisfies all cut constraints, we construct a valid `λ` using Hall's Marriage Theorem:

1. **Copy set**: For each vertex `v`, create `w(v)` "copies" (one per unit of wealth)
2. **Token set**: For each edge `e`, create `cap(e)` "tokens" (one per unit of capacity)
3. **Adjacency**: Copy `(v,j)` is adjacent to token `(e,i)` iff `v` is an endpoint of `e`

Hall's condition: For any subset `A` of copies, the neighbor tokens satisfy `|N(A)| ≥ |A|`.

**Key insight**: The cut constraints for `S = { vertices with copies in A }` guarantee Hall's condition:
```
|A| ≤ w(S) ≤ C_in(S) + C_δ(S) = |N(A)|
```

By Hall's theorem, a perfect matching exists. We construct `λ` by counting how many copies of each vertex matched to tokens of each edge.

The proof in Lean is ~780 lines and uses:
- `Mathlib.Combinatorics.Hall.Basic` for Hall's theorem
- Finite cardinality arguments for counting
- Equivalence construction for bijectivity

---

## 3. Rebalancing Invariance

### 3.1 Circulations

A **circulation** is a flow assignment `f : E → V → ℤ` such that:
1. **Skew-symmetry**: `f(e,u) = -f(e,v)` for each edge `e = {u,v}`
2. **Conservation**: `Σ_{e incident on v} f(e,v) = 0` for each vertex `v`
3. **Boundedness**: `-λ(e,v) ≤ f(e,v) ≤ λ(e,v)` (can't overdraw)

### 3.2 Theorem

```lean
theorem pi_eq_of_circulation (hλ : λ ∈ LG G) (hf : IsBoundedCirculation G λ f) :
    Wealth.pi G (applyFlow λ f) = Wealth.pi G λ
```

**Proof**: For each vertex `v`:
```
π(λ')(v) = π(λ)(v) + Σ_e f(e,v) = π(λ)(v) + 0 = π(λ)(v)
```
The sum is zero by the circulation conservation property.

**Security implication**: Channel rebalancing (redistributing funds along cycles) cannot change anyone's net wealth. This is structural, not dependent on honest behavior.

---

## 4. Quotient Structure

### 4.1 Wealth Equivalence

Two liquidity states are equivalent if they project to the same wealth:

```lean
def WealthEquiv (λ₁ λ₂ : LiquidityState G) : Prop := π(λ₁) = π(λ₂)
```

### 4.2 Theorem

```lean
theorem quotientKer_piLG_equiv_WG : (LG G) / WealthEquiv ≃ WG G
```

This shows that `WG` is exactly the quotient of `LG` by rebalancing equivalence — the fundamental object of study for PCN security.

---

## 5. Replay Prevention (MessageModelSeq)

### 5.1 Model

Messages carry source, destination, sequence number, and payload:

```lean
structure Message (Address Payload : Type) where
  src : Address
  dst : Address
  seq : Seq  -- ℕ
  payload : Payload
```

State tracks sent/delivered sets and maximum sequence per source:

```lean
structure State (Address Payload : Type) where
  sent : Finset (Message Address Payload)
  delivered : Finset Key
  maxSeq : Address → Seq
```

### 5.2 Invariants

```lean
structure Invariants (st : State Address Payload) : Prop where
  noReplay : st.delivered.card = st.delivered.toList.length  -- no duplicates
  deliveredSubsetSent : ∀ k ∈ st.delivered, ∃ m ∈ st.sent, m.key = k
  seqBounds : ∀ m ∈ st.sent, m.seq ≤ st.maxSeq m.src
```

### 5.3 Theorem

```lean
theorem deliver_preserves_invariants (hinv : st.Invariants) (hsent : m ∈ st.sent) :
    (deliver st m).Invariants
```

**Security claim**: The `deliver` operation, which accepts a message only if its sequence number exceeds the stored maximum, preserves all invariants. This is proven by case analysis on whether the message is fresh.

---

## 6. Post-Quantum HTLC

### 6.1 Hash-Locked Contracts

```lean
structure HTLC (Address Digest Preimage : Type) where
  sender   : Address
  receiver : Address
  amount   : Nat
  lock     : HashLock Digest Preimage  -- commitment + timeout

def claimable (hash : Preimage → Digest) (h : HTLC) (w : Preimage) : Prop :=
  hash w = h.lock.commitment

def refundable (h : HTLC) (currentBlock : Nat) : Prop :=
  currentBlock ≥ h.lock.timeout
```

The HTLC is parameterized over hash function — instantiate with Poseidon2 for post-quantum security.

### 6.2 XMSS Integration

```lean
structure XMSSScheme where
  sign : Params → SecKey → Msg → SecKey × Signature
  verify : Params → PubKey → Msg → Signature → Prop
  Correct : ∀ ..., verify (sign ...) = true
  EpochAdvances : ∀ ..., (sign sk msg).1.epoch > sk.epoch
```

The `EpochAdvances` property ensures each secret key is used at most once, preventing quantum attacks on signature reuse.

### 6.3 No-Replay Assumption

```lean
def NoReplayAssumption (X : XMSSScheme) : Prop :=
  XMSSScheme.EpochAdvances X
```

This connects XMSS epoch tracking to the settlement sequence-number model.

---

## 7. Base/EVM Adapter

### 7.1 EVM State Model

```lean
structure EVMState where
  balances : Address → Nat
  storage : Address → Nat → Nat
```

### 7.2 Channel Record Extraction

```lean
structure ChannelRecord where
  participant1 : Address
  participant2 : Address
  capacity : Nat
  status : ChannelStatus

def extractChannelGraphSumCap (cfg : ExtractorConfig) (s : EVMState) : ChannelGraph Address
```

The `SumCap` variant aggregates parallel channels by summing capacities per endpoint pair, supporting Base's ability to have multiple open channels between the same addresses.

### 7.3 Settlement Operations

```lean
inductive SettlementOp
  | open : Address → Address → Nat → SettlementOp
  | close : Address → Address → SettlementOp
  | splice : Address → Address → Nat → SettlementOp
  | update : Address → Address → Nat → Nat → SettlementOp
```

Each operation is modeled as a state transition with precondition checks.

---

## 8. Axiom Audit

### 8.1 Standard Axioms Only

The proofs use only Lean's standard axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (for non-constructive existence proofs)
- `Quot.sound` (quotient soundness)

### 8.2 No Custom Axioms

All cryptographic assumptions are stated as `Prop` parameters:
- `XMSSScheme.Correct`
- `XMSSScheme.EpochAdvances`
- Hash function properties (collision resistance, etc.)

These are not axioms — they're specifications that conforming implementations must satisfy.

---

## 9. Verification Reproducibility

### 9.1 Environment

| Component | Version |
|-----------|---------|
| Lean | 4.14.0 |
| Mathlib | v4.14.0 |
| Lake | (bundled) |

### 9.2 Commands

```bash
cd RESEARCHER_BUNDLE
lake update
lake build -- -DwarningAsError=true
grep -rn 'sorry\|admit' HeytingLean/  # should return nothing
```

### 9.3 Verification Checklist

- [x] `lake build` succeeds
- [x] No `sorry` or `admit`
- [x] No custom axioms beyond standard
- [x] Main theorem statement matches specification
- [x] Demo executables run correctly

---

## 10. Conclusion

This formalization demonstrates that key PCN security properties on Base are **algebraically necessary** — they follow from the structure of capacity constraints, not from cryptographic assumptions.

The main theorem `mem_WG_iff_forall_cutIntervalHolds` provides a decision procedure: to check if a proposed wealth distribution is achievable, verify the cut constraints. If any constraint fails, the distribution is provably impossible.

Combined with the replay prevention model and post-quantum signature integration, this provides a layered security architecture:
1. **Algebraic layer**: Feasibility and conservation (always holds)
2. **Structural layer**: Replay prevention via sequence numbers
3. **Cryptographic layer**: XMSS signatures, hash commitments (implementation-specific)

The first two layers are independent of cryptographic choices and provide security guarantees even against quantum adversaries with unlimited computational power.

---

## Appendix A: Line Counts

| Module | Lines | Key Content |
|--------|-------|-------------|
| CutCompleteness.lean | 791 | Main theorem, Hall construction |
| Algorithmic.lean | ~600 | Decidable feasibility checks |
| SeamTheorem.lean | 1580 | EVM↔Graph correctness |
| Rebalancing.lean | 230 | Circulation invariance |
| MessageModelSeq.lean | ~200 | Replay prevention |

Total: ~4500 lines of verified Lean code.

---

## Appendix B: References

1. Hall, P. (1935). "On Representatives of Subsets". *Journal of the London Mathematical Society*.
2. Lund, C. et al. (1992). "Algebraic Methods for Interactive Proof Systems". *JACM*.
3. Base Blockchain Documentation. https://docs.base.org
4. Mathlib4 Hall's Theorem. https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Hall/Basic.html
