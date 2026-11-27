# theorem-s-lean

A Lean 4 proof of a lower bound on the expected number of oracle calls for zero-error quantum search with one marked item, for adaptive query algorithms whose workspace is a separable Hilbert space of any dimension and whose instruments have countably many outcomes per step. The finite case (finite-dimensional workspace, finitely many outcomes) is stated and proved separately. The files depend only on Mathlib.

The proofs were written with AI coding agents and checked by Lean's kernel. No human expert has reviewed the mathematics.

## What is proved

For every `N ≥ 4`, every finite workspace `K` and every zero-error adaptive query algorithm `A` on `ℂ^N ⊗ ℂ^2 ⊗ ℂ^K`, the average over the marked item of the expected number of queries satisfies

- `TheoremSFin`: `(1/N) ∑_x T_x ≥ (2 / arcsin(2/√N)) · (π/8 + 1/4) · (1 − 2/N)`, and
- `TheoremSFin'`: `(1/N) ∑_x T_x ≥ (π/8 + 1/4)·√N − 4/√N`.

For every `N ≥ 4`, every separable complex Hilbert space `K` (finite or infinite dimensional) and every zero-error adaptive query algorithm `A` on `ℂ^N ⊗ ℂ^2 ⊗ K` whose instruments have finitely or countably many outcomes, the same two bounds hold:

- `TheoremSInf`: `(1/N) ∑_x T_x ≥ (2 / arcsin(2/√N)) · (π/8 + 1/4) · (1 − 2/N)`, and
- `TheoremSInf'`: `(1/N) ∑_x T_x ≥ (π/8 + 1/4)·√N − 4/√N`.

All four inequalities are stated in `[0, ∞]`, with the left side passed through `ENNReal.ofReal`. The right side of `TheoremSFin'` and `TheoremSInf'` is negative for `N` in {4, 5, 6}, where `ofReal` makes it 0 and the claim says nothing. Since the average is at most `max_x T_x`, the worst case satisfies the same bounds; that corollary is not stated in Lean.

The proofs are `theoremSFin` and `theoremSFin'` in `TheoremS/Bound.lean`, and `theoremSInf` and `theoremSInf'` in `TheoremS/Inf/Bound.lean`. The countable case is proved directly, by the same argument with countable sums, not by reduction to the finite case. All four proofs depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. No file under `TheoremS/` contains `sorry`, `admit`, `native_decide`, `axiom` or `unsafe`.

## The model

The state space is `ℂ^N ⊗ ℂ^2 ⊗ ℂ^K` (address, marker bit, workspace), written as `EuclideanSpace ℂ (Fin N × Bool × K)` for a finite type `K`. The oracle for the marked item `x` is the permutation unitary `|y, b, w⟩ ↦ |y, b xor [y = x], w⟩`. The algorithm is a rooted tree of classical control, given as a map from finite lists of outcomes (newest first) to the kind of node reached. A query node applies the oracle and has one child. An operation node applies an instrument with a finite set of outcomes and Kraus operators `A_j` with `∑_j A_j† A_j = I`, with one child per outcome. A halt node is a leaf with an output in `Fin N`. Neither the initial state nor the tree depends on `x`, and paths may be infinite. The branch vector of a node is the initial state after the operators along its path; `p_x(h)` is its squared norm, the cost `T_x` is the sum of `p_x(h)` over query nodes (a value in `[0, ∞]`), the success probability `s_x` is the sum over halt nodes with output `x`, and zero error means `s_x = 1` for every `x`. All of this is in `TheoremS/Statement.lean`, which imports only Mathlib and defines the model and the claims without proving anything.

The countable model in `TheoremS/Inf/Statement.lean` (also Mathlib only) has the same tree, oracle and definitions of `p_x`, `T_x`, `s_x` and zero error. The workspace is any separable complex Hilbert space `K`, and the state space `ℂ^N ⊗ ℂ^2 ⊗ K` is written as `PiLp 2 (fun _ : Fin N × Bool => K)`, the ℓ² sum of `2N` copies of `K`. An operation node has an outcome set `J ⊆ ℕ`, finite or countably infinite, and bounded operators `A_j` with `∑_{j ∈ J} A_j† A_j = I` in the strong operator topology (an unordered sum). The separability hypothesis is part of the statement, as in the paper, but the proof does not use it.

## What is not proved here

- Instruments with an arbitrary measurable outcome space (outcome sets that are not countable). The paper proves the same bound for them on paper only.
- The paper's finite-memory lemma, which reduces the countable model to the finite one. The countable case is proved here directly, so that lemma is not needed and is not formalised.
- Anything beyond the mean. The theorem bounds the expected number of queries of a zero-error algorithm. It says nothing about the distribution of the number of queries, about bounded-error algorithms, or about non-uniform priors on the marked item.
- The matching upper bound (an algorithm with cost `(π/8 + 1/4)√N + O(1)`) is in the paper, not here.

## Files

| File | Content |
|---|---|
| `TheoremS/Statement.lean` | The model and the claims `TheoremSFin`, `TheoremSFin'` (Mathlib only) |
| `TheoremS/Potential.lean` | The potential `V(C, W) = W g(C/W)` and its properties (real analysis) |
| `TheoremS/Tree.lean` | Truncated sums over a tree of histories |
| `TheoremS/Mean.lean` | The mean vector and the one-step lemmas |
| `TheoremS/Bound.lean` | The proofs `theoremSFin`, `theoremSFin'` |
| `TheoremS/Inf/Statement.lean` | The countable model and the claims `TheoremSInf`, `TheoremSInf'` (Mathlib only) |
| `TheoremS/Inf/Potential.lean` | Countable subadditivity of the potential |
| `TheoremS/Inf/Tree.lean` | Tree sums in `[0, ∞]` with countably many children |
| `TheoremS/Inf/Mean.lean` | The one-step lemmas for the countable model |
| `TheoremS/Inf/Bound.lean` | The proofs `theoremSInf`, `theoremSInf'` |
| `checks/Axioms.lean` | Prints the four statements and the axioms of the four proofs |

## Building

Install [elan](https://github.com/leanprover/elan). In a clone:

```
lake exe cache get
lake build
lake env lean checks/Axioms.lean
```

The toolchain is Lean `v4.35.0` (`lean-toolchain`) and Mathlib is pinned by `lake-manifest.json` to commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`). The last command should print the four statements and, for each proof, `[propext, Classical.choice, Quot.sound]`. `CHECK.md` records a build from a clean clone.

## The paper

The theorem is Theorem S of the paper "The expected number of oracle calls for zero-error quantum search with classical control" (M. Moenius, in preparation), for instruments with countably many outcomes. The paper proves the theorem on paper also for measurable outcome spaces, with the matching upper bound, and explains where the constant `π/8 + 1/4` comes from.

## Licence

Apache-2.0, see `LICENSE`.
