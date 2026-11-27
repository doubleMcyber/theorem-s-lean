# theorem-s-lean

A Lean 4 proof of a lower bound on the expected number of oracle calls for zero-error quantum search with one marked item, for adaptive query algorithms whose workspace is a separable Hilbert space of any dimension. Three models are stated and proved separately: finitely many outcomes per step with a finite-dimensional workspace, countably many outcomes per step, and instruments whose outcome is a point of an arbitrary measurable space, with every later step depending measurably on the earlier outcomes. The files depend only on Mathlib.

The proofs were written with AI coding agents and checked by Lean's kernel. No human expert has reviewed the mathematics.

## What is proved

For every `N ≥ 4`, every finite workspace `K` and every zero-error adaptive query algorithm `A` on `ℂ^N ⊗ ℂ^2 ⊗ ℂ^K`, the average over the marked item of the expected number of queries satisfies

- `TheoremSFin`: `(1/N) ∑_x T_x ≥ (2 / arcsin(2/√N)) · (π/8 + 1/4) · (1 − 2/N)`, and
- `TheoremSFin'`: `(1/N) ∑_x T_x ≥ (π/8 + 1/4)·√N − 4/√N`.

For every `N ≥ 4`, every separable complex Hilbert space `K` (finite or infinite dimensional) and every zero-error adaptive query algorithm `A` on `ℂ^N ⊗ ℂ^2 ⊗ K` whose instruments have finitely or countably many outcomes, the same two bounds hold:

- `TheoremSInf`: `(1/N) ∑_x T_x ≥ (2 / arcsin(2/√N)) · (π/8 + 1/4) · (1 − 2/N)`, and
- `TheoremSInf'`: `(1/N) ∑_x T_x ≥ (π/8 + 1/4)·√N − 4/√N`.

For every `N ≥ 4`, every separable complex Hilbert space `K`, every family of nonempty measurable outcome spaces `Ω_1, Ω_2, …` and every zero-error algorithm `A` with measurable outcomes on `ℂ^N ⊗ ℂ^2 ⊗ K`, the same two bounds hold:

- `TheoremSMeasGen`: `(1/N) ∑_x T_x ≥ (2 / arcsin(2/√N)) · (π/8 + 1/4) · (1 − 2/N)`, and
- `TheoremSMeasGen'`: `(1/N) ∑_x T_x ≥ (π/8 + 1/4)·√N − 4/√N`.

`TheoremSMeas` and `TheoremSMeas'` are the same two claims restricted to standard Borel outcome spaces, so they follow from the general ones. Here `T_x` is computed from the history measures of `A` (see the model below). The four claims quantify over every family of history measures of `A`; `historyExists` proves that every algorithm has one for every marked item, so the claims are not vacuous, and `historyUnique` proves that any two agree on measurable sets, so `T_x` and `s_x` do not depend on the choice.

All eight inequalities are stated in `[0, ∞]`, with the left side passed through `ENNReal.ofReal`. The right side of `TheoremSFin'`, `TheoremSInf'`, `TheoremSMeasGen'` and `TheoremSMeas'` is negative for `N` in {4, 5, 6}, where `ofReal` makes it 0 and the claim says nothing. Since the average is at most `max_x T_x`, the worst case satisfies the same bounds; that corollary is not stated in Lean.

The proofs are `theoremSFin` and `theoremSFin'` in `TheoremS/Bound.lean`, `theoremSInf` and `theoremSInf'` in `TheoremS/Inf/Bound.lean`, and `theoremSMeasGen`, `theoremSMeasGen'`, `theoremSMeas` and `theoremSMeas'` in `TheoremS/Meas/Bound.lean` (with `historyExists` and `historyUnique` in `TheoremS/Meas/Hist.lean`). The countable case is proved directly, by the same argument with countable sums, not by reduction to the finite case. The measurable case is also proved directly, by the paper's argument with operator-valued measures on the spaces of histories; it does not use the countable proof, only the real-analysis lemmas of `TheoremS/Potential.lean`. All ten proofs depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. No file under `TheoremS/` contains `sorry`, `admit`, `native_decide`, `axiom` or `unsafe`.

## The model

The state space is `ℂ^N ⊗ ℂ^2 ⊗ ℂ^K` (address, marker bit, workspace), written as `EuclideanSpace ℂ (Fin N × Bool × K)` for a finite type `K`. The oracle for the marked item `x` is the permutation unitary `|y, b, w⟩ ↦ |y, b xor [y = x], w⟩`. The algorithm is a rooted tree of classical control, given as a map from finite lists of outcomes (newest first) to the kind of node reached. A query node applies the oracle and has one child. An operation node applies an instrument with a finite set of outcomes and Kraus operators `A_j` with `∑_j A_j† A_j = I`, with one child per outcome. A halt node is a leaf with an output in `Fin N`. Neither the initial state nor the tree depends on `x`, and paths may be infinite. The branch vector of a node is the initial state after the operators along its path; `p_x(h)` is its squared norm, the cost `T_x` is the sum of `p_x(h)` over query nodes (a value in `[0, ∞]`), the success probability `s_x` is the sum over halt nodes with output `x`, and zero error means `s_x = 1` for every `x`. All of this is in `TheoremS/Statement.lean`, which imports only Mathlib and defines the model and the claims without proving anything.

The countable model in `TheoremS/Inf/Statement.lean` (also Mathlib only) has the same tree, oracle and definitions of `p_x`, `T_x`, `s_x` and zero error. The workspace is any separable complex Hilbert space `K`, and the state space `ℂ^N ⊗ ℂ^2 ⊗ K` is written as `PiLp 2 (fun _ : Fin N × Bool => K)`, the ℓ² sum of `2N` copies of `K`. An operation node has an outcome set `J ⊆ ℕ`, finite or countably infinite, and bounded operators `A_j` with `∑_{j ∈ J} A_j† A_j = I` in the strong operator topology (an unordered sum). The separability hypothesis is part of the statement, as in the paper, but the proof does not use it.

The model with measurable outcomes in `TheoremS/Meas/Statement.lean` (Mathlib only) is the paper's definition of an algorithm with measurable outcomes (label def:s-meas). The state space and the oracle are those of the countable model. Positive trace-class operators are positive bounded operators `Y` with `tr Y = ∑_e ⟪e, Y e⟫ < ∞` over a fixed Hilbert basis (Mathlib has no trace-class type). A history of depth `M` is a point of `Ω_1 × ⋯ × Ω_M` with the product σ-algebra. The algorithm consists of an initial density operator `ρ₀`, a measurable map `k_M` from histories of depth `M` to the kinds (operation, query, halt with an output in `Fin N`), and for each history `h` an instrument `I_{M,h}` with outcome space `Ω_{M+1}`, given on each measurable set `F` by a countable Kraus family, trace preserving on the whole space, countably additive in `F` and measurable in `h`. A query step applies the oracle and then the instrument. Nothing depends on the marked item. The history measures `ρ^{(M)}_x` are positive operator measures on histories of depth `M`, fixed by `ρ^{(0)} = ρ₀` and the recursion `ρ^{(M+1)}(G) = ∫ Ξ^x_{M,h}(G_h)(σ(h)) τ(dh)` for a density `(σ, τ)` of `ρ^{(M)}`, where `Ξ^x_{M,h}` is the step after `h` with marked item `x`. Then `T_x = ∑_M tr ρ^{(M)}_x(k_M⁻¹(query))`, `s_x = ∑_M tr ρ^{(M)}_x(k_M⁻¹(halt x))`, and zero error means `s_x = 1` for every `x`. The docstring of `Alg` explains why countable Kraus families give exactly the paper's class of instruments when `K` is separable; that argument (Kraus' theorem) is in the comment, not in Lean.

Comments in `TheoremS/Meas/` name the paper's statements by their LaTeX labels: def:s-meas (algorithm with measurable outcomes), lem:m-int (weak integral), lem:m-dens (densities), lem:m-comp (one step), lem:m-front (frontier), lem:m-joint (joint measures), lem:m-cell (one joint state), thm:S-meas (Theorem S for measurable outcomes) and rem:m-cover (what the definition contains).

## What is not proved here

- That the measurable model contains the countable one. `TheoremS/Meas/Statement.lean` states this as `CountableEmbeds` (the paper's Remark rem:m-cover(a)) but nothing proves it. The countable model is covered by `TheoremSInf` directly.
- For measurable outcomes, the sharper zero-error bound with `1 − 1/N` in place of `1 − 2/N` and the bounded-error form, which the paper proves on paper. They are not stated in Lean.
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
| `TheoremS/Meas/Statement.lean` | The model with measurable outcomes and the claims `TheoremSMeasGen`, `TheoremSMeasGen'`, `TheoremSMeas`, `TheoremSMeas'`, `HistoryExists`, `HistoryUnique`, `CountableEmbeds` (Mathlib only) |
| `TheoremS/Meas/Trace.lean` | Basis sums of positive operators and matrix elements of maps in Kraus form |
| `TheoremS/Meas/Dens.lean` | Weak integrals of operator fields and densities of positive operator measures |
| `TheoremS/Meas/Comp.lean` | Measurable kernels in Kraus form and one step of the recursion |
| `TheoremS/Meas/Hist.lean` | The proofs `historyExists`, `historyUnique` |
| `TheoremS/Meas/Front.lean` | Truncated histories and the frontier lemma |
| `TheoremS/Meas/Joint.lean` | The reference register and the joint measures |
| `TheoremS/Meas/Cell.lean` | The one-step inequalities for one joint state |
| `TheoremS/Meas/Bound.lean` | The proofs `theoremSMeasGen`, `theoremSMeasGen'`, `theoremSMeas`, `theoremSMeas'` |
| `checks/Axioms.lean` | Prints the eight statements and the axioms of the ten proofs |

## Building

Install [elan](https://github.com/leanprover/elan). In a clone:

```
lake exe cache get
lake build
lake env lean checks/Axioms.lean
```

The toolchain is Lean `v4.35.0` (`lean-toolchain`) and Mathlib is pinned by `lake-manifest.json` to commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`). The last command should print the eight statements and, for each of the ten proofs, `[propext, Classical.choice, Quot.sound]`. `CHECK.md` records a build from a clean clone.

## The paper

The theorem is Theorem S of the paper "The expected number of oracle calls for zero-error quantum search with classical control" (M. Moenius, in preparation), for instruments with countably many outcomes, and the paper's Theorem S for measurable outcomes (label thm:S-meas). The paper also proves the matching upper bound and explains where the constant `π/8 + 1/4` comes from.

## Licence

Apache-2.0, see `LICENSE`.
