/-
Copyright 2026 Marlon Moenius

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-
The statement of Theorem S for measurable outcome spaces (Theorem thm:S-meas of the paper).

This file imports only Mathlib and proves nothing about algorithms: it defines the model of Definition
def:s-meas of the paper and states the claims. Conventions follow `TheoremS/Inf/Statement.lean` (namespace
`TheoremS.Inf`); the state space, the bit oracle and the bound expressions are copied from there word for word.

The model (Definition def:s-meas):

* `H = ℂ^N ⊗ ℂ^2 ⊗ K = PiLp 2 (fun _ : Fin N × Bool => K)`, `K` a separable complex Hilbert space; bit
  oracle `O_x` as in `TheoremS.Inf` (`oracle`, here also as a bounded operator `oracleL`).
* Positive trace-class operators are bounded operators `Y : H →L[ℂ] H` with `Y.IsPositive` and
  `tr Y < ∞` (`PosTC`), where `tr Y = ∑_e re ⟪e, Y e⟫` over a fixed Hilbert basis of `H` (`tr`). For a
  positive operator this sum does not depend on the basis; Mathlib has no trace-class type.
* Outcome spaces `Ω m` (`m ≥ 0`): `Ω m` is the paper's `Ω_{m+1}`, the outcome space of the step taken after
  a history of depth `m`. Histories of depth `M` are `Hist Ω M`, defined by `Hist Ω 0 = Unit` and
  `Hist Ω (M+1) = Hist Ω M × Ω M` with the (iterated binary) product σ-algebra; this is the paper's
  `X_M = Ω_1 × ... × Ω_M` with the identification `X_{M+1} = X_M × Ω_{M+1}` made definitional.
* Kinds `k_M : Hist Ω M → Kind N` (operation, query, halt with output), measurable, `Kind N` with all
  subsets measurable.
* Instruments `I_{M,h}` with outcome space `Ω M`, given per measurable set `F` by a countable Kraus family
  `kraus M h F : ℕ → (H →L[ℂ] H)`, `I_{M,h}(F)(Y) = ∑_k A_k Y A_k†` (see the docstring of `Alg` for why
  this is the paper's class of instruments).
* History measures `ρ^{(M)}_x`: positive operator measures on `Hist Ω M`, characterised by the paper's
  recursion `ρ^{(0)}({∅}) = ρ₀`, `ρ^{(M+1)} = Ξ^x_M ∘ ρ^{(M)}` (Lemma lem:m-comp(ii)) through a density
  `(σ, τ)` of `ρ^{(M)}` (Lemma lem:m-dens). `IsHistory A x ρ` says that `ρ` is this family.
* `s_x = ∑_M tr ρ^{(M)}_x (k_M⁻¹(x))`, `T_x = ∑_M tr ρ^{(M)}_x (k_M⁻¹(q))`, zero error `s_x = 1` for all x.

Claims: `TheoremSMeas`, `TheoremSMeas'` (the bounds of `TheoremSInf`, `TheoremSInf'`, for standard Borel
outcome spaces), `TheoremSMeasGen`, `TheoremSMeasGen'` (the same for arbitrary nonempty measurable outcome
spaces, the generality of the paper). Side conditions stated as propositions:
`HistoryExists` (Lemmas lem:m-dens and lem:m-comp(ii)), `HistoryUnique` (Lemma lem:m-comp(iii)), and
`CountableEmbeds` (Remark rem:m-cover(a), with the countable model copied from `TheoremS.Inf` into
`TheoremS.Meas.Countable`).

Reading of the claims: they quantify over every family `ρ` with `IsHistory`, so they are stronger than the
paper's theorem as stated, and they say something about an algorithm only if such a family exists.
`TheoremSMeasGen` implies the `κγ(1 - 2/N)` bound of Theorem thm:S-meas, once the instruments are written in
Kraus form (see `Alg`). `TheoremSMeasGen'` implies the explicit bound. `HistoryExists` shows that the claims
are not vacuous, and with `HistoryUnique` the paper's theorem implies `TheoremSMeasGen`.
As for `TheoremSInf'`, the bound of `TheoremSMeas'` and `TheoremSMeasGen'` is negative for `N ∈ {4, 5, 6}`,
where `ENNReal.ofReal` clips it to 0. `Ω m : Type` loses nothing: the claims depend on `Ω m` only through
its measurable structure, and every measurable space used in the paper lives in `Type`.

Scope: the sharper zero-error bound `κγ(1 - 1/N)` and the bounded-error form of thm:S-meas are not stated.
-/
import Mathlib

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

/-! ### State space and oracle (copied from `TheoremS.Inf`) -/

/-- Basis labels of `ℂ^N ⊗ ℂ^2`: address and marker bit. -/
abbrev Idx (N : ℕ) := Fin N × Bool

/-- The state space `H = ℂ^N ⊗ ℂ^2 ⊗ K`, as the ℓ² sum of `2N` copies of the workspace `K`. -/
abbrev H (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Idx N => K)

/-- Bounded operators on `H`. -/
abbrev Op (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  H N K →L[ℂ] H N K

/-- The basis map of the bit oracle for the marked item `x`: `(y, b) ↦ (y, b xor [y = x])`. -/
def flip {N : ℕ} (x : Fin N) (i : Idx N) : Idx N :=
  (i.1, xor i.2 (decide (i.1 = x)))

/-- `flip x` as a permutation of the basis labels (it is an involution). -/
def flipEquiv {N : ℕ} (x : Fin N) : Idx N ≃ Idx N where
  toFun := flip x
  invFun := flip x
  left_inv := fun i => by rcases i with ⟨y, b⟩; by_cases h : y = x <;> simp [flip, h]
  right_inv := fun i => by rcases i with ⟨y, b⟩; by_cases h : y = x <;> simp [flip, h]

/-- The bit oracle `O_x`, the unitary on `H` that permutes the `2N` summands by `flip x`. -/
def oracle {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x : Fin N) : H N K ≃ₗᵢ[ℂ] H N K :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (flipEquiv x)

/-- The bit oracle as a bounded operator. -/
def oracleL {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x : Fin N) : Op N K :=
  (oracle x).toLinearIsometry.toContinuousLinearMap

/-! ### Trace, positive trace-class operators, Kraus maps -/

section Operators

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A fixed Hilbert basis (complete orthonormal set) of `H`: `exists_hilbertBasis` gives a set `w` and a
Hilbert basis `b : HilbertBasis w ℂ H` with `⇑b = (↑)`. Countable when `K` is separable. -/
def basisSet (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    Set (H N K) :=
  Classical.choose (exists_hilbertBasis ℂ (H N K))

/-- The trace `tr Y = ∑_e ⟪e, Y e⟫ ∈ [0, ∞]` over the basis `basisSet`, for positive `Y` (the paper's
"second fact": a positive `Y` is trace class iff this sum is finite, and then it is the trace). For a
positive operator the value does not depend on the basis. Only applied to positive operators below. -/
def tr (Y : Op N K) : ℝ≥0∞ :=
  ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Y e⟫_ℂ).re

/-- `Y ∈ 𝒯(H)₊`: a positive trace-class operator, i.e. a positive bounded operator of finite trace. -/
def PosTC (Y : Op N K) : Prop :=
  Y.IsPositive ∧ tr Y < ∞

/-- Matrix elements of a map in Kraus form: for `Γ(Y) = ∑_k A_k Y A_k†` (trace-norm convergent when
`∑_k A_k† A_k ≤ I` and `Y` is trace class), `krausMat A Y a b = ⟪a, Γ(Y) b⟫ = ∑_k ⟪A_k† a, Y (A_k† b)⟫`. -/
def krausMat (A : ℕ → Op N K) (Y : Op N K) (a b : H N K) : ℂ :=
  ∑' k, ⟪ContinuousLinearMap.adjoint (A k) a, Y (ContinuousLinearMap.adjoint (A k) b)⟫_ℂ

/-- A positive operator measure on `α` with values in `𝒯(H)₊` (paragraph "Operator measures"): positive
trace-class values on measurable sets and `E ↦ ⟪a, Λ(E) b⟫` countably additive for all `a, b`. Values on
non-measurable sets are not constrained and never used. -/
structure IsPOM {α : Type} [MeasurableSpace α] (Λ : Set α → Op N K) : Prop where
  pos : ∀ E, MeasurableSet E → (Λ E).IsPositive
  trace_lt_top : ∀ E, MeasurableSet E → tr (Λ E) < ∞
  additive : ∀ E : ℕ → Set α, (∀ n, MeasurableSet (E n)) →
    Pairwise (fun i j => Disjoint (E i) (E j)) →
    ∀ a b : H N K, HasSum (fun n => ⟪a, Λ (E n) b⟫_ℂ) ⟪a, Λ (⋃ n, E n) b⟫_ℂ

/-- `(σ, τ)` is a density of `Λ` as in Lemma lem:m-dens: `τ` a finite measure, `σ h` positive of trace one
with measurable matrix elements, and `Λ(E) = ∫_E σ dτ` weakly (Lemma lem:m-int(ii) identifies the weak
integral with the operator integral). -/
structure IsDensity {α : Type} [MeasurableSpace α] (Λ : Set α → Op N K) (τ : Measure α)
    (σ : α → Op N K) : Prop where
  finite : IsFiniteMeasure τ
  pos : ∀ h, (σ h).IsPositive
  trace_one : ∀ h, tr (σ h) = 1
  meas : ∀ a b : H N K, Measurable (fun h => ⟪a, σ h b⟫_ℂ)
  repr : ∀ E, MeasurableSet E → ∀ a b : H N K, ⟪a, Λ E b⟫_ℂ = ∫ h in E, ⟪a, σ h b⟫_ℂ ∂τ

end Operators

/-! ### Histories and kinds -/

/-- Histories of depth `M`: `Hist Ω 0 = Unit` (the empty history `∅`), `Hist Ω (M+1) = Hist Ω M × Ω M`.
`Ω m` is the outcome space of the step taken after a history of depth `m` (the paper's `Ω_{m+1}`). -/
def Hist (Ω : ℕ → Type) : ℕ → Type
  | 0 => Unit
  | M + 1 => Hist Ω M × Ω M

/-- The product σ-algebra on histories (iterated binary products; `⊤` on the one-point space). -/
@[reducible] def Hist.mspace (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)] : (M : ℕ) → MeasurableSpace (Hist Ω M)
  | 0 => ⊤
  | M + 1 => @Prod.instMeasurableSpace (Hist Ω M) (Ω M) (Hist.mspace Ω M) _

instance Hist.instMeasurableSpace (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)] (M : ℕ) :
    MeasurableSpace (Hist Ω M) :=
  Hist.mspace Ω M

/-- Appending an outcome: `(h, ω) ∈ X_{M+1}`. -/
def Hist.cons {Ω : ℕ → Type} {M : ℕ} (h : Hist Ω M) (ω : Ω M) : Hist Ω (M + 1) :=
  (h, ω)

/-- The section `G_h = {ω : (h, ω) ∈ G}` of a set of histories of depth `M + 1`. -/
def Hist.sect {Ω : ℕ → Type} {M : ℕ} (G : Set (Hist Ω (M + 1))) (h : Hist Ω M) : Set (Ω M) :=
  {ω | Hist.cons h ω ∈ G}

/-- The kind of a step (the set `𝒦 = {o, q} ∪ [N]`). -/
inductive Kind (N : ℕ) where
  /-- Apply an instrument. -/
  | op : Kind N
  /-- Query, then apply an instrument. -/
  | query : Kind N
  /-- Halt with output `y`. -/
  | halt (y : Fin N) : Kind N

/-- All subsets of the finite set `𝒦` are measurable. -/
instance (N : ℕ) : MeasurableSpace (Kind N) := ⊤

/-! ### Algorithms with measurable outcomes -/

/-- An algorithm with measurable outcomes (Definition def:s-meas). None of the data depends on the marked
item.

Instruments. The paper's instrument `I_{M,h}` is a family of bounded completely positive maps on `𝒯(H)`,
`F ↦ tr(B I(F)(Y))` countably additive for all `Y ∈ 𝒯(H)`, `B ∈ ℬ(H)`, with `I(Ω)` trace preserving. Here
`I_{M,h}(F)` is given, for each measurable `F`, by a countable Kraus family `kraus M h F`, i.e.
`I_{M,h}(F)(Y) = ∑_k A_k Y A_k†`. This is the same class: a bounded CP map `Γ` on `𝒯(H)` has a normal CP
Banach adjoint `Γ*` on `ℬ(H)`, which by Kraus' theorem is `B ↦ ∑_k A_k† B A_k` (strongly) with countably
many bounded `A_k` since `H` is separable, so `Γ(Y) = ∑_k A_k Y A_k†`; conversely a family with
`∑_k A_k† A_k ≤ I` defines a bounded CP map. Only `I(F)` enters the definitions below (through `krausMat`),
so the choice of Kraus family does not matter. Nothing is assumed about how the families for different `F`
are related beyond the conditions below, and no reference measure on `Ω M` is used (Remark rem:m-cover(d)).
The conditions, field by field:
* `normalised`: `∑_k A_k† A_k = I` strongly for `F = Ω M`, i.e. `I(Ω)` preserves the trace.
* `bounded`: `∑_k ‖A_k ψ‖² ≤ ‖ψ‖²`, i.e. `tr I(F)(Y) ≤ tr Y` for `Y ≥ 0`. In the paper this follows from
  `normalised`, positivity of `I(Ω \ F)` and additivity; here it also makes `krausMat` absolutely summable.
* `additive`: `F ↦ ⟪a, I(F)(Y) b⟫` countably additive for `Y ∈ 𝒯(H)₊` and `a, b ∈ H`. Equivalent to the
  paper's condition (`I(∅) = 0` follows by taking all `F_n = ∅`, since a summable constant sequence is 0;
  hence the partial sums are `I(F_0 ∪ ... ∪ F_n)(Y)`): positive operators span `𝒯(H)`, and for `Y ≥ 0` the partial sums over disjoint `F_n`
  increase with traces bounded by `tr Y`, so weak convergence of the series implies trace-norm convergence,
  hence convergence of `tr(B ·)` for every bounded `B`.
* `measurable`: `h ↦ ⟪a, I_{M,h}(F)(Y) b⟫` measurable for `Y ∈ 𝒯(H)₊`, `a, b ∈ H` (item 4). Equivalent to
  the paper's condition with all `Y ∈ 𝒯(H)` and `B ∈ ℬ(H)`: by linearity in `Y`, and by (M1),
  `tr(B Z) = lim_n ∑_{i,j ≤ n} ⟪e_i, B e_j⟫⟪e_j, Z e_i⟫` is a pointwise limit of matrix elements. -/
structure Alg (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)] where
  /-- The initial density operator `ρ₀` (item 1). -/
  rho0 : Op N K
  rho0_pos : rho0.IsPositive
  rho0_tr : tr rho0 = 1
  /-- The kind `k_M(h)` of the step after history `h` (item 3). -/
  kind : (M : ℕ) → Hist Ω M → Kind N
  kind_meas : ∀ M, Measurable (kind M)
  /-- Kraus family of `I_{M,h}(F)` (item 4); only used for measurable `F`. -/
  kraus : (M : ℕ) → Hist Ω M → Set (Ω M) → ℕ → Op N K
  normalised : ∀ M (h : Hist Ω M) (ψ : H N K),
    HasSum (fun k => ContinuousLinearMap.adjoint (kraus M h Set.univ k) (kraus M h Set.univ k ψ)) ψ
  bounded : ∀ M (h : Hist Ω M) (F : Set (Ω M)), MeasurableSet F → ∀ ψ : H N K,
    ∑' k, ENNReal.ofReal (‖kraus M h F k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2)
  additive : ∀ M (h : Hist Ω M) (F : ℕ → Set (Ω M)), (∀ n, MeasurableSet (F n)) →
    Pairwise (fun i j => Disjoint (F i) (F j)) → ∀ Y : Op N K, PosTC Y → ∀ a b : H N K,
    HasSum (fun n => krausMat (kraus M h (F n)) Y a b) (krausMat (kraus M h (⋃ n, F n)) Y a b)
  measurable : ∀ M (F : Set (Ω M)), MeasurableSet F → ∀ Y : Op N K, PosTC Y → ∀ a b : H N K,
    Measurable (fun h : Hist Ω M => krausMat (kraus M h F) Y a b)

/-- Families of operator-valued set functions, one on each `Hist Ω M` (candidates for `ρ^{(M)}_x`). -/
abbrev HistFam (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (Ω : ℕ → Type) :=
  (M : ℕ) → Set (Hist Ω M) → Op N K

namespace Alg

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

/-- Matrix elements of the step kernel `Ξ^x_{M,h}(F)(Y)`: `I_{M,h}(F)(Y)` after an operation kind,
`I_{M,h}(F)(O_x Y O_x†)` after a query kind (Kraus operators `A_k O_x`), and `0` after a halt kind. -/
def stepMat (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M) (F : Set (Ω M)) (Y : Op N K)
    (a b : H N K) : ℂ :=
  match A.kind M h with
  | .op => krausMat (A.kraus M h F) Y a b
  | .query => krausMat (fun k => A.kraus M h F k ∘L oracleL x) Y a b
  | .halt _ => 0

/-- `ρ` is the family of history measures `ρ^{(M)}_x` of `A` for the marked item `x`:
`ρ^{(0)}({∅}) = ρ₀`, every `ρ^{(M)}` is a positive operator measure, and
`ρ^{(M+1)}(G) = ∫ Ξ^x_{M,h}(G_h)(σ(h)) τ(dh)` (weakly) for a density `(σ, τ)` of `ρ^{(M)}`, which is the
paper's `ρ^{(M+1)}_x = Ξ^x_M ∘ ρ^{(M)}_x` (Lemma lem:m-comp(ii)). By Lemma lem:m-comp(iii) the right side
does not depend on the density, so "for some density" is the same as "for every density".
Both integrands are bounded by `‖a‖‖b‖` and measurable (Lemma lem:m-comp(i), whose proof uses only the
fields of `Alg`), so the Bochner integrals are genuine integrals and not junk values. `IsDensity` forces
`τ = tr ρ^{(M)}` on measurable sets.

Commentary, not used by the statement. Why not a path measure (`ProbabilityTheory.Kernel.traj`): the law of the outcome at step `M` given the
history `h` is `F ↦ tr Ξ^x_{M,h}(F)(σ(h))`, which depends on the post-measurement state `σ(h)`, i.e. on the
density of `ρ^{(M)}_x`. So the Ionescu-Tulcea kernels can only be written down after the operator-valued
measures; with them, `p^{(M+1)}(G) = ∫ κ_M(h, G_h) p^{(M)}(dh)` for the sub-Markov kernel
`κ_M(h, F) = tr Ξ^x_{M,h}(F)(σ(h))`, so the depth-`M` marginal of that path measure (with a cemetery state
for halted runs) on the histories that did not halt before depth `M` is `p^{(M)}`. The paper needs no measure
on infinite histories, and neither does this statement. -/
structure IsHistory (A : Alg N K Ω) (x : Fin N) (ρ : HistFam N K Ω) : Prop where
  init : ρ 0 Set.univ = A.rho0
  pom : ∀ M, IsPOM (ρ M)
  step : ∀ M, ∃ (τ : Measure (Hist Ω M)) (σ : Hist Ω M → Op N K), IsDensity (ρ M) τ σ ∧
    ∀ G : Set (Hist Ω (M + 1)), MeasurableSet G → ∀ a b : H N K,
      ⟪a, ρ (M + 1) G b⟫_ℂ = ∫ h, A.stepMat x M h (Hist.sect G h) (σ h) a b ∂τ

/-- The success probability `s_x = ∑_M p^{(M)}_x(k_M⁻¹(x))`, `p^{(M)}_x = tr ρ^{(M)}_x`. -/
def success (A : Alg N K Ω) (ρ : HistFam N K Ω) (x : Fin N) : ℝ≥0∞ :=
  ∑' M : ℕ, tr (ρ M (A.kind M ⁻¹' {Kind.halt x}))

/-- The cost `T_x = ∑_M p^{(M)}_x(k_M⁻¹(q)) ∈ [0, ∞]`, the expected number of queries. -/
def cost (A : Alg N K Ω) (ρ : HistFam N K Ω) : ℝ≥0∞ :=
  ∑' M : ℕ, tr (ρ M (A.kind M ⁻¹' {Kind.query}))

/-- Zero error: `s_x = 1` for every marked item `x`, where `ρ x` is the history family for `x`. -/
def ZeroError (A : Alg N K Ω) (ρ : Fin N → HistFam N K Ω) : Prop :=
  ∀ x, A.success (ρ x) x = 1

end Alg

/-! ### The claims -/

/-- Theorem S for measurable outcomes, standard Borel outcome spaces: for `N ≥ 4`, every zero-error
algorithm with measurable outcomes has average cost at least `(2 / arcsin (2/√N)) (π/8 + 1/4) (1 - 2/N)`.
`ρ x` ranges over the history families of `A` for the marked item `x`. -/
def TheoremSMeas : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)]
    [∀ m, StandardBorelSpace (Ω m)] [∀ m, Nonempty (Ω m)]
    (A : Alg N K Ω) (ρ : Fin N → HistFam N K Ω), (∀ x, A.IsHistory x (ρ x)) → A.ZeroError ρ →
    ENNReal.ofReal (2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / (N : ℝ)))
      ≤ (∑ x, A.cost (ρ x)) / (N : ℝ≥0∞)

/-- The same with the explicit form `(π/8 + 1/4)√N - 4/√N`. -/
def TheoremSMeas' : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)]
    [∀ m, StandardBorelSpace (Ω m)] [∀ m, Nonempty (Ω m)]
    (A : Alg N K Ω) (ρ : Fin N → HistFam N K Ω), (∀ x, A.IsHistory x (ρ x)) → A.ZeroError ρ →
    ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * Real.sqrt N - 4 / Real.sqrt N)
      ≤ (∑ x, A.cost (ρ x)) / (N : ℝ≥0∞)

/-- `TheoremSMeas` for arbitrary nonempty measurable outcome spaces (in `Type`), the generality of
Definition def:s-meas. -/
def TheoremSMeasGen : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)]
    [∀ m, Nonempty (Ω m)]
    (A : Alg N K Ω) (ρ : Fin N → HistFam N K Ω), (∀ x, A.IsHistory x (ρ x)) → A.ZeroError ρ →
    ENNReal.ofReal (2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / (N : ℝ)))
      ≤ (∑ x, A.cost (ρ x)) / (N : ℝ≥0∞)

/-- `TheoremSMeas'` for arbitrary nonempty measurable outcome spaces. -/
def TheoremSMeasGen' : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)]
    [∀ m, Nonempty (Ω m)]
    (A : Alg N K Ω) (ρ : Fin N → HistFam N K Ω), (∀ x, A.IsHistory x (ρ x)) → A.ZeroError ρ →
    ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * Real.sqrt N - 4 / Real.sqrt N)
      ≤ (∑ x, A.cost (ρ x)) / (N : ℝ≥0∞)

/-- Every algorithm has a history family for every marked item (Lemmas lem:m-dens and lem:m-comp(ii),
by induction on the depth). Without it the claims above could hold vacuously. -/
def HistoryExists : Prop :=
  ∀ (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)]
    [∀ m, Nonempty (Ω m)] (A : Alg N K Ω) (x : Fin N), ∃ ρ : HistFam N K Ω, A.IsHistory x ρ

/-- History families agree on measurable sets (Lemma lem:m-comp(iii), by induction on the depth), so
`cost` and `success` do not depend on the family chosen. -/
def HistoryUnique : Prop :=
  ∀ (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)]
    [∀ m, Nonempty (Ω m)] (A : Alg N K Ω) (x : Fin N) (ρ ρ' : HistFam N K Ω),
    A.IsHistory x ρ → A.IsHistory x ρ' → ∀ M (E : Set (Hist Ω M)), MeasurableSet E → ρ M E = ρ' M E

/-! ### The countable model (copied from `TheoremS.Inf`, not imported) and its embedding -/

namespace Countable

variable (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The kind of a node of the classical control tree (`TheoremS.Inf.Node`). -/
inductive Node where
  | query : Node
  | op (J : Set ℕ) (A : ℕ → H N K →L[ℂ] H N K) : Node
  | halt (out : Fin N) : Node

/-- An adaptive query algorithm of Definition def:s-alg (`TheoremS.Inf.Alg`, word for word). -/
structure Alg where
  psi0 : H N K
  norm_psi0 : ‖psi0‖ = 1
  node : List ℕ → Node N K
  complete : ∀ h J A, node h = .op J A →
    ∀ ψ : H N K, HasSum (fun j : J => ContinuousLinearMap.adjoint (A j) (A j ψ)) ψ

variable {N K}

/-- `true` exactly at query nodes. -/
def Node.isQuery : Node N K → Bool
  | .query => true
  | _ => false

/-- The output of a halt node, `none` at other nodes. -/
def Node.output : Node N K → Option (Fin N)
  | .halt y => some y
  | _ => none

open Classical in
/-- Branch vectors (`TheoremS.Inf.Alg.branch`). -/
def Alg.branch (A : Alg N K) (x : Fin N) : List ℕ → H N K
  | [] => A.psi0
  | j :: h =>
    match A.node h with
    | .query => if j = 0 then oracle x (A.branch x h) else 0
    | .op J B => if j ∈ J then B j (A.branch x h) else 0
    | .halt _ => 0

/-- `p_x h = ‖ψ_x h‖²`. -/
def Alg.prob (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖A.branch x h‖ ^ 2)

/-- The cost `T_x` of the countable model. -/
def Alg.cost (A : Alg N K) (x : Fin N) : ℝ≥0∞ :=
  ∑' h : List ℕ, if (A.node h).isQuery then A.prob x h else 0

/-- The success probability `s_x` of the countable model. -/
def Alg.success (A : Alg N K) (x : Fin N) : ℝ≥0∞ :=
  ∑' h : List ℕ, if (A.node h).output = some x then A.prob x h else 0

end Countable

/-- The outcome space `ℕ` at every depth, with all subsets measurable. -/
def NatOut (_ : ℕ) : Type := ℕ

instance (m : ℕ) : MeasurableSpace (NatOut m) := inferInstanceAs (MeasurableSpace ℕ)

/-- Remark rem:m-cover(a): every algorithm of the countable model is matched, for every marked item, in
cost and success by an algorithm with measurable outcomes (outcome space `ℕ` at every depth), which has
history families, and every history family of it gives that cost and success. Meant to be combined with
`TheoremSMeasGen` (instance search does not see `StandardBorelSpace (NatOut m)`). -/
def CountableEmbeds : Prop :=
  ∀ (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (B : Countable.Alg N K),
    ∃ A : Alg N K NatOut,
      (∃ ρ : Fin N → HistFam N K NatOut, ∀ x, A.IsHistory x (ρ x)) ∧
      ∀ ρ : Fin N → HistFam N K NatOut, (∀ x, A.IsHistory x (ρ x)) →
        ∀ x, A.cost (ρ x) = B.cost x ∧ A.success (ρ x) x = B.success x

end

end TheoremS.Meas
