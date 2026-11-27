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
The trace layer for measurable outcome spaces. Formalises the paragraph "Notation" of the paper's section on
measurable outcome spaces (the basis sum `tr`, the two standard facts about positive trace-class operators,
(M1)) for an arbitrary Hilbert basis, and the matrix elements of a map in Kraus form `Γ(Y) = ∑_k A_k Y A_k†`
between two Hilbert spaces.
-/
import TheoremS.Meas.Statement

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory Filter Topology

noncomputable section

/-! ### The basis sum `trB` -/

section TraceB

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] {ι ι' : Type*}

/-- The basis sum `∑_i ⟪b_i, Y b_i⟫ ∈ [0, ∞]` over an arbitrary Hilbert basis `b` (paragraph "Notation",
second standard fact: for positive `Y` this is the trace, finite iff `Y` is trace class). `tr` of
`TheoremS/Meas/Statement.lean` is `trB` for the fixed basis `hbasis` (`tr_eq_trB`). -/
def trB (b : HilbertBasis ι ℂ E) (Y : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (⟪b i, Y (b i)⟫_ℂ).re

private lemma re_inner_self' (x : E) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

private lemma inner_self_ofReal (x : E) : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact re_inner_self' x
  · rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) x

private lemma re_nonneg {Y : E →L[ℂ] E} (hY : Y.IsPositive) (x : E) :
    0 ≤ (⟪x, Y x⟫_ℂ).re :=
  hY.re_inner_nonneg_right x

private lemma summable_of_enn {α : Type*} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a)
    (h : ∑' a, ENNReal.ofReal (f a) ≠ ∞) : Summable f :=
  (ENNReal.summable_toReal h).congr fun a => ENNReal.toReal_ofReal (h0 a)

private lemma hb_parseval (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using h

private lemma hb_parseval_enn (b : HilbertBasis ι ℂ E) (x : E) :
    ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hb_parseval b x).summable,
    (hb_parseval b x).tsum_eq]

/-- Squared Hilbert-Schmidt norm in a basis. -/
private def HS (b : HilbertBasis ι ℂ E) (S : E →L[ℂ] E') : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2)

private lemma HS_adjoint [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis ι' ℂ E') (S : E →L[ℂ] E') :
    HS b S = HS c (ContinuousLinearMap.adjoint S) := by
  unfold HS
  calc ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, S (b i)⟫_ℂ‖ ^ 2) :=
        tsum_congr fun i => (hb_parseval_enn c _).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪c j, S (b i)⟫_ℂ‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪b i, ContinuousLinearMap.adjoint S (c j)⟫_ℂ‖ ^ 2) := by
        refine tsum_congr fun j => tsum_congr fun i => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left S (b i) (c j), norm_inner_symm]
    _ = ∑' j, ENNReal.ofReal (‖ContinuousLinearMap.adjoint S (c j)‖ ^ 2) :=
        tsum_congr fun j => hb_parseval_enn b _

private lemma exists_sqrt [CompleteSpace E] {Y : E →L[ℂ] E} (hY : Y.IsPositive) :
    ∃ T : E →L[ℂ] E, ContinuousLinearMap.adjoint T = T ∧ Y = T ∘L T := by
  have hY0 : 0 ≤ Y := ContinuousLinearMap.nonneg_iff_isPositive.mpr hY
  refine ⟨CFC.sqrt Y, ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)), ?_⟩
  rw [← ContinuousLinearMap.mul_def, CFC.sqrt_mul_sqrt_self Y hY0]

private lemma inner_TT [CompleteSpace E] {T : E →L[ℂ] E} (hT : ContinuousLinearMap.adjoint T = T)
    (x z : E) : ⟪x, (T ∘L T) z⟫_ℂ = ⟪T x, T z⟫_ℂ := by
  rw [ContinuousLinearMap.comp_apply]
  have h := ContinuousLinearMap.adjoint_inner_right T x (T z)
  rw [hT] at h
  exact h

private lemma trB_eq_HS [CompleteSpace E] (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] E}
    (hT : ContinuousLinearMap.adjoint T = T) : trB b (T ∘L T) = HS b T := by
  unfold trB HS
  refine tsum_congr fun i => ?_
  rw [inner_TT hT, re_inner_self']

private lemma norm_sq_le_HS [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    (S : E →L[ℂ] E') (x : E) :
    ENNReal.ofReal (‖S x‖ ^ 2) ≤ ENNReal.ofReal (‖x‖ ^ 2) * HS b S := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ E'
  rw [HS_adjoint b c S]
  unfold HS
  rw [← hb_parseval_enn c (S x), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← ContinuousLinearMap.adjoint_inner_left S x (c j), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (le_of_le_of_eq (norm_inner_le_norm _ _) (mul_comm _ _)) 2

private lemma norm_le_of_HS [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    (S : E →L[ℂ] E') (hS : HS b S ≠ ∞) (x : E) :
    ‖S x‖ ≤ ‖x‖ * Real.sqrt (HS b S).toReal := by
  have h := norm_sq_le_HS b S x
  rw [← ENNReal.ofReal_toReal hS, ← ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)] at h
  rw [← Real.sqrt_sq (norm_nonneg (S x)), ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- The image of a Hilbert basis under a unitary. -/
private def hbMap (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E') : HilbertBasis ι ℂ E' :=
  HilbertBasis.ofRepr (U.symm.trans b.repr)

private lemma hbMap_apply (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E') (i : ι) :
    hbMap b U i = U (b i) :=
  rfl

private lemma adjoint_lie [CompleteSpace E] [CompleteSpace E'] (U : E ≃ₗᵢ[ℂ] E') :
    ContinuousLinearMap.adjoint U.toLinearIsometry.toContinuousLinearMap =
      U.symm.toLinearIsometry.toContinuousLinearMap := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact U.inner_map_eq_flip x y

private lemma hb_countable [TopologicalSpace.SeparableSpace E] (b : HilbertBasis ι ℂ E) :
    Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (b i) (1 / 2))
    ?_ (fun i => Metric.isOpen_ball) (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  show Disjoint (Metric.ball (b i) (1 / 2)) (Metric.ball (b j) (1 / 2))
  refine Set.disjoint_left.mpr fun x hxi hxj => ?_
  have h2 : ‖b i - b j‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), b.orthonormal.1 i, b.orthonormal.1 j, b.orthonormal.2 hij]
    norm_num
  rw [Metric.mem_ball, dist_eq_norm] at hxi hxj
  have h3 : ‖b i - b j‖ < 1 := by
    calc ‖b i - b j‖ = ‖(x - b j) - (x - b i)‖ := by congr 1; abel
      _ ≤ ‖x - b j‖ + ‖x - b i‖ := norm_sub_le _ _
      _ < 1 := by linarith
  nlinarith [norm_nonneg (b i - b j)]

/-- The trace of a positive operator does not depend on the Hilbert basis (paragraph "Notation"; used
implicitly throughout, e.g. when the paper writes `tr` without naming a basis). -/
theorem trB_indep [CompleteSpace E] (b : HilbertBasis ι ℂ E) (c : HilbertBasis ι' ℂ E)
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) : trB b Y = trB c Y := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  rw [trB_eq_HS b hT, trB_eq_HS c hT, HS_adjoint b c T, hT]

/-- Additivity of the trace on positive operators (paragraph "Notation"). -/
theorem trB_add [CompleteSpace E] {b : HilbertBasis ι ℂ E} {Y Z : E →L[ℂ] E}
    (hY : Y.IsPositive) (hZ : Z.IsPositive) : trB b (Y + Z) = trB b Y + trB b Z := by
  unfold trB
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun i => ?_
  rw [add_apply, inner_add_right, Complex.add_re,
    ENNReal.ofReal_add (re_nonneg hY _) (re_nonneg hZ _)]

/-- Positive homogeneity of the trace (paragraph "Notation"). -/
theorem trB_smul [CompleteSpace E] {b : HilbertBasis ι ℂ E} {Y : E →L[ℂ] E} (c : NNReal) :
    trB b ((c : ℂ) • Y) = c * trB b Y := by
  unfold trB
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [smul_apply, inner_smul_right, Complex.re_ofReal_mul,
    ENNReal.ofReal_mul (NNReal.coe_nonneg c), ENNReal.ofReal_coe_nnreal]

/-- Unitary invariance of the trace, `tr (U Y U†) = tr Y` for a unitary (surjective isometry)
`U : E → E'` (paragraph "Notation"). A non-surjective isometry `V` is the one-operator case of
`trB_eq_of_krausMatG`. -/
theorem trB_conj [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {b' : HilbertBasis ι' ℂ E'} (U : E ≃ₗᵢ[ℂ] E') {Y : E →L[ℂ] E} (hY : Y.IsPositive) :
    trB b' (U.toLinearIsometry.toContinuousLinearMap ∘L Y ∘L
      U.symm.toLinearIsometry.toContinuousLinearMap) = trB b Y := by
  have hpos : (U.toLinearIsometry.toContinuousLinearMap ∘L Y ∘L
      U.symm.toLinearIsometry.toContinuousLinearMap).IsPositive := by
    rw [← adjoint_lie U]
    exact hY.conj_adjoint _
  rw [trB_indep b' (hbMap b U) hpos]
  unfold trB
  refine tsum_congr fun i => ?_
  rw [hbMap_apply]
  simp [LinearIsometryEquiv.inner_map_map]

/-- Monotonicity of the trace: `0 ≤ Y ≤ Z` implies `tr Y ≤ tr Z` (paragraph "Operator measures", used
for `Λ(E) ≤ Λ(E')`). -/
theorem trB_mono [CompleteSpace E] {b : HilbertBasis ι ℂ E} {Y Z : E →L[ℂ] E}
    (hY : Y.IsPositive) (hZY : (Z - Y).IsPositive) : trB b Y ≤ trB b Z := by
  calc trB b Y ≤ trB b Y + trB b (Z - Y) := le_self_add
    _ = trB b (Y + (Z - Y)) := (trB_add hY hZY).symm
    _ = trB b Z := by congr 1; abel

/-- `⟪a, Y a⟫ ≤ ‖a‖² tr Y` for positive `Y` (the bound `‖Y‖ ≤ tr Y`, paragraph "Notation"; used in the
proof of lem:m-int(ii)). -/
theorem ofReal_inner_le_trB [CompleteSpace E] {b : HilbertBasis ι ℂ E} {Y : E →L[ℂ] E}
    (hY : Y.IsPositive) (a : E) :
    ENNReal.ofReal (⟪a, Y a⟫_ℂ).re ≤ ENNReal.ofReal (‖a‖ ^ 2) * trB b Y := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  rw [trB_eq_HS b hT, inner_TT hT, re_inner_self']
  exact norm_sq_le_HS b T a

/-- `|⟪a, Y c⟫| ≤ ‖a‖ ‖c‖ tr Y` for positive trace-class `Y` (proofs of lem:m-int(ii) and lem:m-dens:
`|q(a, b)| ≤ ‖a‖ ‖b‖ ∫ tr Y_h`). -/
theorem norm_inner_le_trB [CompleteSpace E] {b : HilbertBasis ι ℂ E} {Y : E →L[ℂ] E}
    (hY : Y.IsPositive) (hfin : trB b Y < ∞) (a c : E) :
    ‖⟪a, Y c⟫_ℂ‖ ≤ ‖a‖ * ‖c‖ * (trB b Y).toReal := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  rw [trB_eq_HS b hT] at hfin ⊢
  rw [inner_TT hT]
  have ht : 0 ≤ (HS b T).toReal := ENNReal.toReal_nonneg
  calc ‖⟪T a, T c⟫_ℂ‖ ≤ ‖T a‖ * ‖T c‖ := norm_inner_le_norm _ _
    _ ≤ (‖a‖ * Real.sqrt (HS b T).toReal) * (‖c‖ * Real.sqrt (HS b T).toReal) :=
      mul_le_mul (norm_le_of_HS b T hfin.ne a) (norm_le_of_HS b T hfin.ne c) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    _ = ‖a‖ * ‖c‖ * (HS b T).toReal := by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt ht]

/-- A positive operator of trace zero is zero (paragraph "Notation"). -/
theorem eq_zero_of_trB_eq_zero [CompleteSpace E] {b : HilbertBasis ι ℂ E} {Y : E →L[ℂ] E}
    (hY : Y.IsPositive) (h0 : trB b Y = 0) : Y = 0 := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  rw [trB_eq_HS b hT] at h0
  have hT0 : T = 0 := by
    ext x
    have h := norm_sq_le_HS b T x
    rw [h0, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
    have h' : ‖T x‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
    simpa using h'
  rw [hT0]
  simp

end TraceB

/-! ### The fixed basis of `H` -/

/-- The fixed Hilbert basis of `H` behind `basisSet` and `tr` (paragraph "Notation": "We fix an
orthonormal basis `(e_n)`"), the same choice from `exists_hilbertBasis` as `basisSet`. -/
def hbasis (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    HilbertBasis (basisSet N K) ℂ (H N K) :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ (H N K)))

/-- The basis `hbasis` is the inclusion of `basisSet` (paragraph "Notation"). -/
theorem hb_coe {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    ⇑(hbasis N K) = ((↑) : basisSet N K → H N K) := by
  exact Classical.choose_spec (Classical.choose_spec (exists_hilbertBasis ℂ (H N K)))

/-- `tr` of `TheoremS/Meas/Statement.lean` is the basis sum over `hbasis` (paragraph "Notation"). -/
theorem tr_eq_trB {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Y : Op N K) : tr Y = trB (hbasis N K) Y := by
  unfold tr trB
  rw [hb_coe]

/-- The fixed basis is countable when `K` is separable (paragraph "Notation": "All Hilbert spaces in this
subsection are separable", the basis `(e_n)_{n ≥ 1}` is finite or countable). -/
theorem basisSet_countable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K] : (basisSet N K).Countable := by
  have : SecondCountableTopology K := UniformSpace.secondCountable_of_separable K
  exact Set.countable_coe_iff.mp (hb_countable (hbasis N K))

/-! ### Rank-one operators and Kraus maps -/

section Kraus

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] {ι : Type*}

/-- The rank-one operator `|u⟩⟨v|`, `z ↦ ⟪v, z⟫ u` (the matrix units `|e_i⟩⟨e_j|` of (M1) and of the
proof of lem:m-comp(i)). -/
def rk1 (u v : E) : E →L[ℂ] E :=
  (innerSL ℂ v).smulRight u

/-- `|u⟩⟨v| z = ⟪v, z⟫ u`. -/
theorem rk1_apply (u v z : E) : rk1 u v z = ⟪v, z⟫_ℂ • u := by
  rfl

/-- `|w⟩⟨w|` is positive (the pure states and the matrix-unit polarisation of lem:m-comp(i)). -/
theorem rk1_isPositive [CompleteSpace E] (w : E) : (rk1 w w).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have h : ⟪rk1 w w x, x⟫_ℂ = ((‖⟪w, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [rk1_apply, inner_smul_left, Complex.conj_mul', Complex.ofReal_pow]
  rw [h]
  constructor
  · simp only [RCLike.re_to_complex, Complex.ofReal_re]
  · simp only [RCLike.re_to_complex, Complex.ofReal_re]
    positivity

/-- `tr |w⟩⟨w| = ‖w‖²` in any Hilbert basis (Parseval). -/
theorem trB_rk1_self [CompleteSpace E] (b : HilbertBasis ι ℂ E) (w : E) :
    trB b (rk1 w w) = ENNReal.ofReal (‖w‖ ^ 2) := by
  unfold trB
  rw [← hb_parseval_enn b w]
  refine tsum_congr fun i => ?_
  rw [rk1_apply, inner_smul_right, ← inner_conj_symm w (b i), Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Matrix elements of a map in Kraus form between two spaces, `Γ(Y) = ∑_k A_k Y A_k†` with
`A_k : E → E'`: `krausMatG A Y a c = ⟪a, Γ(Y) c⟫ = ∑_k ⟪A_k† a, Y (A_k† c)⟫` (the general form of
`krausMat`; the maps `Θ` of lem:m-int(iii) and the instruments of def:s-meas). -/
def krausMatG [CompleteSpace E] [CompleteSpace E'] (A : ℕ → E →L[ℂ] E') (Y : E →L[ℂ] E)
    (a c : E') : ℂ :=
  ∑' k, ⟪ContinuousLinearMap.adjoint (A k) a, Y (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ

/-- `krausMat` of `TheoremS/Meas/Statement.lean` is `krausMatG` on `H`. -/
theorem krausMat_eq_krausMatG {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (A : ℕ → Op N K) (Y : Op N K) (a c : H N K) :
    krausMat A Y a c = krausMatG A Y a c := by
  rfl

private lemma kraus_K1 [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    (S : E →L[ℂ] E) (a : E') :
    ∑' k, ENNReal.ofReal (‖S (ContinuousLinearMap.adjoint (A k) a)‖ ^ 2) ≤
      ENNReal.ofReal (‖a‖ ^ 2) * HS b S := by
  rw [HS_adjoint b b S]
  unfold HS
  calc ∑' k, ENNReal.ofReal (‖S (ContinuousLinearMap.adjoint (A k) a)‖ ^ 2)
      = ∑' k, ∑' i, ENNReal.ofReal
          (‖⟪b i, S (ContinuousLinearMap.adjoint (A k) a)⟫_ℂ‖ ^ 2) :=
        tsum_congr fun k => (hb_parseval_enn b _).symm
    _ = ∑' k, ∑' i, ENNReal.ofReal
          (‖⟪A k (ContinuousLinearMap.adjoint S (b i)), a⟫_ℂ‖ ^ 2) := by
        refine tsum_congr fun k => tsum_congr fun i => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left S _ (b i),
          ContinuousLinearMap.adjoint_inner_right]
    _ = ∑' i, ∑' k, ENNReal.ofReal
          (‖⟪A k (ContinuousLinearMap.adjoint S (b i)), a⟫_ℂ‖ ^ 2) := ENNReal.tsum_comm
    _ ≤ ∑' i, ENNReal.ofReal (‖a‖ ^ 2) * ∑' k, ENNReal.ofReal
          (‖A k (ContinuousLinearMap.adjoint S (b i))‖ ^ 2) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
        refine ENNReal.ofReal_le_ofReal ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          (le_of_le_of_eq (norm_inner_le_norm _ _) (mul_comm _ _)) 2
    _ ≤ ∑' i, ENNReal.ofReal (‖a‖ ^ 2) *
          ENNReal.ofReal (‖ContinuousLinearMap.adjoint S (b i)‖ ^ 2) :=
        ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl (hA _)
    _ = ENNReal.ofReal (‖a‖ ^ 2) * ∑' i,
          ENNReal.ofReal (‖ContinuousLinearMap.adjoint S (b i)‖ ^ 2) := ENNReal.tsum_mul_left

private lemma real_bound {f : ℕ → ℝ} {r : ℝ} {t : ℝ≥0∞}
    (h : ∑' k, ENNReal.ofReal (f k) ≤ ENNReal.ofReal r * t) (h0 : ∀ k, 0 ≤ f k) (hr : 0 ≤ r)
    (ht : t ≠ ∞) : Summable f ∧ ∑' k, f k ≤ r * t.toReal := by
  have hne : ∑' k, ENNReal.ofReal (f k) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht) h
  have hs : Summable f := summable_of_enn h0 hne
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 hs, ← ENNReal.ofReal_toReal ht,
    ← ENNReal.ofReal_mul hr,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hr ENNReal.toReal_nonneg)] at h
  exact h

private lemma cs_tsum (x z : ℕ → E) (hx : Summable fun k => ‖x k‖ ^ 2)
    (hz : Summable fun k => ‖z k‖ ^ 2) :
    Summable (fun k => ⟪x k, z k⟫_ℂ) ∧
      ‖∑' k, ⟪x k, z k⟫_ℂ‖ ≤ Real.sqrt (∑' k, ‖x k‖ ^ 2) * Real.sqrt (∑' k, ‖z k‖ ^ 2) := by
  have hmx : Memℓp x 2 := memℓp_gen (by simpa [Real.rpow_two] using hx)
  have hmz : Memℓp z 2 := memℓp_gen (by simpa [Real.rpow_two] using hz)
  let X : lp (fun _ : ℕ => E) 2 := ⟨x, hmx⟩
  let Z : lp (fun _ : ℕ => E) 2 := ⟨z, hmz⟩
  have hs : HasSum (fun k => ⟪x k, z k⟫_ℂ) ⟪X, Z⟫_ℂ := lp.hasSum_inner X Z
  have hn : ∀ W : lp (fun _ : ℕ => E) 2, ‖W‖ = Real.sqrt (∑' k, ‖W k‖ ^ 2) := by
    intro W
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) W
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [← h, Real.sqrt_sq (norm_nonneg W)]
  refine ⟨hs.summable, ?_⟩
  rw [hs.tsum_eq]
  calc ‖⟪X, Z⟫_ℂ‖ ≤ ‖X‖ * ‖Z‖ := norm_inner_le_norm _ _
    _ = _ := congrArg₂ (· * ·) (hn X) (hn Z)

private lemma kraus_cross [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    (S R : E →L[ℂ] E) (hS : HS b S ≠ ∞) (hR : HS b R ≠ ∞) (a c : E') :
    Summable (fun k => ⟪S (ContinuousLinearMap.adjoint (A k) a),
        R (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) ∧
      ‖∑' k, ⟪S (ContinuousLinearMap.adjoint (A k) a),
        R (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖ ≤
        ‖a‖ * ‖c‖ * (Real.sqrt (HS b S).toReal * Real.sqrt (HS b R).toReal) := by
  obtain ⟨hsa, hba⟩ := real_bound (kraus_K1 b hA S a) (fun k => sq_nonneg _) (sq_nonneg _) hS
  obtain ⟨hsc, hbc⟩ := real_bound (kraus_K1 b hA R c) (fun k => sq_nonneg _) (sq_nonneg _) hR
  obtain ⟨hs, hb⟩ := cs_tsum _ _ hsa hsc
  refine ⟨hs, ?_⟩
  calc _ ≤ _ := hb
    _ ≤ Real.sqrt (‖a‖ ^ 2 * (HS b S).toReal) * Real.sqrt (‖c‖ ^ 2 * (HS b R).toReal) :=
        mul_le_mul (Real.sqrt_le_sqrt hba) (Real.sqrt_le_sqrt hbc) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
        ring

private lemma kraus_terms [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) (a c : E') :
    Summable (fun k => ⟪ContinuousLinearMap.adjoint (A k) a,
        Y (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) ∧
      ‖krausMatG A Y a c‖ ≤ ‖a‖ * ‖c‖ * (trB b Y).toReal := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  rw [trB_eq_HS b hT] at hYf ⊢
  obtain ⟨hs, hb⟩ := kraus_cross b hA T T hYf.ne hYf.ne a c
  refine ⟨hs.congr fun k => (inner_TT hT _ _).symm, ?_⟩
  unfold krausMatG
  calc ‖∑' k, ⟪ContinuousLinearMap.adjoint (A k) a,
          (T ∘L T) (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖
      = ‖∑' k, ⟪T (ContinuousLinearMap.adjoint (A k) a),
          T (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖ := by
        congr 1
        exact tsum_congr fun k => inner_TT hT _ _
    _ ≤ _ := hb
    _ = ‖a‖ * ‖c‖ * (HS b T).toReal := by rw [Real.mul_self_sqrt ENNReal.toReal_nonneg]

private lemma krausMatG_self_eq [CompleteSpace E] [CompleteSpace E'] {A : ℕ → E →L[ℂ] E'}
    {T : E →L[ℂ] E} (hT : ContinuousLinearMap.adjoint T = T) (x : E') :
    krausMatG A (T ∘L T) x x =
      ((∑' k, ‖T (ContinuousLinearMap.adjoint (A k) x)‖ ^ 2 : ℝ) : ℂ) := by
  unfold krausMatG
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [inner_TT hT, inner_self_ofReal]

private lemma trB_kraus_eq [CompleteSpace E] [CompleteSpace E'] {ι' : Type*}
    (b : HilbertBasis ι ℂ E) (b' : HilbertBasis ι' ℂ E') {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {T : E →L[ℂ] E} (hT : ContinuousLinearMap.adjoint T = T) (hf : HS b T ≠ ∞)
    {Z : E' →L[ℂ] E'} (hZ : ∀ a c, ⟪a, Z c⟫_ℂ = krausMatG A (T ∘L T) a c) :
    trB b' Z = ∑' i, ∑' k, ENNReal.ofReal (‖A k (T (b i))‖ ^ 2) := by
  have h1 : ∀ x : E', (⟪x, Z x⟫_ℂ).re =
      ∑' k, ‖T (ContinuousLinearMap.adjoint (A k) x)‖ ^ 2 := fun x => by
    rw [hZ, krausMatG_self_eq hT, Complex.ofReal_re]
  have hsx : ∀ x : E', Summable fun k => ‖T (ContinuousLinearMap.adjoint (A k) x)‖ ^ 2 :=
    fun x => (real_bound (kraus_K1 b hA T x) (fun k => sq_nonneg _) (sq_nonneg _) hf).1
  unfold trB
  calc ∑' j, ENNReal.ofReal (⟪b' j, Z (b' j)⟫_ℂ).re
      = ∑' j, ∑' k, ENNReal.ofReal (‖T (ContinuousLinearMap.adjoint (A k) (b' j))‖ ^ 2) := by
        refine tsum_congr fun j => ?_
        rw [h1, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) (hsx _)]
    _ = ∑' k, ∑' j, ENNReal.ofReal (‖T (ContinuousLinearMap.adjoint (A k) (b' j))‖ ^ 2) :=
        ENNReal.tsum_comm
    _ = ∑' k, ∑' i, ENNReal.ofReal (‖A k (T (b i))‖ ^ 2) := by
        refine tsum_congr fun k => ?_
        have h := HS_adjoint b' b (T ∘L ContinuousLinearMap.adjoint (A k))
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hT] at h
        unfold HS at h
        exact h
    _ = ∑' i, ∑' k, ENNReal.ofReal (‖A k (T (b i))‖ ^ 2) := ENNReal.tsum_comm

private lemma hN_sum [CompleteSpace E] [CompleteSpace E'] {A : ℕ → E →L[ℂ] E'}
    (hN : ∀ ψ : E, HasSum (fun k => ContinuousLinearMap.adjoint (A k) (A k ψ)) ψ) (ψ : E) :
    HasSum (fun k => ‖A k ψ‖ ^ 2) (‖ψ‖ ^ 2) := by
  have h2 := Complex.reCLM.hasSum ((innerSL ℂ ψ).hasSum (hN ψ))
  simp only [Complex.reCLM_apply, innerSL_apply_apply,
    ContinuousLinearMap.adjoint_inner_right] at h2
  simpa only [re_inner_self'] using h2

/-- The orthogonal projection onto the span of `b i`, `i ∈ s`. -/
private def prj (b : HilbertBasis ι ℂ E) (s : Finset ι) : E →L[ℂ] E :=
  ∑ i ∈ s, rk1 (b i) (b i)

private lemma prj_apply (b : HilbertBasis ι ℂ E) (s : Finset ι) (x : E) :
    prj b s x = ∑ i ∈ s, ⟪b i, x⟫_ℂ • b i := by
  simp only [prj, sum_apply, rk1_apply]

private lemma prj_of_mem (b : HilbertBasis ι ℂ E) {s : Finset ι} {j : ι} (hj : j ∈ s) :
    prj b s (b j) = b j := by
  classical
  rw [prj_apply, Finset.sum_eq_single j]
  · rw [inner_self_ofReal, b.orthonormal.1 j]
    simp
  · intro i _ hij
    rw [b.orthonormal.2 hij, zero_smul]
  · intro h
    exact absurd hj h

private lemma prj_of_nmem (b : HilbertBasis ι ℂ E) {s : Finset ι} {j : ι} (hj : j ∉ s) :
    prj b s (b j) = 0 := by
  rw [prj_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  rw [b.orthonormal.2 hij, zero_smul]

private lemma prj_inner (b : HilbertBasis ι ℂ E) (s : Finset ι) (Y : E →L[ℂ] E) (x z : E) :
    ⟪prj b s x, Y (prj b s z)⟫_ℂ =
      ∑ i ∈ s, ∑ j ∈ s, ⟪b i, Y (b j)⟫_ℂ * (⟪x, b i⟫_ℂ * ⟪b j, z⟫_ℂ) := by
  rw [prj_apply, prj_apply, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

private lemma HS_S2_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (s : Finset ι) :
    HS b (T ∘L prj b s) ≤ HS b T := by
  unfold HS
  refine ENNReal.tsum_le_tsum fun i => ?_
  by_cases hi : i ∈ s
  · simp only [ContinuousLinearMap.comp_apply, prj_of_mem b hi, le_refl]
  · simp [prj_of_nmem b hi]

private lemma HS_S1_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (s : Finset ι) :
    HS b (T - T ∘L prj b s) ≤ HS b T := by
  unfold HS
  refine ENNReal.tsum_le_tsum fun i => ?_
  by_cases hi : i ∈ s
  · simp [prj_of_mem b hi]
  · simp [prj_of_nmem b hi]

private lemma HS_S1_eq (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (s : Finset ι) :
    HS b (T - T ∘L prj b s) = ∑' i : {x // x ∉ s}, ENNReal.ofReal (‖T (b i)‖ ^ 2) := by
  classical
  have h := tsum_subtype ({x | x ∉ s} : Set ι) (fun i => ENNReal.ofReal (‖T (b i)‖ ^ 2))
  refine Eq.trans ?_ h.symm
  unfold HS
  refine tsum_congr fun i => ?_
  by_cases hi : i ∈ s
  · simp [hi, prj_of_mem b hi]
  · simp [hi, prj_of_nmem b hi]

private lemma kraus_split [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    (T S : E →L[ℂ] E) (hT : HS b T ≠ ∞) (hS : HS b S ≠ ∞) (hST : HS b S ≤ HS b T)
    (hR : HS b (T - S) ≠ ∞) (a c : E') {F K : ℂ}
    (hF : HasSum (fun k => ⟪S (ContinuousLinearMap.adjoint (A k) a),
      S (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) F)
    (hK : HasSum (fun k => ⟪T (ContinuousLinearMap.adjoint (A k) a),
      T (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) K) :
    ‖F - K‖ ≤
      2 * (‖a‖ * ‖c‖ * Real.sqrt (HS b T).toReal) * Real.sqrt (HS b (T - S)).toReal := by
  obtain ⟨sA, bA⟩ := kraus_cross b hA (T - S) T hR hT a c
  obtain ⟨sB, bB⟩ := kraus_cross b hA S (T - S) hS hR a c
  have h2 : HasSum (fun k => ⟪S (ContinuousLinearMap.adjoint (A k) a),
      S (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ - ⟪T (ContinuousLinearMap.adjoint (A k) a),
      T (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ)
      (-(∑' k, ⟪(T - S) (ContinuousLinearMap.adjoint (A k) a),
          T (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ +
        ∑' k, ⟪S (ContinuousLinearMap.adjoint (A k) a),
          (T - S) (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ)) := by
    convert (sA.hasSum.add sB.hasSum).neg using 1
    funext k
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    ring
  rw [(hF.sub hK).unique h2, norm_neg]
  have hm : Real.sqrt (HS b S).toReal ≤ Real.sqrt (HS b T).toReal :=
    Real.sqrt_le_sqrt ((ENNReal.toReal_le_toReal hS hT).mpr hST)
  have hx := mul_nonneg (norm_nonneg a) (norm_nonneg c)
  have hr := Real.sqrt_nonneg (HS b (T - S)).toReal
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖c‖ * (Real.sqrt (HS b (T - S)).toReal * Real.sqrt (HS b T).toReal) +
        ‖a‖ * ‖c‖ * (Real.sqrt (HS b S).toReal * Real.sqrt (HS b (T - S)).toReal) :=
          add_le_add bA bB
    _ ≤ ‖a‖ * ‖c‖ * (Real.sqrt (HS b (T - S)).toReal * Real.sqrt (HS b T).toReal) +
        ‖a‖ * ‖c‖ * (Real.sqrt (HS b T).toReal * Real.sqrt (HS b (T - S)).toReal) := by
          gcongr
    _ = _ := by ring

/-- The Kraus series converges (absolutely) for `∑_k A_k† A_k ≤ I` and positive trace-class `Y`
(def:s-meas, docstring of `Alg.bounded`: `bounded` makes `krausMat` absolutely summable). -/
theorem krausMatG_hasSum [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) (a c : E') :
    HasSum (fun k => ⟪ContinuousLinearMap.adjoint (A k) a,
      Y (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) (krausMatG A Y a c) := by
  exact (kraus_terms b hA hY hYf a c).1.hasSum

/-- `Γ(Y) = ∑_k A_k Y A_k†` is a positive bounded operator for positive trace-class `Y` (def:s-meas: a
family with `∑_k A_k† A_k ≤ I` defines a bounded CP map; with `trB_le_of_krausMatG`, `Γ(Y) ∈ 𝒯(E')₊`). -/
theorem exists_krausOp [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) :
    ∃ Z : E' →L[ℂ] E', Z.IsPositive ∧ ∀ a c, ⟪a, Z c⟫_ℂ = krausMatG A Y a c := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  have hsum := fun a c => (kraus_terms b hA hY hYf a c).1
  have hbd := fun a c => (kraus_terms b hA hY hYf a c).2
  let f : E' →ₗ⋆[ℂ] E' →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (krausMatG A (T ∘L T))
      (fun a₁ a₂ c => by
        simp only [krausMatG, map_add, inner_add_left]
        exact (hsum a₁ c).tsum_add (hsum a₂ c))
      (fun r a c => by
        simp only [krausMatG, map_smul, inner_smul_left, smul_eq_mul]
        exact tsum_mul_left)
      (fun a c₁ c₂ => by
        simp only [krausMatG, map_add, inner_add_right]
        exact (hsum a c₁).tsum_add (hsum a c₂))
      (fun r a c => by
        simp only [krausMatG, map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left)
  let B : E' →L⋆[ℂ] E' →L[ℂ] ℂ :=
    f.mkContinuous₂ (trB b (T ∘L T)).toReal (fun a c => le_of_le_of_eq (hbd a c) (by ring))
  have hZ : ∀ a c, ⟪a, ContinuousLinearMap.adjoint
      (InnerProductSpace.continuousLinearMapOfBilin B) c⟫_ℂ = krausMatG A (T ∘L T) a c :=
    fun a c => by
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact InnerProductSpace.continuousLinearMapOfBilin_apply B a c
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin B), ?_, hZ⟩
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have h1 : ⟪ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin B) x,
      x⟫_ℂ = ((∑' k, ‖T (ContinuousLinearMap.adjoint (A k) x)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hZ, krausMatG_self_eq hT, Complex.conj_ofReal]
  rw [h1]
  constructor
  · simp only [RCLike.re_to_complex, Complex.ofReal_re]
  · simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact tsum_nonneg fun k => sq_nonneg _

/-- `tr Γ(Y) ≤ tr Y` for `∑_k A_k† A_k ≤ I` (def:s-meas, docstring of `Alg.bounded`; the trace
condition of a measurable CP kernel, paragraph "Kernels"). -/
theorem trB_le_of_krausMatG [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {ι' : Type*} {b' : HilbertBasis ι' ℂ E'} {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) {Z : E' →L[ℂ] E'}
    (hZ : ∀ a c, ⟪a, Z c⟫_ℂ = krausMatG A Y a c) : trB b' Z ≤ trB b Y := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  rw [trB_eq_HS b hT] at hYf ⊢
  rw [trB_kraus_eq b b' hA hT hYf.ne hZ]
  unfold HS
  exact ENNReal.tsum_le_tsum fun i => hA (T (b i))

/-- `tr Γ(Y) = tr Y` for `∑_k A_k† A_k = I` strongly (def:s-meas, docstring of `Alg.normalised`:
`I(Ω)` preserves the trace). `hN` implies the bound `hA` of the other lemmas. -/
theorem trB_eq_of_krausMatG [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {ι' : Type*} {b' : HilbertBasis ι' ℂ E'} {A : ℕ → E →L[ℂ] E'}
    (hN : ∀ ψ : E, HasSum (fun k => ContinuousLinearMap.adjoint (A k) (A k ψ)) ψ)
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) {Z : E' →L[ℂ] E'}
    (hZ : ∀ a c, ⟪a, Z c⟫_ℂ = krausMatG A Y a c) : trB b' Z = trB b Y := by
  have hAeq : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) = ENNReal.ofReal (‖ψ‖ ^ 2) :=
    fun ψ => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) (hN_sum hN ψ).summable,
        (hN_sum hN ψ).tsum_eq]
  have hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2) :=
    fun ψ => (hAeq ψ).le
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  rw [trB_eq_HS b hT] at hYf ⊢
  rw [trB_kraus_eq b b' hA hT hYf.ne hZ]
  unfold HS
  exact tsum_congr fun i => hAeq (T (b i))

/-- Additivity of a Kraus map on positive trace-class operators (linearity of `Γ`, lem:m-int(iii) and
lem:m-comp). -/
theorem krausMatG_add [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y Z : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) (hZ : Z.IsPositive)
    (hZf : trB b Z < ∞) (a c : E') :
    krausMatG A (Y + Z) a c = krausMatG A Y a c + krausMatG A Z a c := by
  have s1 := (kraus_terms b hA hY hYf a c).1
  have s2 := (kraus_terms b hA hZ hZf a c).1
  simp only [krausMatG, add_apply, inner_add_right]
  exact s1.tsum_add s2

/-- Homogeneity of a Kraus map (linearity of `Γ`, lem:m-int(iii) and lem:m-comp(iii)); no hypotheses,
the junk value `0` of a non-summable series scales too. -/
theorem krausMatG_smul [CompleteSpace E] [CompleteSpace E'] (A : ℕ → E →L[ℂ] E') (Y : E →L[ℂ] E)
    (r : ℂ) (a c : E') :
    krausMatG A (r • Y) a c = r * krausMatG A Y a c := by
  simp only [krausMatG, smul_apply, inner_smul_right]
  exact tsum_mul_left

/-- A Kraus map on a matrix unit: `⟪a, Γ(|u⟩⟨v|) c⟫ = ∑_k ⟪a, A_k u⟫ ⟪A_k v, c⟫`, the series converging
(proof of lem:m-comp(i): `tr(B Γ_h(G_h)(|e_i⟩⟨e_j|))`). -/
theorem krausMatG_rk1_hasSum [CompleteSpace E] [CompleteSpace E'] {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    (u v : E) (a c : E') :
    HasSum (fun k => ⟪a, A k u⟫_ℂ * ⟪A k v, c⟫_ℂ) (krausMatG A (rk1 u v) a c) := by
  have hterm : ∀ k, ⟪ContinuousLinearMap.adjoint (A k) a,
      rk1 u v (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ = ⟪a, A k u⟫_ℂ * ⟪A k v, c⟫_ℂ := by
    intro k
    rw [rk1_apply, inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  have hfin : ∀ w : E, Summable fun k => ‖A k w‖ ^ 2 := fun w =>
    summable_of_enn (fun k => sq_nonneg _) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hA w))
  have su := hfin u
  have sv := hfin v
  have hs : Summable fun k => ⟪a, A k u⟫_ℂ * ⟪A k v, c⟫_ℂ := by
    refine Summable.of_norm_bounded ((su.add sv).mul_left (‖a‖ * ‖c‖)) fun k => ?_
    rw [norm_mul]
    have h1 := norm_inner_le_norm (𝕜 := ℂ) a (A k u)
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (A k v) c
    have h3 : ‖A k u‖ * ‖A k v‖ ≤ ‖A k u‖ ^ 2 + ‖A k v‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A k u‖ - ‖A k v‖), norm_nonneg (A k u), norm_nonneg (A k v)]
    calc ‖⟪a, A k u⟫_ℂ‖ * ‖⟪A k v, c⟫_ℂ‖ ≤ (‖a‖ * ‖A k u‖) * (‖A k v‖ * ‖c‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖a‖ * ‖c‖ * (‖A k u‖ * ‖A k v‖) := by ring
      _ ≤ ‖a‖ * ‖c‖ * (‖A k u‖ ^ 2 + ‖A k v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have heq : krausMatG A (rk1 u v) a c = ∑' k, ⟪a, A k u⟫_ℂ * ⟪A k v, c⟫_ℂ := by
    unfold krausMatG
    exact tsum_congr hterm
  rw [heq]
  exact hs.hasSum

/-- Polarisation: a Kraus map on the matrix unit `|u⟩⟨v|` is a combination of its values on the four
positive operators `|u + iᵐ v⟩⟨u + iᵐ v|` (proof of lem:m-comp(i), reduction to positive inputs). -/
theorem krausMatG_rk1_polar [CompleteSpace E] [CompleteSpace E'] {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    (u v : E) (a c : E') :
    krausMatG A (rk1 u v) a c = (1 / 4 : ℂ) * ∑ m : Fin 4,
      Complex.I ^ (m : ℕ) * krausMatG A (rk1 (u + Complex.I ^ (m : ℕ) • v)
        (u + Complex.I ^ (m : ℕ) • v)) a c := by
  have hm : ∀ m ∈ (Finset.univ : Finset (Fin 4)), HasSum (fun k => Complex.I ^ (m : ℕ) *
      (⟪a, A k (u + Complex.I ^ (m : ℕ) • v)⟫_ℂ * ⟪A k (u + Complex.I ^ (m : ℕ) • v), c⟫_ℂ))
      (Complex.I ^ (m : ℕ) * krausMatG A (rk1 (u + Complex.I ^ (m : ℕ) • v)
        (u + Complex.I ^ (m : ℕ) • v)) a c) :=
    fun m _ => (krausMatG_rk1_hasSum hA _ _ a c).mul_left _
  have hsum := (hasSum_sum hm).mul_left (1 / 4 : ℂ)
  have key : ∀ k, (1 / 4 : ℂ) * ∑ m ∈ (Finset.univ : Finset (Fin 4)), Complex.I ^ (m : ℕ) *
      (⟪a, A k (u + Complex.I ^ (m : ℕ) • v)⟫_ℂ * ⟪A k (u + Complex.I ^ (m : ℕ) • v), c⟫_ℂ) =
      ⟪a, A k u⟫_ℂ * ⟪A k v, c⟫_ℂ := by
    intro k
    have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have hI := Complex.I_sq
    rw [Fin.sum_univ_four]
    simp only [e0, e1, e2, e3, map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, map_pow, Complex.conj_I]
    linear_combination (1 / 4 : ℂ) *
      (⟪a, A k u⟫_ℂ * ⟪A k u, c⟫_ℂ * (1 + Complex.I) +
        ⟪a, A k u⟫_ℂ * ⟪A k v, c⟫_ℂ * (-Complex.I ^ 4 + 2 * Complex.I ^ 2 - 3) +
        ⟪a, A k v⟫_ℂ * ⟪A k u, c⟫_ℂ * (1 + Complex.I ^ 4) +
        ⟪a, A k v⟫_ℂ * ⟪A k v, c⟫_ℂ * (1 - Complex.I ^ 3) *
          (1 - Complex.I ^ 2 + Complex.I ^ 4)) * hI
  refine (krausMatG_rk1_hasSum hA u v a c).unique ?_
  convert hsum using 1
  funext k
  exact (key k).symm

/-- Composition: `∑_k (A_k B) Y (A_k B)† = ∑_k A_k (B Y B†) A_k†`, termwise, no hypotheses (the
isometries `V` and the `β_x` of lem:m-comp and lem:m-joint composed with an instrument). -/
theorem krausMatG_comp {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [CompleteSpace E] [CompleteSpace E'] (A : ℕ → E →L[ℂ] E') (B : E₀ →L[ℂ] E) (Y : E₀ →L[ℂ] E₀)
    (a c : E') :
    krausMatG (fun k => A k ∘L B) Y a c =
      krausMatG A (B ∘L Y ∘L ContinuousLinearMap.adjoint B) a c := by
  simp only [krausMatG, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- Bound on the matrix elements of a Kraus image, `|⟪a, Γ(Y) c⟫| ≤ ‖a‖ ‖c‖ tr Y` (domination in the
proofs of lem:m-int(iii) and lem:m-comp(i)). -/
theorem norm_krausMatG_le [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) (a c : E') :
    ‖krausMatG A Y a c‖ ≤ ‖a‖ * ‖c‖ * (trB b Y).toReal := by
  exact (kraus_terms b hA hY hYf a c).2

/-- Measurability of the matrix elements of a Kraus image of a measurable family (lem:m-comp(i):
`h ↦ Γ_h(G_h)` has measurable matrix elements). -/
theorem measurable_krausMatG [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {α : Type*} [MeasurableSpace α] {Yf : α → E →L[ℂ] E} (hpos : ∀ h, (Yf h).IsPositive)
    (hfin : ∀ h, trB b (Yf h) < ∞) (hmeas : ∀ x y : E, Measurable (fun h => ⟪x, Yf h y⟫_ℂ))
    (a c : E') : Measurable (fun h => krausMatG A (Yf h) a c) := by
  have hlim : ∀ h, Tendsto (fun n => ∑ k ∈ Finset.range n,
      ⟪ContinuousLinearMap.adjoint (A k) a, Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ)
      atTop (𝓝 (krausMatG A (Yf h) a c)) :=
    fun h => (kraus_terms b hA (hpos h) (hfin h) a c).1.hasSum.tendsto_sum_nat
  refine measurable_of_tendsto_metrizable (f := fun n h => ∑ k ∈ Finset.range n,
      ⟪ContinuousLinearMap.adjoint (A k) a, Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ)
    (fun n => ?_) (tendsto_pi_nhds.mpr hlim)
  exact Finset.measurable_sum (f := fun k h =>
      ⟪ContinuousLinearMap.adjoint (A k) a, Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ)
    (Finset.range n) fun k _ => hmeas _ _

/-- (M1) for Kraus maps: `P_s Y P_s = ∑_{i,j ∈ s} ⟪b_i, Y b_j⟫ |b_i⟩⟨b_j|` converges to `Y` in trace
norm along finite sets `s` of basis indices, and a Kraus map is trace-norm continuous, so the matrix
elements of `Γ(P_s Y P_s)` converge to those of `Γ(Y)` (paragraph "Notation", first standard fact and
(M1); proof of lem:m-comp(i)). -/
theorem krausMatG_tendsto_matrix [CompleteSpace E] [CompleteSpace E'] {b : HilbertBasis ι ℂ E}
    {A : ℕ → E →L[ℂ] E'}
    (hA : ∀ ψ : E, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y : E →L[ℂ] E} (hY : Y.IsPositive) (hYf : trB b Y < ∞) (a c : E') :
    Tendsto (fun s : Finset ι => ∑ i ∈ s, ∑ j ∈ s,
        ⟪b i, Y (b j)⟫_ℂ * krausMatG A (rk1 (b i) (b j)) a c)
      atTop (𝓝 (krausMatG A Y a c)) := by
  obtain ⟨T, hT, rfl⟩ := exists_sqrt hY
  have hf : HS b T ≠ ∞ := by
    rw [← trB_eq_HS b hT]
    exact hYf.ne
  have hK : HasSum (fun k => ⟪T (ContinuousLinearMap.adjoint (A k) a),
      T (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) (krausMatG A (T ∘L T) a c) := by
    have h := krausMatG_hasSum (b := b) hA hY hYf a c
    simp only [inner_TT hT] at h
    exact h
  have hF : ∀ s : Finset ι, HasSum
      (fun k => ⟪(T ∘L prj b s) (ContinuousLinearMap.adjoint (A k) a),
        (T ∘L prj b s) (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ)
      (∑ i ∈ s, ∑ j ∈ s, ⟪b i, (T ∘L T) (b j)⟫_ℂ * krausMatG A (rk1 (b i) (b j)) a c) := by
    intro s
    have h := hasSum_sum fun i (_ : i ∈ s) => hasSum_sum fun j (_ : j ∈ s) =>
      (krausMatG_rk1_hasSum hA (b i) (b j) a c).mul_left ⟪b i, (T ∘L T) (b j)⟫_ℂ
    convert h using 1
    funext k
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← inner_TT hT, prj_inner]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hd : Tendsto (fun s : Finset ι => (HS b (T - T ∘L prj b s)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (ENNReal.tendsto_tsum_compl_atTop_zero (f := fun i => ENNReal.ofReal (‖T (b i)‖ ^ 2)) hf)
    rw [ENNReal.toReal_zero] at h
    refine h.congr fun s => ?_
    simp only [Function.comp_apply, HS_S1_eq]
  have hlim : Tendsto (fun s : Finset ι => 2 * (‖a‖ * ‖c‖ * Real.sqrt (HS b T).toReal) *
      Real.sqrt (HS b (T - T ∘L prj b s)).toReal) atTop (𝓝 0) := by
    have h := hd.sqrt.const_mul (2 * (‖a‖ * ‖c‖ * Real.sqrt (HS b T).toReal))
    rw [Real.sqrt_zero, mul_zero] at h
    exact h
  exact squeeze_zero (fun s => norm_nonneg _) (fun s => kraus_split b hA T (T ∘L prj b s) hf
    (ne_top_of_le_ne_top hf (HS_S2_le b T s)) (HS_S2_le b T s)
    (ne_top_of_le_ne_top hf (HS_S1_le b T s)) a c (hF s) hK) hlim

end Kraus

end

end TheoremS.Meas
