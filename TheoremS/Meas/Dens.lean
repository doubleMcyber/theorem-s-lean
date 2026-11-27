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
Lemma lem:m-int (weak integral) and Lemma lem:m-dens (densities) of the paper's section on measurable outcome
spaces, and the facts about positive operator measures in its paragraph "Operator measures".

Hypotheses of lem:m-int: `Yf h` positive, measurable matrix elements, `∫ tr (Yf h) dτ < ∞`.
-/
import TheoremS.Meas.Trace

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

/-! ### Helpers -/

section BdHelpers

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem bd_re_nonneg {Y : E →L[ℂ] E} (hY : Y.IsPositive) (x : E) : 0 ≤ (⟪x, Y x⟫_ℂ).re := by
  simpa using hY.re_inner_nonneg_right x

theorem bd_inner_self_eq_re {Y : E →L[ℂ] E} (hY : Y.IsPositive) (x : E) :
    ⟪x, Y x⟫_ℂ = ((⟪x, Y x⟫_ℂ).re : ℂ) := by
  have h := ((ContinuousLinearMap.isPositive_iff_complex Y).1 hY x).1
  have him : (⟪Y x, x⟫_ℂ).im = 0 := by
    have := congrArg Complex.im h
    simpa using this.symm
  rw [← hY.inner_left_eq_inner_right]
  exact Complex.ext (by simp) (by simp [him])

theorem bd_isPositive_of_real {T : E →L[ℂ] E}
    (h : ∀ x, ∃ r : ℝ, 0 ≤ r ∧ ⟪x, T x⟫_ℂ = r) : T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨r, hr, hx⟩ := h x
  have h' : ⟪T x, x⟫_ℂ = r := by rw [← inner_conj_symm, hx, Complex.conj_ofReal]
  rw [h']
  simp [hr]

theorem bd_cs_of_forms (P m m' Q : ℂ) (hm' : m' = starRingEnd ℂ m) (hP : 0 ≤ P.re) (hQ : 0 ≤ Q.re)
    (h : ∀ z : ℂ, 0 ≤ (starRingEnd ℂ z * z * P + starRingEnd ℂ z * m + z * m' + Q).re) :
    ‖m‖ ^ 2 ≤ P.re * Q.re := by
  subst hm'
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Complex.normSq m := ⟨_, rfl⟩
  have hMn : ‖m‖ ^ 2 = M := by rw [hM, Complex.normSq_eq_norm_sq]
  have hM0 : 0 ≤ M := by rw [hM]; exact Complex.normSq_nonneg m
  have hmm : starRingEnd ℂ m * m = (M : ℂ) := by rw [hM, Complex.normSq_eq_conj_mul_self]
  have hmm' : m * starRingEnd ℂ m = (M : ℂ) := by rw [mul_comm, hmm]
  have key : ∀ t : ℝ, 0 ≤ (M * P.re) * (t * t) + (2 * M) * t + Q.re := by
    intro t
    have h1 := h ((t : ℂ) * m)
    have e : starRingEnd ℂ ((t : ℂ) * m) * ((t : ℂ) * m) * P + starRingEnd ℂ ((t : ℂ) * m) * m
        + (t : ℂ) * m * starRingEnd ℂ m + Q
        = ((t * t * M : ℝ) : ℂ) * P + ((2 * t * M : ℝ) : ℂ) + Q := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      linear_combination ((t : ℂ) * t * P + t) * hmm + (t : ℂ) * hmm'
    rw [e] at h1
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at h1
    linarith [h1]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  rw [hMn]
  rcases hM0.lt_or_eq with hpos | hzero
  · nlinarith [mul_nonneg hP hQ]
  · rw [← hzero]; exact mul_nonneg hP hQ

/-- Cauchy-Schwarz for a positive operator. -/
theorem bd_op_cs {Y : E →L[ℂ] E} (hY : Y.IsPositive) (u v : E) :
    ‖⟪u, Y v⟫_ℂ‖ ^ 2 ≤ (⟪u, Y u⟫_ℂ).re * (⟪v, Y v⟫_ℂ).re := by
  refine bd_cs_of_forms _ _ ⟪v, Y u⟫_ℂ _ ?_ (bd_re_nonneg hY u) (bd_re_nonneg hY v) ?_
  · rw [inner_conj_symm, hY.inner_left_eq_inner_right]
  · intro z
    have h := bd_re_nonneg hY (z • u + v)
    have e : ⟪z • u + v, Y (z • u + v)⟫_ℂ = starRingEnd ℂ z * z * ⟪u, Y u⟫_ℂ
        + starRingEnd ℂ z * ⟪u, Y v⟫_ℂ + z * ⟪v, Y u⟫_ℂ + ⟪v, Y v⟫_ℂ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right]
      ring
    rw [← e]; exact h

theorem bd_exists_op [CompleteSpace E] (q : E → E → ℂ) (C : ℝ)
    (h1 : ∀ a a' b, q (a + a') b = q a b + q a' b)
    (h2 : ∀ (c : ℂ) a b, q (c • a) b = starRingEnd ℂ c * q a b)
    (h3 : ∀ a b b', q a (b + b') = q a b + q a b')
    (h4 : ∀ (c : ℂ) a b, q a (c • b) = c * q a b)
    (hC : ∀ a b, ‖q a b‖ ≤ C * ‖a‖ * ‖b‖) :
    ∃ T : E →L[ℂ] E, ∀ a b, ⟪a, T b⟫_ℂ = q a b := by
  let B₀ : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) q h1
    (fun c m n => by rw [h2, smul_eq_mul]) h3
    (fun c m n => by rw [h4, RingHom.id_apply, smul_eq_mul])
  let B : E →L⋆[ℂ] E →L[ℂ] ℂ := B₀.mkContinuous₂ C hC
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin B),
    fun a b => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

theorem bd_vec_ext {ι : Type*} [CompleteSpace E] (b : HilbertBasis ι ℂ E) {x y : E}
    (h : ∀ i, ⟪b i, x⟫_ℂ = ⟪b i, y⟫_ℂ) : x = y := by
  have hx := b.hasSum_repr x
  have hy := b.hasSum_repr y
  simp only [HilbertBasis.repr_apply_apply, h] at hx
  simp only [HilbertBasis.repr_apply_apply] at hy
  exact hx.unique hy

theorem bd_op_ext {ι : Type*} [CompleteSpace E] (b : HilbertBasis ι ℂ E) {Y Z : E →L[ℂ] E}
    (h : ∀ i j, ⟪b i, Y (b j)⟫_ℂ = ⟪b i, Z (b j)⟫_ℂ) : Y = Z := by
  have hcol : ∀ j, Y (b j) = Z (b j) := fun j => bd_vec_ext b fun i => h i j
  ext x
  have hY := (b.hasSum_repr x).mapL Y
  have hZ := (b.hasSum_repr x).mapL Z
  simp only [map_smul, hcol] at hY hZ
  exact hY.unique hZ

theorem bd_le_add_of_sq_le {m X Y : ℝ} (hm : 0 ≤ m) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : m ^ 2 ≤ X * Y) : m ≤ X + Y := by
  nlinarith [mul_nonneg hX hY, mul_nonneg hX hX, mul_nonneg hY hY]

theorem bd_enorm_le_add {Y : E →L[ℂ] E} (hY : Y.IsPositive) (u v : E) :
    ‖⟪u, Y v⟫_ℂ‖ₑ ≤ ENNReal.ofReal (⟪u, Y u⟫_ℂ).re + ENNReal.ofReal (⟪v, Y v⟫_ℂ).re := by
  have hu := bd_re_nonneg hY u
  have hv := bd_re_nonneg hY v
  have hn := bd_le_add_of_sq_le (norm_nonneg _) hu hv (bd_op_cs hY u v)
  rw [← ofReal_norm, ← ENNReal.ofReal_add hu hv]
  exact ENNReal.ofReal_le_ofReal hn

/-- Polarisation for an operator. -/
theorem bd_polar (T : E →L[ℂ] E) (a b : E) :
    ⟪a, T b⟫_ℂ = (⟪a + b, T (a + b)⟫_ℂ - ⟪a - b, T (a - b)⟫_ℂ
      - Complex.I * (⟪a + Complex.I • b, T (a + Complex.I • b)⟫_ℂ
        - ⟪a - Complex.I • b, T (a - Complex.I • b)⟫_ℂ)) / 4 := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  linear_combination (⟪a, T b⟫_ℂ - ⟪b, T a⟫_ℂ) / 2 * Complex.I_sq

theorem bd_bound_of_sq (q : E → E → ℂ)
    (h2 : ∀ (c : ℂ) a b, q (c • a) b = starRingEnd ℂ c * q a b)
    (h4 : ∀ (c : ℂ) a b, q a (c • b) = c * q a b) (C : ℝ)
    (hC : ∀ a b, ‖q a b‖ ≤ C * (‖a‖ ^ 2 + ‖b‖ ^ 2)) :
    ∀ a b, ‖q a b‖ ≤ 2 * C * ‖a‖ * ‖b‖ := by
  intro a b
  rcases eq_or_ne a 0 with rfl | ha
  · have h := h2 0 0 b
    simp only [smul_zero, map_zero, zero_mul] at h
    rw [h]; simp
  rcases eq_or_ne b 0 with rfl | hb
  · have h := h4 0 a 0
    simp only [smul_zero, zero_mul] at h
    rw [h]; simp
  have hra : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hrb : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hna : ‖((‖a‖⁻¹ : ℝ) : ℂ) • a‖ = 1 := by
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hra.ne']
  have hnb : ‖((‖b‖⁻¹ : ℝ) : ℂ) • b‖ = 1 := by
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hrb.ne']
  have h := hC (((‖a‖⁻¹ : ℝ) : ℂ) • a) (((‖b‖⁻¹ : ℝ) : ℂ) • b)
  rw [hna, hnb, h2, h4, Complex.conj_ofReal, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, norm_inv, norm_inv, norm_norm, norm_norm] at h
  calc ‖q a b‖ = (‖a‖ * ‖a‖⁻¹) * (‖b‖ * ‖b‖⁻¹) * ‖q a b‖ := by
        rw [mul_inv_cancel₀ hra.ne', mul_inv_cancel₀ hrb.ne', one_mul, one_mul]
    _ = ‖a‖ * ‖b‖ * (‖a‖⁻¹ * (‖b‖⁻¹ * ‖q a b‖)) := by ring
    _ ≤ ‖a‖ * ‖b‖ * (C * (1 ^ 2 + 1 ^ 2)) := mul_le_mul_of_nonneg_left (by linarith [h]) (by positivity)
    _ = 2 * C * ‖a‖ * ‖b‖ := by ring

theorem bd_forms_all (P m m' Q : ℂ)
    (h : ∀ n : ℕ, 0 ≤ (starRingEnd ℂ (TopologicalSpace.denseSeq ℂ n) * TopologicalSpace.denseSeq ℂ n * P
      + starRingEnd ℂ (TopologicalSpace.denseSeq ℂ n) * m + TopologicalSpace.denseSeq ℂ n * m'
      + Q).re) :
    ∀ z : ℂ, 0 ≤ (starRingEnd ℂ z * z * P + starRingEnd ℂ z * m + z * m' + Q).re := by
  have hc : Continuous fun z : ℂ => starRingEnd ℂ z * z * P + starRingEnd ℂ z * m + z * m' + Q :=
    ((((Complex.continuous_conj.mul continuous_id).mul continuous_const).add
      (Complex.continuous_conj.mul continuous_const)).add
      (continuous_id.mul continuous_const)).add continuous_const
  exact isClosed_property (TopologicalSpace.denseRange_denseSeq ℂ)
    (isClosed_le continuous_const (Complex.continuous_re.comp hc)) h

end BdHelpers

section WeakIntegral

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {α : Type} [MeasurableSpace α]

/-- `h ↦ tr Y_h` is measurable (used in lem:m-int(ii), "by monotone convergence"; needs the countable
basis of a separable `H`). -/
theorem measurable_tr [TopologicalSpace.SeparableSpace K] {Yf : α → Op N K}
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, Yf h b⟫_ℂ)) :
    Measurable (fun h => tr (Yf h)) := by
  have : Countable (basisSet N K) := basisSet_countable.to_subtype
  show Measurable fun h => ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Yf h e⟫_ℂ).re
  exact Measurable.ennreal_tsum fun e => ENNReal.measurable_ofReal.comp
    (Complex.measurable_re.comp (hmeas _ _))

omit [CompleteSpace K] in
theorem bd_meas_re {Yf : α → Op N K}
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, Yf h b⟫_ℂ)) (x y : H N K) :
    Measurable (fun h => ENNReal.ofReal (⟪x, Yf h y⟫_ℂ).re) :=
  ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp (hmeas x y))

theorem bd_enorm_inner_le {Y : Op N K} (hY : Y.IsPositive) (a b : H N K) :
    ‖⟪a, Y b⟫_ℂ‖ₑ ≤ ENNReal.ofReal (‖a‖ * ‖b‖) * tr Y := by
  rcases eq_or_ne (tr Y) ⊤ with htop | hfin
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    rw [htop, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (mul_pos (norm_pos_iff.2 ha) (norm_pos_iff.2 hb))).ne'
  · rw [tr_eq_trB] at hfin ⊢
    have h := norm_inner_le_trB hY hfin.lt_top a b
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖⟪a, Y b⟫_ℂ‖
        ≤ ENNReal.ofReal (‖a‖ * ‖b‖ * (trB (hbasis N K) Y).toReal) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal (‖a‖ * ‖b‖) * trB (hbasis N K) Y := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin]

/-- The matrix elements `h ↦ ⟪a, Y_h b⟫` are integrable (lem:m-int(i) with `B = |b⟩⟨a|`, and the
bound `|q(a, b)| ≤ ‖a‖ ‖b‖ ∫ tr Y_h` of the proof of lem:m-int(ii)). -/
theorem integrable_inner {τ : Measure α} {Yf : α → Op N K}
    (hpos : ∀ h, (Yf h).IsPositive)
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hint : ∫⁻ h, tr (Yf h) ∂τ < ∞) (a b : H N K) :
    Integrable (fun h => ⟪a, Yf h b⟫_ℂ) τ := by
  refine ⟨(hmeas a b).aestronglyMeasurable, ?_⟩
  show ∫⁻ h, ‖⟪a, Yf h b⟫_ℂ‖ₑ ∂τ < ∞
  calc ∫⁻ h, ‖⟪a, Yf h b⟫_ℂ‖ₑ ∂τ ≤ ∫⁻ h, ENNReal.ofReal (‖a‖ * ‖b‖) * tr (Yf h) ∂τ :=
        lintegral_mono fun h => bd_enorm_inner_le (hpos h) a b
    _ = ENNReal.ofReal (‖a‖ * ‖b‖) * ∫⁻ h, tr (Yf h) ∂τ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

theorem bd_norm_integral_le {τ : Measure α} {Yf : α → Op N K}
    (hpos : ∀ h, (Yf h).IsPositive) (hint : ∫⁻ h, tr (Yf h) ∂τ < ∞) (a b : H N K) :
    ‖∫ h, ⟪a, Yf h b⟫_ℂ ∂τ‖ ≤ (∫⁻ h, tr (Yf h) ∂τ).toReal * ‖a‖ * ‖b‖ := by
  have h1 : ‖∫ h, ⟪a, Yf h b⟫_ℂ ∂τ‖ₑ ≤ ENNReal.ofReal (‖a‖ * ‖b‖) * ∫⁻ h, tr (Yf h) ∂τ :=
    calc ‖∫ h, ⟪a, Yf h b⟫_ℂ ∂τ‖ₑ ≤ ∫⁻ h, ‖⟪a, Yf h b⟫_ℂ‖ₑ ∂τ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ h, ENNReal.ofReal (‖a‖ * ‖b‖) * tr (Yf h) ∂τ :=
          lintegral_mono fun h => bd_enorm_inner_le (hpos h) a b
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint.ne) h1
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  calc ‖∫ h, ⟪a, Yf h b⟫_ℂ ∂τ‖ ≤ ‖a‖ * ‖b‖ * (∫⁻ h, tr (Yf h) ∂τ).toReal := h2
    _ = _ := by ring

-- CHANGED: added `[TopologicalSpace.SeparableSpace K]`. Without it the trace identity fails: for
-- `K = ℓ²([0,1])`, `τ` Lebesgue measure on `[0,1]` and `Yf h = |e_h⟩⟨e_h|` (uncountably many basis
-- vectors `e_h`), every matrix element `h ↦ ⟪a, Yf h b⟫` vanishes off a countable set, so the weak
-- integral is `0`, while `∫ tr (Yf h) dτ = 1`. Positivity and the matrix elements hold without it.
/-- Lemma lem:m-int(ii): the weak integral `Y = ∫ Y_h τ(dh)` exists, is positive trace class with
`tr Y = ∫ tr Y_h dτ`, and has matrix elements `⟪a, Y b⟫ = ∫ ⟪a, Y_h b⟫ dτ` (which is `tr(B Y) =
∫ tr(B Y_h) dτ` for `B = |b⟩⟨a|`). Uniqueness is `ext_inner_left` and is not stated. -/
theorem exists_weakInt [TopologicalSpace.SeparableSpace K] {τ : Measure α} {Yf : α → Op N K}
    (hpos : ∀ h, (Yf h).IsPositive)
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hint : ∫⁻ h, tr (Yf h) ∂τ < ∞) :
    ∃ Y : Op N K, PosTC Y ∧ tr Y = ∫⁻ h, tr (Yf h) ∂τ ∧
      ∀ a b : H N K, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂τ := by
  have hI := integrable_inner hpos hmeas hint
  obtain ⟨Y, hY⟩ : ∃ Y : Op N K, ∀ a b, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂τ :=
    bd_exists_op (fun a b => ∫ h, ⟪a, Yf h b⟫_ℂ ∂τ) (∫⁻ h, tr (Yf h) ∂τ).toReal
      (fun a a' b => by simp only [inner_add_left]; exact integral_add (hI a b) (hI a' b))
      (fun c a b => by simp only [inner_smul_left]; exact integral_const_mul _ _)
      (fun a b b' => by
        simp only [map_add, inner_add_right]; exact integral_add (hI a b) (hI a b'))
      (fun c a b => by simp only [map_smul, inner_smul_right]; exact integral_const_mul _ _)
      (bd_norm_integral_le hpos hint)
  have hYre : ∀ x, ⟪x, Y x⟫_ℂ = ((∫ h, (⟪x, Yf h x⟫_ℂ).re ∂τ : ℝ) : ℂ) := by
    intro x
    rw [hY, ← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ fun h => bd_inner_self_eq_re (hpos h) x)
  have hYpos : Y.IsPositive := bd_isPositive_of_real fun x =>
    ⟨_, integral_nonneg fun h => bd_re_nonneg (hpos h) x, hYre x⟩
  have : Countable (basisSet N K) := basisSet_countable.to_subtype
  have htr : tr Y = ∫⁻ h, tr (Yf h) ∂τ := by
    show ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Y e⟫_ℂ).re
      = ∫⁻ h, ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Yf h e⟫_ℂ).re ∂τ
    rw [lintegral_tsum fun e : basisSet N K =>
      (bd_meas_re hmeas (e : H N K) (e : H N K)).aemeasurable]
    refine tsum_congr fun e => ?_
    rw [hYre, Complex.ofReal_re]
    exact ofReal_integral_eq_lintegral_ofReal (hI _ _).re
      (ae_of_all _ fun h => bd_re_nonneg (hpos h) _)
  exact ⟨Y, ⟨hYpos, htr ▸ hint⟩, htr, hY⟩

omit [CompleteSpace K] in
theorem bd_inner_re_eq {τ : Measure α} {Yf : α → Op N K}
    (hpos : ∀ h, (Yf h).IsPositive) {Y : Op N K}
    (hY : ∀ a b : H N K, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂τ) (x : H N K) :
    ⟪x, Y x⟫_ℂ = ((∫ h, (⟪x, Yf h x⟫_ℂ).re ∂τ : ℝ) : ℂ) := by
  rw [hY, ← integral_complex_ofReal]
  exact integral_congr_ae (ae_of_all _ fun h => bd_inner_self_eq_re (hpos h) x)

theorem bd_ofReal_re_eq {τ : Measure α} {Yf : α → Op N K}
    (hpos : ∀ h, (Yf h).IsPositive)
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hint : ∫⁻ h, tr (Yf h) ∂τ < ∞) {Y : Op N K}
    (hY : ∀ a b : H N K, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂τ) (x : H N K) :
    ENNReal.ofReal (⟪x, Y x⟫_ℂ).re = ∫⁻ h, ENNReal.ofReal (⟪x, Yf h x⟫_ℂ).re ∂τ := by
  rw [bd_inner_re_eq hpos hY x, Complex.ofReal_re]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_inner hpos hmeas hint x x).re
    (ae_of_all _ fun h => bd_re_nonneg (hpos h) x)

/-- A weak integral of positive operators is positive with `tr Y ≤ ∫ tr Y_h` (no separability). -/
theorem bd_weak_pos {τ : Measure α} {Yf : α → Op N K}
    (hpos : ∀ h, (Yf h).IsPositive)
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hint : ∫⁻ h, tr (Yf h) ∂τ < ∞) {Y : Op N K}
    (hY : ∀ a b : H N K, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂τ) :
    Y.IsPositive ∧ tr Y ≤ ∫⁻ h, tr (Yf h) ∂τ := by
  refine ⟨bd_isPositive_of_real fun x =>
    ⟨_, integral_nonneg fun h => bd_re_nonneg (hpos h) x, bd_inner_re_eq hpos hY x⟩, ?_⟩
  show ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Y e⟫_ℂ).re ≤ _
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  calc ∑ e ∈ s, ENNReal.ofReal (⟪(e : H N K), Y e⟫_ℂ).re
      = ∑ e ∈ s, ∫⁻ h, ENNReal.ofReal (⟪(e : H N K), Yf h e⟫_ℂ).re ∂τ :=
        Finset.sum_congr rfl fun e _ => bd_ofReal_re_eq hpos hmeas hint hY _
    _ = ∫⁻ h, ∑ e ∈ s, ENNReal.ofReal (⟪(e : H N K), Yf h e⟫_ℂ).re ∂τ :=
        (lintegral_finsetSum s fun e _ => bd_meas_re hmeas (e : H N K) (e : H N K)).symm
    _ ≤ ∫⁻ h, tr (Yf h) ∂τ := lintegral_mono fun h => by
        show _ ≤ ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Yf h e⟫_ℂ).re
        exact ENNReal.sum_le_tsum s

/-- Lemma lem:m-int(iii) for Kraus maps `Θ(Y) = ∑_k A_k Y A_k†` with `∑_k A_k† A_k ≤ I`: the matrix
elements of `Θ(Y_h)` are integrable and `Θ(∫ Y_h dτ) = ∫ Θ(Y_h) dτ` weakly. The maps `β_x` of norm
`√N` are covered by the contraction `⟨x| ⊗ I` and a factor `N` (`krausMatG_smul`). -/
theorem krausMatG_weakInt {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [CompleteSpace E'] (A : ℕ → H N K →L[ℂ] E')
    (hA : ∀ ψ : H N K, ∑' k, ENNReal.ofReal (‖A k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {τ : Measure α} {Yf : α → Op N K}
    (hpos : ∀ h, (Yf h).IsPositive)
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hint : ∫⁻ h, tr (Yf h) ∂τ < ∞) (Y : Op N K)
    (hY : ∀ a b : H N K, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂τ) (a c : E') :
    Integrable (fun h => krausMatG A (Yf h) a c) τ ∧
      krausMatG A Y a c = ∫ h, krausMatG A (Yf h) a c ∂τ := by
  obtain ⟨hYpos, hYle⟩ := bd_weak_pos hpos hmeas hint hY
  have hYf : trB (hbasis N K) Y < ∞ := by rw [← tr_eq_trB]; exact hYle.trans_lt hint
  have hS : ∀ x : E', ∑' k, ENNReal.ofReal (⟪ContinuousLinearMap.adjoint (A k) x,
      Y (ContinuousLinearMap.adjoint (A k) x)⟫_ℂ).re ≠ ∞ := by
    intro x
    have h := Complex.hasSum_re (krausMatG_hasSum hA hYpos hYf x x)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => bd_re_nonneg hYpos _) h.summable]
    exact ENNReal.ofReal_ne_top
  have hbound : ∀ k, ∫⁻ h, ‖⟪ContinuousLinearMap.adjoint (A k) a,
      Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖ₑ ∂τ ≤
      ENNReal.ofReal (⟪ContinuousLinearMap.adjoint (A k) a,
        Y (ContinuousLinearMap.adjoint (A k) a)⟫_ℂ).re +
      ENNReal.ofReal (⟪ContinuousLinearMap.adjoint (A k) c,
        Y (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ).re := by
    intro k
    rw [bd_ofReal_re_eq hpos hmeas hint hY (ContinuousLinearMap.adjoint (A k) a),
      bd_ofReal_re_eq hpos hmeas hint hY (ContinuousLinearMap.adjoint (A k) c),
      ← lintegral_add_left (bd_meas_re hmeas _ _)]
    exact lintegral_mono fun h => bd_enorm_le_add (hpos h) _ _
  have hsum : ∑' k, ∫⁻ h, ‖⟪ContinuousLinearMap.adjoint (A k) a,
      Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖ₑ ∂τ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.2 ⟨hS a, hS c⟩
  have hsm : ∀ k, AEStronglyMeasurable (fun h => ⟪ContinuousLinearMap.adjoint (A k) a,
      Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) τ :=
    fun k => (hmeas _ _).aestronglyMeasurable
  have heq : ∫ h, krausMatG A (Yf h) a c ∂τ = krausMatG A Y a c := by
    show ∫ h, ∑' k, ⟪ContinuousLinearMap.adjoint (A k) a,
      Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ ∂τ = ∑' k, ⟪ContinuousLinearMap.adjoint (A k) a,
      Y (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ
    rw [MeasureTheory.integral_tsum hsm hsum]
    exact tsum_congr fun k => (hY _ _).symm
  have hm' : ∀ k, Measurable (fun h => ‖⟪ContinuousLinearMap.adjoint (A k) a,
      Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖ₑ) := fun k => (hmeas _ _).enorm
  have hlin : ∫⁻ h, ∑' k, ‖⟪ContinuousLinearMap.adjoint (A k) a,
      Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖ₑ ∂τ ≠ ∞ := by
    rw [lintegral_tsum fun k => (hm' k).aemeasurable]
    exact hsum
  have hae : ∀ᵐ h ∂τ, HasSum (fun k => ⟪ContinuousLinearMap.adjoint (A k) a,
      Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) (krausMatG A (Yf h) a c) := by
    filter_upwards [ae_lt_top (Measurable.ennreal_tsum hm') hlin] with h hh
    exact (Summable.of_enorm hh.ne).hasSum
  have hpm : ∀ n : ℕ, AEStronglyMeasurable (fun h => ∑ k ∈ Finset.range n,
      ⟪ContinuousLinearMap.adjoint (A k) a, Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ) τ :=
    fun n => (Finset.measurable_sum (Finset.range n) fun k _ => hmeas _ _).aestronglyMeasurable
  have hasm : AEStronglyMeasurable (fun h => krausMatG A (Yf h) a c) τ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hpm (hae.mono fun h hh => hh.tendsto_sum_nat)
  refine ⟨⟨hasm, ?_⟩, heq.symm⟩
  show ∫⁻ h, ‖krausMatG A (Yf h) a c‖ₑ ∂τ < ∞
  calc ∫⁻ h, ‖krausMatG A (Yf h) a c‖ₑ ∂τ
      ≤ ∫⁻ h, ∑' k, ‖⟪ContinuousLinearMap.adjoint (A k) a,
        Yf h (ContinuousLinearMap.adjoint (A k) c)⟫_ℂ‖ₑ ∂τ :=
        lintegral_mono fun h => enorm_tsum_le_tsum_enorm
    _ < ∞ := hlin.lt_top

end WeakIntegral

/-! ### Positive operator measures and densities -/

section Densities

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {α : Type} [MeasurableSpace α]

/-- A positive operator measure vanishes on the empty set (paragraph "Operator measures"; countable
additivity with all sets empty). -/
theorem IsPOM.empty {Λ : Set α → Op N K} (hΛ : IsPOM Λ) : Λ ∅ = 0 := by
  have hz : ∀ a b : H N K, ⟪a, Λ ∅ b⟫_ℂ = 0 := by
    intro a b
    have h := hΛ.additive (fun _ => ∅) (fun _ => MeasurableSet.empty) (fun i j _ => by simp) a b
    rw [Set.iUnion_empty] at h
    exact (summable_const_iff _).1 h.summable
  ext1 b
  refine ext_inner_left ℂ fun a => ?_
  rw [hz]
  simp

/-- The two-set sequence `E, F, ∅, ∅, …` (helper for finite additivity). -/
def bdSeq2 (E F : Set α) (n : ℕ) : Set α :=
  if n = 0 then E else if n = 1 then F else ∅

theorem bd_union {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {E F : Set α} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (hEF : Disjoint E F) : Λ (E ∪ F) = Λ E + Λ F := by
  have hm : ∀ n, MeasurableSet (bdSeq2 E F n) := by
    intro n; unfold bdSeq2; split_ifs <;> simp [hE, hF]
  have hd : Pairwise (fun i j => Disjoint (bdSeq2 E F i) (bdSeq2 E F j)) := by
    intro i j hij
    unfold bdSeq2
    split_ifs <;> subst_vars <;> simp_all [hEF.symm]
  have hU : (⋃ n, bdSeq2 E F n) = E ∪ F := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union, bdSeq2]
    constructor
    · rintro ⟨n, hn⟩
      split_ifs at hn <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  ext1 b
  refine ext_inner_left ℂ fun a => ?_
  have h := hΛ.additive (bdSeq2 E F) hm hd a b
  rw [hU] at h
  have h0 : Λ ∅ = 0 := hΛ.empty
  have hs : HasSum (fun n => ⟪a, Λ (bdSeq2 E F n) b⟫_ℂ)
      (∑ n ∈ Finset.range 2, ⟪a, Λ (bdSeq2 E F n) b⟫_ℂ) := hasSum_sum_of_ne_finset_zero (by
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have h1 : n ≠ 0 := by omega
      have h2 : n ≠ 1 := by omega
      simp [bdSeq2, h1, h2, h0])
  have e : ∑ n ∈ Finset.range 2, ⟪a, Λ (bdSeq2 E F n) b⟫_ℂ = ⟪a, Λ E b⟫_ℂ + ⟪a, Λ F b⟫_ℂ := by
    simp [Finset.sum_range_succ, bdSeq2]
  rw [e] at hs
  rw [h.unique hs, add_apply, inner_add_right]

/-- `E ⊆ E'` implies `Λ(E) ≤ Λ(E')` (paragraph "Operator measures"). -/
theorem IsPOM.mono {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {E E' : Set α} (hE : MeasurableSet E)
    (hE' : MeasurableSet E') (hsub : E ⊆ E') : (Λ E' - Λ E).IsPositive := by
  have hD : MeasurableSet (E' \ E) := hE'.diff hE
  have hu := bd_union hΛ hE hD Set.disjoint_sdiff_right
  rw [Set.union_sdiff_cancel hsub] at hu
  rw [hu, add_sub_cancel_left]
  exact hΛ.pos _ hD

/-- Finite additivity, `Λ(E ∪ F) = Λ(E) + Λ(F)` for disjoint measurable `E, F` (paragraph "Operator
measures"). -/
theorem IsPOM.union {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {E F : Set α} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (hEF : Disjoint E F) : Λ (E ∪ F) = Λ E + Λ F := by
  exact bd_union hΛ hE hF hEF

/-- The scalar measure `E ↦ re ⟪v, Λ(E) v⟫`. -/
def bdScalarMeas {Λ : Set α → Op N K} (hΛ : IsPOM Λ) (v : H N K) : Measure α :=
  Measure.ofMeasurable (fun E _ => ENNReal.ofReal (⟪v, Λ E v⟫_ℂ).re) (by simp [hΛ.empty])
    (fun f hf hd => by
      have h := Complex.hasSum_re (hΛ.additive f hf hd v v)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => bd_re_nonneg (hΛ.pos _ (hf n)) v) h.summable,
        h.tsum_eq])

theorem bdScalarMeas_apply {Λ : Set α → Op N K} (hΛ : IsPOM Λ) (v : H N K) {E : Set α}
    (hE : MeasurableSet E) : bdScalarMeas hΛ v E = ENNReal.ofReal (⟪v, Λ E v⟫_ℂ).re :=
  Measure.ofMeasurable_apply E hE

instance bdScalarMeas_finite {Λ : Set α → Op N K} (hΛ : IsPOM Λ) (v : H N K) :
    IsFiniteMeasure (bdScalarMeas hΛ v) :=
  ⟨by rw [bdScalarMeas_apply hΛ v MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩

/-- The trace measure `E ↦ tr Λ(E)`, as a sum of scalar measures over the basis. -/
def bdTrMeas {Λ : Set α → Op N K} (hΛ : IsPOM Λ) : Measure α :=
  Measure.sum (fun e : basisSet N K => bdScalarMeas hΛ (e : H N K))

theorem bdTrMeas_apply {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {E : Set α} (hE : MeasurableSet E) :
    bdTrMeas hΛ E = tr (Λ E) := by
  rw [bdTrMeas, Measure.sum_apply _ hE]
  show _ = ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Λ E e⟫_ℂ).re
  exact tsum_congr fun e => bdScalarMeas_apply hΛ _ hE

instance bdTrMeas_finite {Λ : Set α → Op N K} (hΛ : IsPOM Λ) : IsFiniteMeasure (bdTrMeas hΛ) :=
  ⟨by rw [bdTrMeas_apply hΛ MeasurableSet.univ]; exact hΛ.trace_lt_top _ MeasurableSet.univ⟩

/-- `E ↦ tr Λ(E)` is a finite measure (paragraph "Operator measures": "exchange two sums of nonnegative
terms"). -/
theorem IsPOM.exists_traceMeasure {Λ : Set α → Op N K} (hΛ : IsPOM Λ) :
    ∃ μ : Measure α, IsFiniteMeasure μ ∧ ∀ E, MeasurableSet E → μ E = tr (Λ E) := by
  exact ⟨bdTrMeas hΛ, inferInstance, fun E hE => bdTrMeas_apply hΛ hE⟩

/-! #### Helpers for `exists_density` -/

theorem bd_good_set {μ : Measure α} {p : α → Prop} (hp : ∀ᵐ h ∂μ, p h) :
    ∃ M : Set α, MeasurableSet M ∧ (∀ᵐ h ∂μ, h ∈ M) ∧ ∀ h ∈ M, p h := by
  refine ⟨(toMeasurable μ {h | ¬p h})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · exact compl_mem_ae_iff.2 ((measure_toMeasurable _).trans (ae_iff.1 hp))
  · intro h hh
    by_contra hn
    exact hh (subset_toMeasurable _ _ hn)

theorem bd_orth : Orthonormal ℂ (fun i : basisSet N K => (i : H N K)) := by
  have h := (hbasis N K).orthonormal
  rwa [hb_coe] at h

theorem bd_bessel (x : H N K) :
    ∑' i : basisSet N K, ENNReal.ofReal (‖⟪(i : H N K), x⟫_ℂ‖ ^ 2) ≤ ENNReal.ofReal (‖x‖ ^ 2) := by
  have hob : Orthonormal ℂ (fun i : basisSet N K => (i : H N K)) := bd_orth
  have hs : Summable fun i : basisSet N K => ‖⟪(i : H N K), x⟫_ℂ‖ ^ 2 :=
    hob.inner_products_summable x
  have hl : ∑' i : basisSet N K, ‖⟪(i : H N K), x⟫_ℂ‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    hob.tsum_inner_products_le x
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs]
  exact ENNReal.ofReal_le_ofReal hl

theorem bd_tsum_prod_mul {ι : Type*} (u v : ι → ℝ≥0∞) :
    ∑' p : ι × ι, u p.1 * v p.2 = (∑' i, u i) * ∑' j, v j := by
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
  refine tsum_congr fun i => ?_
  exact (ENNReal.tsum_mul_left : ∑' j, u i * v j = u i * ∑' j, v j)

/-- Terms of the series `∑_{i,j} ⟪a, e_i⟫ g(i,j) ⟪e_j, b⟫`. -/
def bdT (g : basisSet N K × basisSet N K → ℂ) (a b : H N K) (p : basisSet N K × basisSet N K) :
    ℂ :=
  ⟪a, (p.1 : H N K)⟫_ℂ * g p * ⟪(p.2 : H N K), b⟫_ℂ

/-- The sesquilinear form with matrix `g` in the basis. -/
def bdQ (g : basisSet N K × basisSet N K → ℂ) (a b : H N K) : ℂ :=
  ∑' p, bdT g a b p

theorem bdQ_enorm_le (g : basisSet N K × basisSet N K → ℂ)
    (hcs : ∀ i j : basisSet N K, ‖g (i, j)‖ ^ 2 ≤ (g (i, i)).re * (g (j, j)).re)
    (hd0 : ∀ i, 0 ≤ (g (i, i)).re)
    (hd1 : ∑' i, ENNReal.ofReal (g (i, i)).re ≤ 1) (a b : H N K) :
    ∑' p, ‖bdT g a b p‖ₑ ≤ ENNReal.ofReal (‖a‖ ^ 2) + ENNReal.ofReal (‖b‖ ^ 2) := by
  have hterm : ∀ i j : basisSet N K, ‖bdT g a b (i, j)‖ₑ ≤
      ENNReal.ofReal (‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2) * ENNReal.ofReal (g (j, j)).re
      + ENNReal.ofReal (g (i, i)).re * ENNReal.ofReal (‖⟪(j : H N K), b⟫_ℂ‖ ^ 2) := by
    intro i j
    have hX : 0 ≤ ‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2 * (g (j, j)).re := mul_nonneg (by positivity) (hd0 j)
    have hY : 0 ≤ (g (i, i)).re * ‖⟪(j : H N K), b⟫_ℂ‖ ^ 2 := mul_nonneg (hd0 i) (by positivity)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (hd0 i),
      ← ENNReal.ofReal_add hX hY, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal (bd_le_add_of_sq_le (norm_nonneg _) hX hY ?_)
    have e : ‖bdT g a b (i, j)‖ = ‖⟪a, (i : H N K)⟫_ℂ‖ * ‖g (i, j)‖ * ‖⟪(j : H N K), b⟫_ℂ‖ := by
      simp only [bdT, norm_mul]
    rw [e]
    have h1 := hcs i j
    calc (‖⟪a, (i : H N K)⟫_ℂ‖ * ‖g (i, j)‖ * ‖⟪(j : H N K), b⟫_ℂ‖) ^ 2
        = ‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2 * ‖g (i, j)‖ ^ 2 * ‖⟪(j : H N K), b⟫_ℂ‖ ^ 2 := by ring
      _ ≤ ‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2 * ((g (i, i)).re * (g (j, j)).re)
          * ‖⟪(j : H N K), b⟫_ℂ‖ ^ 2 := by gcongr
      _ = _ := by ring
  have hA : ∑' i : basisSet N K, ENNReal.ofReal (‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2)
      ≤ ENNReal.ofReal (‖a‖ ^ 2) := by
    calc ∑' i : basisSet N K, ENNReal.ofReal (‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2)
        = ∑' i : basisSet N K, ENNReal.ofReal (‖⟪(i : H N K), a⟫_ℂ‖ ^ 2) :=
          tsum_congr fun i => by rw [norm_inner_symm]
      _ ≤ _ := bd_bessel a
  have hB := bd_bessel b
  calc ∑' p, ‖bdT g a b p‖ₑ
      ≤ ∑' p : basisSet N K × basisSet N K,
          (ENNReal.ofReal (‖⟪a, (p.1 : H N K)⟫_ℂ‖ ^ 2) * ENNReal.ofReal (g (p.2, p.2)).re
          + ENNReal.ofReal (g (p.1, p.1)).re * ENNReal.ofReal (‖⟪(p.2 : H N K), b⟫_ℂ‖ ^ 2)) :=
        ENNReal.tsum_le_tsum fun p => hterm p.1 p.2
    _ = (∑' i : basisSet N K, ENNReal.ofReal (‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2))
            * (∑' j : basisSet N K, ENNReal.ofReal (g (j, j)).re)
          + (∑' i : basisSet N K, ENNReal.ofReal (g (i, i)).re)
            * (∑' j : basisSet N K, ENNReal.ofReal (‖⟪(j : H N K), b⟫_ℂ‖ ^ 2)) := by
        rw [ENNReal.tsum_add]
        congr 1
        · exact bd_tsum_prod_mul
            (fun i : basisSet N K => ENNReal.ofReal (‖⟪a, (i : H N K)⟫_ℂ‖ ^ 2))
            (fun j : basisSet N K => ENNReal.ofReal (g (j, j)).re)
        · exact bd_tsum_prod_mul (fun i : basisSet N K => ENNReal.ofReal (g (i, i)).re)
            (fun j : basisSet N K => ENNReal.ofReal (‖⟪(j : H N K), b⟫_ℂ‖ ^ 2))
    _ ≤ ENNReal.ofReal (‖a‖ ^ 2) * 1 + 1 * ENNReal.ofReal (‖b‖ ^ 2) :=
        add_le_add (mul_le_mul' hA hd1) (mul_le_mul' hd1 hB)
    _ = _ := by rw [mul_one, one_mul]

theorem bdQ_summable (g : basisSet N K × basisSet N K → ℂ)
    (hcs : ∀ i j : basisSet N K, ‖g (i, j)‖ ^ 2 ≤ (g (i, i)).re * (g (j, j)).re)
    (hd0 : ∀ i, 0 ≤ (g (i, i)).re)
    (hd1 : ∑' i, ENNReal.ofReal (g (i, i)).re ≤ 1) (a b : H N K) :
    Summable (bdT g a b) :=
  Summable.of_enorm (ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
    (bdQ_enorm_le g hcs hd0 hd1 a b))

theorem bdQ_norm_le (g : basisSet N K × basisSet N K → ℂ)
    (hcs : ∀ i j : basisSet N K, ‖g (i, j)‖ ^ 2 ≤ (g (i, i)).re * (g (j, j)).re)
    (hd0 : ∀ i, 0 ≤ (g (i, i)).re)
    (hd1 : ∑' i, ENNReal.ofReal (g (i, i)).re ≤ 1) (a b : H N K) :
    ‖bdQ g a b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h : ‖bdQ g a b‖ₑ ≤ ENNReal.ofReal (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    show ‖∑' p, bdT g a b p‖ₑ ≤ _
    exact enorm_tsum_le_tsum_enorm.trans (bdQ_enorm_le g hcs hd0 hd1 a b)
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

theorem bdQ_add_left (g : basisSet N K × basisSet N K → ℂ) (hs : ∀ a b, Summable (bdT g a b))
    (a a' b : H N K) : bdQ g (a + a') b = bdQ g a b + bdQ g a' b := by
  unfold bdQ
  rw [← (hs a b).tsum_add (hs a' b)]
  exact tsum_congr fun p => by simp only [bdT, inner_add_left]; ring

theorem bdQ_add_right (g : basisSet N K × basisSet N K → ℂ) (hs : ∀ a b, Summable (bdT g a b))
    (a b b' : H N K) : bdQ g a (b + b') = bdQ g a b + bdQ g a b' := by
  unfold bdQ
  rw [← (hs a b).tsum_add (hs a b')]
  exact tsum_congr fun p => by simp only [bdT, inner_add_right]; ring

theorem bdQ_smul_left (g : basisSet N K × basisSet N K → ℂ) (hs : ∀ a b, Summable (bdT g a b))
    (c : ℂ) (a b : H N K) : bdQ g (c • a) b = starRingEnd ℂ c * bdQ g a b := by
  unfold bdQ
  rw [← (hs a b).tsum_mul_left (starRingEnd ℂ c)]
  exact tsum_congr fun p => by simp only [bdT, inner_smul_left]; ring

theorem bdQ_smul_right (g : basisSet N K × basisSet N K → ℂ) (hs : ∀ a b, Summable (bdT g a b))
    (c : ℂ) (a b : H N K) : bdQ g a (c • b) = c * bdQ g a b := by
  unfold bdQ
  rw [← (hs a b).tsum_mul_left c]
  exact tsum_congr fun p => by simp only [bdT, inner_smul_right]; ring

theorem bdQ_exists_op (g : basisSet N K × basisSet N K → ℂ)
    (hcs : ∀ i j : basisSet N K, ‖g (i, j)‖ ^ 2 ≤ (g (i, i)).re * (g (j, j)).re)
    (hd0 : ∀ i, 0 ≤ (g (i, i)).re)
    (hd1 : ∑' i, ENNReal.ofReal (g (i, i)).re ≤ 1) :
    ∃ T : Op N K, ∀ a b, ⟪a, T b⟫_ℂ = bdQ g a b := by
  have hs : ∀ a b, Summable (bdT g a b) := bdQ_summable g hcs hd0 hd1
  have h2 : ∀ (c : ℂ) a b, bdQ g (c • a) b = starRingEnd ℂ c * bdQ g a b := bdQ_smul_left g hs
  have h4 : ∀ (c : ℂ) a b, bdQ g a (c • b) = c * bdQ g a b := bdQ_smul_right g hs
  exact bd_exists_op (bdQ g) _ (bdQ_add_left g hs) h2 (bdQ_add_right g hs) h4
    (bd_bound_of_sq (bdQ g) h2 h4 1 fun a b => by
      rw [one_mul]; exact bdQ_norm_le g hcs hd0 hd1 a b)

theorem bdQ_basis (g : basisSet N K × basisSet N K → ℂ) (i j : basisSet N K) :
    bdQ g (i : H N K) (j : H N K) = g (i, j) := by
  classical
  have hob : Orthonormal ℂ (fun i : basisSet N K => (i : H N K)) := bd_orth
  have hio : ∀ x y : basisSet N K, ⟪(x : H N K), (y : H N K)⟫_ℂ = if x = y then 1 else 0 :=
    orthonormal_iff_ite.1 hob
  have hval : bdT g (i : H N K) (j : H N K) (i, j) = g (i, j) := by
    have h1 := hio i i
    have h2 := hio j j
    rw [if_pos rfl] at h1 h2
    simp only [bdT]
    rw [h1, h2, one_mul, mul_one]
  have hs : HasSum (bdT g (i : H N K) (j : H N K)) (bdT g (i : H N K) (j : H N K) (i, j)) :=
    hasSum_single (i, j) fun p hp => by
      obtain ⟨p1, p2⟩ := p
      simp only [bdT]
      by_cases h1 : i = p1
      · have h2 : p2 ≠ j := by
          rintro rfl
          exact hp (by rw [h1])
        have h := hio p2 j
        rw [if_neg h2] at h
        rw [h, mul_zero]
      · have h := hio i p1
        rw [if_neg h1] at h
        rw [h, zero_mul, zero_mul]
  rw [hval] at hs
  exact hs.tsum_eq

theorem bd_ac {Λ : Set α → Op N K} (hΛ : IsPOM Λ) (v : H N K) :
    bdScalarMeas hΛ v ≪ bdTrMeas hΛ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro E hE h0
  rw [bdTrMeas_apply hΛ hE, tr_eq_trB] at h0
  rw [bdScalarMeas_apply hΛ v hE]
  have h := ofReal_inner_le_trB (b := hbasis N K) (hΛ.pos E hE) v
  rw [h0, mul_zero] at h
  exact le_antisymm h zero_le

theorem bd_real_dens {Λ : Set α → Op N K} (hΛ : IsPOM Λ) (v : H N K) :
    ∃ f : α → ℝ, Measurable f ∧ Integrable f (bdTrMeas hΛ) ∧
      ∀ E, MeasurableSet E → ∫ h in E, f h ∂(bdTrMeas hΛ) = (⟪v, Λ E v⟫_ℂ).re := by
  refine ⟨fun h => ((bdScalarMeas hΛ v).rnDeriv (bdTrMeas hΛ) h).toReal,
    (Measure.measurable_rnDeriv _ _).ennreal_toReal, Measure.integrable_toReal_rnDeriv,
    fun E hE => ?_⟩
  rw [Measure.setIntegral_toReal_rnDeriv (bd_ac hΛ v) E, measureReal_def,
    bdScalarMeas_apply hΛ v hE, ENNReal.toReal_ofReal (bd_re_nonneg (hΛ.pos E hE) v)]

theorem bd_cplx_dens {Λ : Set α → Op N K} (hΛ : IsPOM Λ) (a b : H N K) :
    ∃ g : α → ℂ, Measurable g ∧ Integrable g (bdTrMeas hΛ) ∧
      ∀ E, MeasurableSet E → ∫ h in E, g h ∂(bdTrMeas hΛ) = ⟪a, Λ E b⟫_ℂ := by
  obtain ⟨f1, hm1, hi1, he1⟩ := bd_real_dens hΛ (a + b)
  obtain ⟨f2, hm2, hi2, he2⟩ := bd_real_dens hΛ (a - b)
  obtain ⟨f3, hm3, hi3, he3⟩ := bd_real_dens hΛ (a + Complex.I • b)
  obtain ⟨f4, hm4, hi4, he4⟩ := bd_real_dens hΛ (a - Complex.I • b)
  refine ⟨fun h => (((f1 h : ℂ) - (f2 h : ℂ)) - Complex.I * ((f3 h : ℂ) - (f4 h : ℂ))) / 4,
    ?_, ?_, ?_⟩
  · exact (((Complex.measurable_ofReal.comp hm1).sub (Complex.measurable_ofReal.comp hm2)).sub
      (((Complex.measurable_ofReal.comp hm3).sub
        (Complex.measurable_ofReal.comp hm4)).const_mul Complex.I)).div_const 4
  · exact (((hi1.ofReal.sub' hi2.ofReal).sub'
      ((hi3.ofReal.sub' hi4.ofReal).const_mul Complex.I))).div_const 4
  · intro E hE
    have J : ∀ f : α → ℝ, Integrable f (bdTrMeas hΛ) →
        Integrable (fun h => (f h : ℂ)) ((bdTrMeas hΛ).restrict E) :=
      fun f hf => hf.ofReal.integrableOn
    have J12 : Integrable (fun h => (f1 h : ℂ) - (f2 h : ℂ)) ((bdTrMeas hΛ).restrict E) :=
      (J f1 hi1).sub' (J f2 hi2)
    have J34 : Integrable (fun h => (f3 h : ℂ) - (f4 h : ℂ)) ((bdTrMeas hΛ).restrict E) :=
      (J f3 hi3).sub' (J f4 hi4)
    have J34' : Integrable (fun h => Complex.I * ((f3 h : ℂ) - (f4 h : ℂ)))
        ((bdTrMeas hΛ).restrict E) := J34.const_mul Complex.I
    rw [integral_div, integral_sub J12 J34', integral_sub (J f1 hi1) (J f2 hi2),
      integral_const_mul, integral_sub (J f3 hi3) (J f4 hi4),
      integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
      integral_complex_ofReal, he1 E hE, he2 E hE, he3 E hE, he4 E hE,
      ← bd_inner_self_eq_re (hΛ.pos E hE), ← bd_inner_self_eq_re (hΛ.pos E hE),
      ← bd_inner_self_eq_re (hΛ.pos E hE), ← bd_inner_self_eq_re (hΛ.pos E hE)]
    exact (bd_polar (Λ E) a b).symm

theorem bd_ae_re_nonneg {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {τ : Measure α} [IsFiniteMeasure τ]
    {u : α → ℂ} (hu : Integrable u τ) (x : H N K)
    (hE : ∀ E, MeasurableSet E → ∫ h in E, u h ∂τ = ⟪x, Λ E x⟫_ℂ) :
    ∀ᵐ h ∂τ, 0 ≤ (u h).re := by
  have h := ae_nonneg_of_forall_setIntegral_nonneg (f := fun h => (u h).re) hu.re
    fun s hs _ => by
      have e : ∫ h in s, (u h).re ∂τ = (⟪x, Λ s x⟫_ℂ).re := by
        rw [← hE s hs]
        exact integral_re hu.integrableOn
      rw [e]
      exact bd_re_nonneg (hΛ.pos s hs) x
  filter_upwards [h] with y hy
  exact hy

theorem bd_ae_im_zero {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {τ : Measure α} [IsFiniteMeasure τ]
    {u : α → ℂ} (hu : Integrable u τ) (x : H N K)
    (hE : ∀ E, MeasurableSet E → ∫ h in E, u h ∂τ = ⟪x, Λ E x⟫_ℂ) :
    ∀ᵐ h ∂τ, (u h).im = 0 := by
  have h := ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := τ) (f := fun h => (u h).im)
    (g := fun _ => (0 : ℝ)) (fun s _ _ => hu.im.integrableOn)
    (fun s _ _ => (integrable_const (0 : ℝ)).integrableOn) fun s hs _ => by
      have e : ∫ h in s, (u h).im ∂τ = (⟪x, Λ s x⟫_ℂ).im := by
        rw [← hE s hs]
        exact integral_im hu.integrableOn
      rw [e, bd_inner_self_eq_re (hΛ.pos s hs) x, Complex.ofReal_im]
      simp
  filter_upwards [h] with y hy
  exact hy

theorem bd_ae_herm {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {τ : Measure α} [IsFiniteMeasure τ]
    {u v : α → ℂ} (hu : Integrable u τ) (hv : Integrable v τ) (hum : Measurable u)
    (x y : H N K)
    (huE : ∀ E, MeasurableSet E → ∫ h in E, u h ∂τ = ⟪x, Λ E y⟫_ℂ)
    (hvE : ∀ E, MeasurableSet E → ∫ h in E, v h ∂τ = ⟪y, Λ E x⟫_ℂ) :
    ∀ᵐ h ∂τ, v h = starRingEnd ℂ (u h) := by
  have hc : Integrable (fun h => starRingEnd ℂ (u h)) τ :=
    hu.norm.mono' (Complex.continuous_conj.measurable.comp hum).aestronglyMeasurable
      (ae_of_all _ fun h => by simp)
  have h := ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hv.integrableOn)
    (fun s _ _ => hc.integrableOn) fun s hs _ => by
      rw [hvE s hs, integral_conj, huE s hs, inner_conj_symm,
        (hΛ.pos s hs).inner_left_eq_inner_right]
  filter_upwards [h] with z hz
  exact hz

theorem bd_ae_form {Λ : Set α → Op N K} (hΛ : IsPOM Λ) {τ : Measure α} [IsFiniteMeasure τ]
    (z : ℂ) {uxx uxy uyx uyy : α → ℂ}
    (hxx : Integrable uxx τ) (hxy : Integrable uxy τ) (hyx : Integrable uyx τ)
    (hyy : Integrable uyy τ) (x y : H N K)
    (hxxE : ∀ E, MeasurableSet E → ∫ h in E, uxx h ∂τ = ⟪x, Λ E x⟫_ℂ)
    (hxyE : ∀ E, MeasurableSet E → ∫ h in E, uxy h ∂τ = ⟪x, Λ E y⟫_ℂ)
    (hyxE : ∀ E, MeasurableSet E → ∫ h in E, uyx h ∂τ = ⟪y, Λ E x⟫_ℂ)
    (hyyE : ∀ E, MeasurableSet E → ∫ h in E, uyy h ∂τ = ⟪y, Λ E y⟫_ℂ) :
    ∀ᵐ h ∂τ, 0 ≤ (starRingEnd ℂ z * z * uxx h + starRingEnd ℂ z * uxy h + z * uyx h
      + uyy h).re := by
  have hall : Integrable (fun h => starRingEnd ℂ z * z * uxx h + starRingEnd ℂ z * uxy h
      + z * uyx h + uyy h) τ :=
    (((hxx.const_mul _).add (hxy.const_mul _)).add (hyx.const_mul _)).add hyy
  refine bd_ae_re_nonneg hΛ hall (z • x + y) fun E hE => ?_
  have iA : Integrable (fun h => starRingEnd ℂ z * z * uxx h) (τ.restrict E) :=
    (hxx.const_mul _).integrableOn
  have iB : Integrable (fun h => starRingEnd ℂ z * uxy h) (τ.restrict E) :=
    (hxy.const_mul _).integrableOn
  have iC : Integrable (fun h => z * uyx h) (τ.restrict E) := (hyx.const_mul _).integrableOn
  have iD : Integrable uyy (τ.restrict E) := hyy.integrableOn
  have iAB : Integrable (fun h => starRingEnd ℂ z * z * uxx h + starRingEnd ℂ z * uxy h)
      (τ.restrict E) := iA.add iB
  have iABC : Integrable (fun h => starRingEnd ℂ z * z * uxx h + starRingEnd ℂ z * uxy h
      + z * uyx h) (τ.restrict E) := iAB.add iC
  rw [integral_add iABC iD, integral_add iAB iC, integral_add iA iB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    hxxE E hE, hxyE E hE, hyxE E hE, hyyE E hE]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  ring

/-- Lemma lem:m-dens, existence: a positive operator measure has a density `(σ, τ)` with
`τ = tr Λ`. `ρ₀` is the fixed density operator used on the null set `Z` of the proof; it exists iff
`H ≠ 0`, and for `H = 0` (where `trace_one` cannot hold) the lemma is vacuous. -/
theorem exists_density [TopologicalSpace.SeparableSpace K] {Λ : Set α → Op N K} (hΛ : IsPOM Λ)
    (ρ₀ : Op N K) (h₀ : ρ₀.IsPositive) (h₀tr : tr ρ₀ = 1) :
    ∃ (τ : Measure α) (σ : α → Op N K), IsDensity Λ τ σ ∧
      ∀ E, MeasurableSet E → τ E = tr (Λ E) := by
  classical
  have : Countable (basisSet N K) := basisSet_countable.to_subtype
  have : SecondCountableTopology K := UniformSpace.secondCountable_of_separable K
  -- scalar densities of the matrix entries `E ↦ ⟪e_i, Λ(E) e_j⟫`
  choose s hsm hsi hsE using fun p : basisSet N K × basisSet N K =>
    bd_cplx_dens hΛ (p.1 : H N K) (p.2 : H N K)
  -- the countably many algebraic identities, almost everywhere
  have hherm : ∀ p : basisSet N K × basisSet N K,
      ∀ᵐ h ∂(bdTrMeas hΛ), s (p.2, p.1) h = starRingEnd ℂ (s p h) := fun p =>
    bd_ae_herm hΛ (hsi p) (hsi (p.2, p.1)) (hsm p) _ _ (hsE p) (hsE (p.2, p.1))
  have hdiag : ∀ i : basisSet N K, ∀ᵐ h ∂(bdTrMeas hΛ), 0 ≤ (s (i, i) h).re := fun i =>
    bd_ae_re_nonneg hΛ (hsi (i, i)) _ (hsE (i, i))
  have hform : ∀ q : (basisSet N K × basisSet N K) × ℕ, ∀ᵐ h ∂(bdTrMeas hΛ),
      0 ≤ (starRingEnd ℂ (TopologicalSpace.denseSeq ℂ q.2) * TopologicalSpace.denseSeq ℂ q.2
        * s (q.1.1, q.1.1) h + starRingEnd ℂ (TopologicalSpace.denseSeq ℂ q.2) * s (q.1.1, q.1.2) h
        + TopologicalSpace.denseSeq ℂ q.2 * s (q.1.2, q.1.1) h + s (q.1.2, q.1.2) h).re := fun q =>
    bd_ae_form hΛ (TopologicalSpace.denseSeq ℂ q.2) (hsi (q.1.1, q.1.1)) (hsi (q.1.1, q.1.2))
      (hsi (q.1.2, q.1.1)) (hsi (q.1.2, q.1.2)) (q.1.1 : H N K) (q.1.2 : H N K)
      (hsE (q.1.1, q.1.1)) (hsE (q.1.1, q.1.2)) (hsE (q.1.2, q.1.1)) (hsE (q.1.2, q.1.2))
  have hdm : ∀ i : basisSet N K, Measurable fun h => ENNReal.ofReal (s (i, i) h).re :=
    fun i => ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp (hsm (i, i)))
  have htr_ae : ∀ᵐ h ∂(bdTrMeas hΛ), ∑' i : basisSet N K, ENNReal.ofReal (s (i, i) h).re = 1 := by
    have h := ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := bdTrMeas hΛ)
      (f := fun h => ∑' i : basisSet N K, ENNReal.ofReal (s (i, i) h).re)
      (g := fun _ => (1 : ℝ≥0∞)) (Measurable.ennreal_tsum hdm) measurable_const
      fun E hE _ => by
        rw [lintegral_tsum fun i : basisSet N K => (hdm i).aemeasurable, setLIntegral_const,
          one_mul, bdTrMeas_apply hΛ hE]
        show _ = ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), Λ E e⟫_ℂ).re
        refine tsum_congr fun i => ?_
        have hnn : ∀ᵐ h ∂((bdTrMeas hΛ).restrict E), 0 ≤ (s (i, i) h).re :=
          ae_restrict_of_ae (hdiag i)
        have hir : Integrable (fun h => (s (i, i) h).re) ((bdTrMeas hΛ).restrict E) :=
          (hsi (i, i)).integrableOn.re
        rw [← ofReal_integral_eq_lintegral_ofReal hir hnn]
        congr 1
        have e : ∫ h in E, (s (i, i) h).re ∂(bdTrMeas hΛ)
            = (∫ h in E, s (i, i) h ∂(bdTrMeas hΛ)).re :=
          integral_re (hsi (i, i)).integrableOn
        rw [e, hsE (i, i) E hE]
    filter_upwards [h] with y hy
    exact hy
  obtain ⟨M1, hM1m, hM1ae, hM1⟩ := bd_good_set ((ae_all_iff.2 hherm).and
    ((ae_all_iff.2 hdiag).and ((ae_all_iff.2 hform).and htr_ae)))
  have hd0 : ∀ h ∈ M1, ∀ i : basisSet N K, 0 ≤ (s (i, i) h).re := fun h hh => (hM1 h hh).2.1
  have hd1' : ∀ h ∈ M1, ∑' i : basisSet N K, ENNReal.ofReal (s (i, i) h).re = 1 :=
    fun h hh => (hM1 h hh).2.2.2
  have hcs : ∀ h ∈ M1, ∀ i j : basisSet N K,
      ‖s (i, j) h‖ ^ 2 ≤ (s (i, i) h).re * (s (j, j) h).re := by
    intro h hh i j
    obtain ⟨hH, hD, hF, -⟩ := hM1 h hh
    exact bd_cs_of_forms (s (i, i) h) (s (i, j) h) (s (j, i) h) (s (j, j) h) (hH (i, j)) (hD i)
      (hD j) (bd_forms_all (s (i, i) h) (s (i, j) h) (s (j, i) h) (s (j, j) h)
        fun n => hF ((i, j), n))
  -- the operator off the null set
  have hT : ∀ h, ∃ T : Op N K, h ∈ M1 → ∀ a b, ⟪a, T b⟫_ℂ = bdQ (fun p => s p h) a b := by
    intro h
    by_cases hh : h ∈ M1
    · obtain ⟨T, hT⟩ := bdQ_exists_op (fun p => s p h) (hcs h hh) (hd0 h hh) (hd1' h hh).le
      exact ⟨T, fun _ => hT⟩
    · exact ⟨0, fun h' => absurd h' hh⟩
  choose T hTQ using hT
  obtain ⟨σ1, hσ1⟩ : ∃ σ1 : α → Op N K, ∀ h, σ1 h = if h ∈ M1 then T h else 0 :=
    ⟨_, fun h => rfl⟩
  have hQ1 : ∀ h a b, ⟪a, σ1 h b⟫_ℂ = if h ∈ M1 then bdQ (fun p => s p h) a b else 0 := by
    intro h a b
    rw [hσ1]
    split_ifs with hh
    · exact hTQ h hh a b
    · simp
  have hmeasQ : ∀ a b : H N K, Measurable fun h => ⟪a, σ1 h b⟫_ℂ := by
    intro a b
    have e : (fun h => ⟪a, σ1 h b⟫_ℂ) = fun h => if h ∈ M1 then bdQ (fun p => s p h) a b else 0 :=
      funext fun h => hQ1 h a b
    rw [e]
    refine measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (t : Finset (basisSet N K × basisSet N K)) h =>
        if h ∈ M1 then ∑ p ∈ t, bdT (fun p => s p h) a b p else 0) (fun t => ?_) ?_
    · show Measurable fun h => if h ∈ M1 then ∑ p ∈ t, bdT (fun p => s p h) a b p else 0
      refine Measurable.ite hM1m ?_ measurable_const
      show Measurable fun h => ∑ p ∈ t, ⟪a, (p.1 : H N K)⟫_ℂ * s p h * ⟪(p.2 : H N K), b⟫_ℂ
      exact Finset.measurable_sum t fun p _ => ((hsm p).const_mul _).mul_const _
    · refine tendsto_pi_nhds.2 fun h => ?_
      by_cases hh : h ∈ M1
      · simp only [if_pos hh]
        exact (bdQ_summable (fun p => s p h) (hcs h hh) (hd0 h hh) (hd1' h hh).le a b).hasSum
      · simp only [if_neg hh]
        exact tendsto_const_nhds
  have hbd1 : ∀ h a b, ‖⟪a, σ1 h b⟫_ℂ‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    intro h a b
    rw [hQ1]
    split_ifs with hh
    · exact bdQ_norm_le _ (hcs h hh) (hd0 h hh) (hd1' h hh).le a b
    · rw [norm_zero]; positivity
  have hI1 : ∀ a b : H N K, Integrable (fun h => ⟪a, σ1 h b⟫_ℂ) (bdTrMeas hΛ) := fun a b =>
    Integrable.of_bound (hmeasQ a b).aestronglyMeasurable _ (ae_of_all _ fun h => hbd1 h a b)
  -- the representation identity, first for basis vectors, then for all vectors
  have repr1 : ∀ E, MeasurableSet E → ∀ a b : H N K,
      ∫ h in E, ⟪a, σ1 h b⟫_ℂ ∂(bdTrMeas hΛ) = ⟪a, Λ E b⟫_ℂ := by
    intro E hE
    obtain ⟨L, hL⟩ : ∃ L : H N K → H N K → ℂ, ∀ a b,
        L a b = ∫ h in E, ⟪a, σ1 h b⟫_ℂ ∂(bdTrMeas hΛ) := ⟨_, fun a b => rfl⟩
    have h1 : ∀ a a' b, L (a + a') b = L a b + L a' b := by
      intro a a' b
      simp only [hL, inner_add_left]
      exact integral_add (hI1 a b).integrableOn (hI1 a' b).integrableOn
    have h2 : ∀ (c : ℂ) a b, L (c • a) b = starRingEnd ℂ c * L a b := by
      intro c a b
      simp only [hL, inner_smul_left]
      exact integral_const_mul _ _
    have h3 : ∀ a b b', L a (b + b') = L a b + L a b' := by
      intro a b b'
      simp only [hL, map_add, inner_add_right]
      exact integral_add (hI1 a b).integrableOn (hI1 a b').integrableOn
    have h4 : ∀ (c : ℂ) a b, L a (c • b) = c * L a b := by
      intro c a b
      simp only [hL, map_smul, inner_smul_right]
      exact integral_const_mul _ _
    have hb : ∀ a b, ‖L a b‖ ≤ ((bdTrMeas hΛ).restrict E).real Set.univ * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
      intro a b
      rw [hL]
      exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun h => hbd1 h a b)).trans_eq
        (mul_comm _ _)
    obtain ⟨Y, hY⟩ := bd_exists_op L _ h1 h2 h3 h4 (bd_bound_of_sq L h2 h4 _ hb)
    have hYE : Y = Λ E := by
      refine bd_op_ext (hbasis N K) fun i j => ?_
      rw [hb_coe]
      show ⟪(i : H N K), Y (j : H N K)⟫_ℂ = ⟪(i : H N K), Λ E (j : H N K)⟫_ℂ
      rw [hY, hL]
      have hae : ∀ᵐ h ∂(bdTrMeas hΛ), ⟪(i : H N K), σ1 h (j : H N K)⟫_ℂ = s (i, j) h := by
        filter_upwards [hM1ae] with h hh
        rw [hQ1, if_pos hh, bdQ_basis]
      rw [integral_congr_ae (ae_restrict_of_ae hae)]
      exact hsE (i, j) E hE
    intro a b
    rw [← hYE, hY, hL]
  -- positivity off a second null set
  have hposae : ∀ n : ℕ, ∀ᵐ h ∂(bdTrMeas hΛ),
      0 ≤ (⟪TopologicalSpace.denseSeq (H N K) n,
        σ1 h (TopologicalSpace.denseSeq (H N K) n)⟫_ℂ).re ∧
      (⟪TopologicalSpace.denseSeq (H N K) n,
        σ1 h (TopologicalSpace.denseSeq (H N K) n)⟫_ℂ).im = 0 := by
    intro n
    have hv := hI1 (TopologicalSpace.denseSeq (H N K) n) (TopologicalSpace.denseSeq (H N K) n)
    have hvE := fun (E : Set α) (hE : MeasurableSet E) => repr1 E hE
      (TopologicalSpace.denseSeq (H N K) n) (TopologicalSpace.denseSeq (H N K) n)
    exact (bd_ae_re_nonneg hΛ hv _ hvE).and (bd_ae_im_zero hΛ hv _ hvE)
  obtain ⟨M2, hM2m, hM2ae, hM2⟩ := bd_good_set (hM1ae.and (ae_all_iff.2 hposae))
  have hpos2 : ∀ h ∈ M2, (σ1 h).IsPositive := by
    intro h hh
    obtain ⟨-, hn⟩ := hM2 h hh
    refine bd_isPositive_of_real fun x => ⟨(⟪x, σ1 h x⟫_ℂ).re, ?_, ?_⟩
    · exact isClosed_property (TopologicalSpace.denseRange_denseSeq (H N K))
        (isClosed_le continuous_const
          (Complex.continuous_re.comp (continuous_id.inner (σ1 h).continuous)))
        (fun n => (hn n).1) x
    · have him : (⟪x, σ1 h x⟫_ℂ).im = 0 :=
        isClosed_property (TopologicalSpace.denseRange_denseSeq (H N K))
          (isClosed_eq (Complex.continuous_im.comp (continuous_id.inner (σ1 h).continuous))
            continuous_const) (fun n => (hn n).2) x
      exact Complex.ext (by simp) (by simp [him])
  have htr1 : ∀ h ∈ M1, tr (σ1 h) = 1 := by
    intro h hh
    show ∑' e : basisSet N K, ENNReal.ofReal (⟪(e : H N K), σ1 h e⟫_ℂ).re = 1
    have e : ∀ i : basisSet N K, ENNReal.ofReal (⟪(i : H N K), σ1 h i⟫_ℂ).re
        = ENNReal.ofReal (s (i, i) h).re := by
      intro i
      rw [hQ1, if_pos hh, bdQ_basis]
    rw [tsum_congr e]
    exact hd1' h hh
  -- the density: `σ1` off the null set, `ρ₀` on it
  obtain ⟨σ, hσ⟩ : ∃ σ : α → Op N K, ∀ h, σ h = if h ∈ M2 then σ1 h else ρ₀ :=
    ⟨_, fun h => rfl⟩
  refine ⟨bdTrMeas hΛ, σ, ⟨inferInstance, fun h => ?_, fun h => ?_, fun a b => ?_,
    fun E hE a b => ?_⟩, fun E hE => bdTrMeas_apply hΛ hE⟩
  · rw [hσ]
    split_ifs with hh
    · exact hpos2 h hh
    · exact h₀
  · rw [hσ]
    split_ifs with hh
    · exact htr1 h (hM2 h hh).1
    · exact h₀tr
  · have e : (fun h => ⟪a, σ h b⟫_ℂ) = fun h => if h ∈ M2 then ⟪a, σ1 h b⟫_ℂ else ⟪a, ρ₀ b⟫_ℂ := by
      funext h
      rw [hσ]
      split_ifs <;> rfl
    rw [e]
    exact Measurable.ite hM2m (hmeasQ a b) measurable_const
  · rw [← repr1 E hE a b]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hM2ae] with h hh
    rw [hσ, if_pos hh]

/-- The measure of a density is the trace measure, `τ = tr Λ` on measurable sets (Lemma lem:m-dens and
the docstring of `IsHistory`: "`IsDensity` forces `τ = tr ρ^{(M)}` on measurable sets"). -/
theorem IsDensity.apply_eq_tr [TopologicalSpace.SeparableSpace K] {Λ : Set α → Op N K}
    {τ : Measure α} {σ : α → Op N K} (hd : IsDensity Λ τ σ) {E : Set α} (hE : MeasurableSet E) :
    τ E = tr (Λ E) := by
  have := hd.finite
  have hconst : ∀ F : Set α, ∫⁻ h, tr (σ h) ∂(τ.restrict F) = τ F := by
    intro F
    simp_rw [hd.trace_one]
    rw [lintegral_const, one_mul, Measure.restrict_apply_univ]
  have hint : ∫⁻ h, tr (σ h) ∂(τ.restrict E) < ∞ := by
    rw [hconst]; exact measure_lt_top τ E
  obtain ⟨Y, -, hYtr, hYm⟩ := exists_weakInt (τ := τ.restrict E) hd.pos hd.meas hint
  have hYE : Y = Λ E := by
    ext1 b
    refine ext_inner_left ℂ fun a => ?_
    rw [hYm, hd.repr E hE]
  rw [← hYE, hYtr, hconst]

/-- Lemma lem:m-dens, uniqueness: two densities `ξ, ξ'` of the same operator measure with respect to
one finite measure `ν` agree `ν`-almost everywhere. -/
theorem density_ae_eq [TopologicalSpace.SeparableSpace K] (ν : Measure α) [IsFiniteMeasure ν]
    (ξ ξ' : α → Op N K) (hξ : ∀ h, (ξ h).IsPositive) (hξ' : ∀ h, (ξ' h).IsPositive)
    (hmξ : ∀ a b : H N K, Measurable (fun h => ⟪a, ξ h b⟫_ℂ))
    (hmξ' : ∀ a b : H N K, Measurable (fun h => ⟪a, ξ' h b⟫_ℂ))
    (hiξ : ∫⁻ h, tr (ξ h) ∂ν < ∞) (hiξ' : ∫⁻ h, tr (ξ' h) ∂ν < ∞)
    (hEq : ∀ E, MeasurableSet E → ∀ a b : H N K,
      ∫ h in E, ⟪a, ξ h b⟫_ℂ ∂ν = ∫ h in E, ⟪a, ξ' h b⟫_ℂ ∂ν) :
    ∀ᵐ h ∂ν, ξ h = ξ' h := by
  have : Countable (basisSet N K) := basisSet_countable.to_subtype
  have hij : ∀ p : basisSet N K × basisSet N K,
      ∀ᵐ h ∂ν, ⟪(p.1 : H N K), ξ h p.2⟫_ℂ = ⟪(p.1 : H N K), ξ' h p.2⟫_ℂ := by
    intro p
    exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => (integrable_inner hξ hmξ hiξ _ _).integrableOn)
      (fun s _ _ => (integrable_inner hξ' hmξ' hiξ' _ _).integrableOn)
      (fun s hs _ => hEq s hs _ _)
  filter_upwards [ae_all_iff.2 hij] with h hh
  refine bd_op_ext (hbasis N K) fun i j => ?_
  rw [hb_coe]
  exact hh (i, j)

end Densities

end

end TheoremS.Meas
