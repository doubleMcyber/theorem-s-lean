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
The potential `V(C, W) = W g(C/W)` and the facts about it that the proof of Theorem S uses.

Pure real analysis, Mathlib only. The proofs are copied without change from the repository
doubleMcyber/quantum-specs (commit cbfdb57, `LowerBounds/Grover/FullPotential.lean` lines 40 to 300 and
`FullQuery.lean` lines 38 to the end; Apache-2.0), with the specification-dependent `Vf_measure` dropped
and the namespace changed. `Vf_finset_sum` (subadditivity over a Finset) is added at the end.
-/
import Mathlib

open Filter
open scoped ENNReal NNReal

namespace TheoremS

noncomputable def gf (r : ℝ) : ℝ := if r ≤ 1 / 2 then r / 2 else 1 / 4 + Real.arcsin (2 * r - 1) / 4
noncomputable def Vf (C W : ℝ) : ℝ := if W ≤ 0 then 0 else W * gf (C / W)

/-! ### Values of `gf` -/

lemma gf_of_le {r : ℝ} (h : r ≤ 1 / 2) : gf r = r / 2 := by
  unfold gf; rw [if_pos h]

lemma gf_of_gt {r : ℝ} (h : 1 / 2 < r) : gf r = 1 / 4 + Real.arcsin (2 * r - 1) / 4 := by
  unfold gf; rw [if_neg (not_le.2 h)]

lemma gf_of_ge {r : ℝ} (h : 1 / 2 ≤ r) : gf r = 1 / 4 + Real.arcsin (2 * r - 1) / 4 := by
  rcases h.eq_or_lt with h | h
  · subst h
    rw [gf_of_le le_rfl]
    norm_num [Real.arcsin_zero]
  · exact gf_of_gt h

lemma gf_zero : gf 0 = 0 := by
  rw [gf_of_le (by norm_num)]; norm_num

theorem gf_one : gf 1 = Real.pi / 8 + 1 / 4 := by
  have h : (2 : ℝ) * 1 - 1 = 1 := by norm_num
  rw [gf_of_gt (by norm_num), h, Real.arcsin_one]
  ring

/-! ### Supporting lines -/

lemma sin_tangent {a a0 : ℝ} (ha : a ∈ Set.Icc 0 Real.pi) (ha0 : a0 ∈ Set.Icc 0 Real.pi) :
    Real.sin a ≤ Real.sin a0 + Real.cos a0 * (a - a0) := by
  have hc : ConvexOn ℝ (Set.Icc 0 Real.pi) (fun x => -Real.sin x) :=
    strictConcaveOn_sin_Icc.concaveOn.neg
  have hd : HasDerivAt (fun x => -Real.sin x) (-Real.cos a0) a0 := (Real.hasDerivAt_sin a0).neg
  rcases lt_trichotomy a a0 with h | h | h
  · have h1 := hc.slope_le_of_hasDerivAt ha ha0 h hd
    rw [slope_def_field] at h1
    beta_reduce at h1
    rw [div_le_iff₀ (by linarith)] at h1
    nlinarith
  · subst h; simp
  · have h1 := hc.le_slope_of_hasDerivAt ha0 ha h hd
    rw [slope_def_field] at h1
    beta_reduce at h1
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith

lemma arcsin_tangent {y0 y : ℝ} (h0 : 0 ≤ y0) (h0' : y0 < 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    y - y0 ≤ Real.sqrt (1 - y0 ^ 2) * (Real.arcsin y - Real.arcsin y0) := by
  have h := sin_tangent (a := Real.arcsin y) (a0 := Real.arcsin y0)
    ⟨Real.arcsin_nonneg.2 hy, by linarith [Real.arcsin_le_pi_div_two y, Real.pi_pos]⟩
    ⟨Real.arcsin_nonneg.2 h0, by linarith [Real.arcsin_le_pi_div_two y0, Real.pi_pos]⟩
  rw [Real.sin_arcsin (by linarith) hy', Real.sin_arcsin (by linarith) h0'.le,
    Real.cos_arcsin] at h
  linarith

/-- the slope of the supporting line at `r0` -/
noncomputable def sg (r0 : ℝ) : ℝ :=
  if r0 ≤ 1 / 2 then 1 / 2 else 1 / (4 * Real.sqrt (r0 * (1 - r0)))

lemma sg_ge (r0 : ℝ) (h1 : r0 < 1) : 1 / 2 ≤ sg r0 := by
  unfold sg
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    have hs : 0 < Real.sqrt (r0 * (1 - r0)) :=
      Real.sqrt_pos.2 (mul_pos (by linarith) (by linarith))
    have hs2 : Real.sqrt (r0 * (1 - r0)) ≤ 1 / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      nlinarith [sq_nonneg (r0 - 1 / 2)]
    rw [le_div_iff₀ (by positivity)]
    linarith

lemma tangent_gf {r0 r : ℝ} (h : 1 / 2 < r0) (h1 : r0 < 1) (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) :
    gf r0 + sg r0 * (r - r0) ≤ gf r := by
  have hs : 0 < Real.sqrt (r0 * (1 - r0)) :=
    Real.sqrt_pos.2 (mul_pos (by linarith) (by linarith))
  have hsg : sg r0 = 1 / (4 * Real.sqrt (r0 * (1 - r0))) := by
    unfold sg; rw [if_neg (not_le.2 h)]
  have hT := arcsin_tangent (y0 := 2 * r0 - 1) (y := 2 * r - 1)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hq : Real.sqrt (1 - (2 * r0 - 1) ^ 2) = 2 * Real.sqrt (r0 * (1 - r0)) := by
    have e : 1 - (2 * r0 - 1) ^ 2 = 2 ^ 2 * (r0 * (1 - r0)) := by ring
    rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hq] at hT
  rw [gf_of_gt h, gf_of_ge hr, hsg]
  have e2 : 1 / (4 * Real.sqrt (r0 * (1 - r0))) * (r - r0)
      = (r - r0) / (4 * Real.sqrt (r0 * (1 - r0))) := by ring
  rw [e2]
  have h2 : (r - r0) / (4 * Real.sqrt (r0 * (1 - r0)))
      ≤ (Real.arcsin (2 * r - 1) - Real.arcsin (2 * r0 - 1)) / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hT]
  linarith

lemma gf_ge_half {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : r / 2 ≤ gf r := by
  by_cases h : r ≤ 1 / 2
  · rw [gf_of_le h]
  · push_neg at h
    have hy : 0 ≤ 2 * r - 1 := by linarith
    have hA := Real.sin_le (Real.arcsin_nonneg.2 hy)
    rw [Real.sin_arcsin (by linarith) (by linarith)] at hA
    rw [gf_of_gt h]
    linarith

lemma gf_support {r0 r : ℝ} (h0 : 0 ≤ r0) (h1 : r0 < 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    gf r0 + sg r0 * (r - r0) ≤ gf r := by
  by_cases hr0 : r0 ≤ 1 / 2
  · have hs : sg r0 = 1 / 2 := by unfold sg; rw [if_pos hr0]
    rw [hs, gf_of_le hr0]
    have := gf_ge_half hr hr1
    linarith
  · push_neg at hr0
    by_cases hh : 1 / 2 ≤ r
    · exact tangent_gf hr0 h1 hh hr1
    · push_neg at hh
      have hT := tangent_gf (r := 1 / 2) hr0 h1 le_rfl (by norm_num)
      rw [gf_of_le (le_refl _)] at hT
      have hsg := sg_ge r0 h1
      rw [gf_of_le hh.le]
      nlinarith [mul_nonneg (sub_nonneg.2 hsg) (sub_nonneg.2 hh.le)]

/-! ### Convexity, monotonicity -/

theorem gf_convexOn : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) gf := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  by_cases hz : a * x + (1 - a) * y < 1
  · have hz0 : 0 ≤ a * x + (1 - a) * y := by nlinarith
    have h1 := gf_support hz0 hz hx0 hx1
    have h2 := gf_support hz0 hz hy0 hy1
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · push_neg at hz
    rcases ha.eq_or_lt with h | h
    · subst h
      have : y = 1 := by nlinarith
      subst this
      simp
    · rcases hb.eq_or_lt with h' | h'
      · have ha1 : a = 1 := by linarith
        subst ha1
        have : x = 1 := by nlinarith
        subst this
        simp
      · have hx' : x = 1 := by nlinarith
        have hy' : y = 1 := by nlinarith
        subst hx'; subst hy'
        apply le_of_eq
        have e : a * 1 + (1 - a) * 1 = 1 := by ring
        rw [e]; ring

theorem gf_monotoneOn : MonotoneOn gf (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  by_cases hy2 : y ≤ 1 / 2
  · rw [gf_of_le hy2, gf_of_le (hxy.trans hy2)]; linarith
  · push_neg at hy2
    have hA : 0 ≤ Real.arcsin (2 * y - 1) := Real.arcsin_nonneg.2 (by linarith)
    rw [gf_of_gt hy2]
    by_cases hx2 : x ≤ 1 / 2
    · rw [gf_of_le hx2]; linarith
    · push_neg at hx2
      rw [gf_of_gt hx2]
      have := Real.arcsin_le_arcsin (show 2 * x - 1 ≤ 2 * y - 1 by linarith)
      linarith

lemma gf_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ gf r := by
  have := gf_monotoneOn ⟨le_rfl, zero_le_one⟩ ⟨h0, h1⟩ h0
  rwa [gf_zero] at this

theorem gf_le_mul (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : gf r ≤ (Real.pi / 8 + 1 / 4) * r := by
  have := gf_convexOn.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    (sub_nonneg.2 h1) h0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, gf_zero, gf_one] at this
  linarith

/-! ### The perspective `Vf` -/

lemma Vf_of_pos {C W : ℝ} (h : 0 < W) : Vf C W = W * gf (C / W) := by
  unfold Vf; rw [if_neg (not_le.2 h)]

lemma Vf_of_nonpos {C W : ℝ} (h : W ≤ 0) : Vf C W = 0 := by
  unfold Vf; rw [if_pos h]

lemma Vf_00 : Vf 0 0 = 0 := Vf_of_nonpos le_rfl

theorem Vf_add (C₁ W₁ C₂ W₂ : ℝ) (h₁ : 0 ≤ C₁) (h₁' : C₁ ≤ W₁) (h₂ : 0 ≤ C₂) (h₂' : C₂ ≤ W₂) :
    Vf (C₁ + C₂) (W₁ + W₂) ≤ Vf C₁ W₁ + Vf C₂ W₂ := by
  have hW1 : 0 ≤ W₁ := h₁.trans h₁'
  have hW2 : 0 ≤ W₂ := h₂.trans h₂'
  rcases hW1.eq_or_lt with e1 | p1
  · subst e1
    have : C₁ = 0 := le_antisymm h₁' h₁
    subst this
    simp [Vf_00]
  · rcases hW2.eq_or_lt with e2 | p2
    · subst e2
      have : C₂ = 0 := le_antisymm h₂' h₂
      subst this
      simp [Vf_00]
    · have hs : 0 < W₁ + W₂ := add_pos p1 p2
      rw [Vf_of_pos hs, Vf_of_pos p1, Vf_of_pos p2]
      have hx : C₁ / W₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg h₁ p1.le, (div_le_one p1).2 h₁'⟩
      have hy : C₂ / W₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg h₂ p2.le, (div_le_one p2).2 h₂'⟩
      have hab : W₁ / (W₁ + W₂) + W₂ / (W₁ + W₂) = 1 := by
        rw [← add_div]; exact div_self hs.ne'
      have key := gf_convexOn.2 hx hy (div_nonneg p1.le hs.le) (div_nonneg p2.le hs.le) hab
      simp only [smul_eq_mul] at key
      have e : W₁ / (W₁ + W₂) * (C₁ / W₁) + W₂ / (W₁ + W₂) * (C₂ / W₂)
          = (C₁ + C₂) / (W₁ + W₂) := by
        field_simp
      rw [e] at key
      have ha : (W₁ + W₂) * (W₁ / (W₁ + W₂)) = W₁ := mul_div_cancel₀ _ hs.ne'
      have hb : (W₁ + W₂) * (W₂ / (W₁ + W₂)) = W₂ := mul_div_cancel₀ _ hs.ne'
      have := mul_le_mul_of_nonneg_left key hs.le
      calc (W₁ + W₂) * gf ((C₁ + C₂) / (W₁ + W₂))
          ≤ (W₁ + W₂) * (W₁ / (W₁ + W₂) * gf (C₁ / W₁) + W₂ / (W₁ + W₂) * gf (C₂ / W₂)) := this
        _ = ((W₁ + W₂) * (W₁ / (W₁ + W₂))) * gf (C₁ / W₁)
            + ((W₁ + W₂) * (W₂ / (W₁ + W₂))) * gf (C₂ / W₂) := by ring
        _ = W₁ * gf (C₁ / W₁) + W₂ * gf (C₂ / W₂) := by rw [ha, hb]

theorem Vf_fin_sum {k : ℕ} (C W : Fin k → ℝ) (h0 : ∀ o, 0 ≤ C o) (h1 : ∀ o, C o ≤ W o) :
    Vf (∑ o, C o) (∑ o, W o) ≤ ∑ o, Vf (C o) (W o) := by
  induction k with
  | zero => simp [Vf_00]
  | succ k ih =>
    simp only [Fin.sum_univ_succ]
    have hih := ih (fun i => C i.succ) (fun i => W i.succ) (fun i => h0 _) (fun i => h1 _)
    have hs0 : 0 ≤ ∑ i : Fin k, C i.succ := Finset.sum_nonneg fun i _ => h0 _
    have hs1 : ∑ i : Fin k, C i.succ ≤ ∑ i : Fin k, W i.succ :=
      Finset.sum_le_sum fun i _ => h1 _
    have := Vf_add (C 0) (W 0) _ _ (h0 0) (h1 0) hs0 hs1
    linarith

theorem Vf_self (W : ℝ) (hW : 0 ≤ W) : Vf W W = (Real.pi / 8 + 1 / 4) * W := by
  rcases hW.eq_or_lt with h | h
  · subst h; simp [Vf_00]
  · rw [Vf_of_pos h, div_self h.ne', gf_one]; ring

theorem Vf_le (C W : ℝ) (hC : 0 ≤ C) (hCW : C ≤ W) : Vf C W ≤ (Real.pi / 8 + 1 / 4) * C := by
  rcases (hC.trans hCW).eq_or_lt with h | h
  · have hC0 : C = 0 := by linarith
    rw [Vf_of_nonpos (by linarith), hC0]; simp
  · rw [Vf_of_pos h]
    have h1 := gf_le_mul (C / W) (div_nonneg hC h.le) ((div_le_one h).2 hCW)
    calc W * gf (C / W) ≤ W * ((Real.pi / 8 + 1 / 4) * (C / W)) :=
          mul_le_mul_of_nonneg_left h1 h.le
      _ = (Real.pi / 8 + 1 / 4) * C := by field_simp

theorem Vf_nonneg (C W : ℝ) (hC : 0 ≤ C) (hCW : C ≤ W) : 0 ≤ Vf C W := by
  by_cases h : W ≤ 0
  · rw [Vf_of_nonpos h]
  · push_neg at h
    rw [Vf_of_pos h]
    exact mul_nonneg h.le (gf_nonneg (div_nonneg hC h.le) ((div_le_one h).2 hCW))

/-! ### `gf ∘ cos²` -/

lemma cos_sq_ge_half {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ Real.pi / 4) : 1 / 2 ≤ Real.cos φ ^ 2 := by
  have h := Real.cos_two_mul φ
  have hc : 0 ≤ Real.cos (2 * φ) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
  linarith

lemma gf_cos_sq_small {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ Real.pi / 4) :
    gf (Real.cos φ ^ 2) = Real.pi / 8 + 1 / 4 - φ / 2 := by
  rw [gf_of_ge (cos_sq_ge_half h0 h1)]
  have e : 2 * Real.cos φ ^ 2 - 1 = Real.sin (Real.pi / 2 - 2 * φ) := by
    rw [Real.sin_pi_div_two_sub, Real.cos_two_mul]
  rw [e, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)]
  ring

lemma gf_cos_sq_large {φ : ℝ} (h0 : Real.pi / 4 ≤ φ) (h1 : φ ≤ Real.pi / 2) :
    gf (Real.cos φ ^ 2) = Real.cos φ ^ 2 / 2 := by
  apply gf_of_le
  have h := Real.cos_two_mul φ
  have hc : Real.cos (2 * φ) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [Real.pi_pos])
  linarith

lemma cos_sq_sub (a b : ℝ) :
    Real.cos a ^ 2 - Real.cos b ^ 2 = Real.sin (b + a) * Real.sin (b - a) := by
  rw [Real.sin_add, Real.sin_sub]
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  linear_combination (-(Real.cos a ^ 2)) * hb + (Real.cos b ^ 2) * ha

lemma gf_cos_sq_lip_large {a b : ℝ} (ha : Real.pi / 4 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    gf (Real.cos a ^ 2) - gf (Real.cos b ^ 2) ≤ (b - a) / 2 := by
  rw [gf_cos_sq_large ha (hab.trans hb), gf_cos_sq_large (ha.trans hab) hb]
  have h1 : 0 ≤ Real.sin (b + a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h2 : 0 ≤ Real.sin (b - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have h3 : Real.sin (b + a) ≤ 1 := Real.sin_le_one _
  have h4 : Real.sin (b - a) ≤ b - a := Real.sin_le (by linarith)
  have h5 := cos_sq_sub a b
  have h6 := mul_le_mul h3 h4 h2 zero_le_one
  linarith

/-- `gf (cos φ ^ 2)` is `1/2`-Lipschitz and nonincreasing in the one-sided form used by the query. -/
lemma gf_cos_sq_lip {φ φ' : ℝ} (h0 : 0 ≤ φ) (h : φ ≤ φ') (h1 : φ' ≤ Real.pi / 2) :
    gf (Real.cos φ ^ 2) - gf (Real.cos φ' ^ 2) ≤ (φ' - φ) / 2 := by
  rcases le_total φ' (Real.pi / 4) with hb | hb
  · rw [gf_cos_sq_small h0 (h.trans hb), gf_cos_sq_small (h0.trans h) hb]
    linarith
  · rcases le_total φ (Real.pi / 4) with ha | ha
    · have s1 := gf_cos_sq_small h0 ha
      have s2 := gf_cos_sq_small (by linarith [Real.pi_pos] : 0 ≤ Real.pi / 4) le_rfl
      have l := gf_cos_sq_lip_large (le_refl (Real.pi / 4)) hb h1
      linarith
    · exact gf_cos_sq_lip_large ha h h1

/-! ### Facts about `β = arcsin (2 / t)` -/

lemma cos_arcsin_le (t : ℝ) (ht : 2 ≤ t) : Real.cos (Real.arcsin (2 / t)) ≤ 1 - 2 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [Real.cos_arcsin]
  have h1 : 0 ≤ 1 - 2 / t ^ 2 := by
    have : 2 / t ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  apply Real.sqrt_le_iff.2 ⟨h1, ?_⟩
  have e : (2 / t) ^ 2 = 2 * (2 / t ^ 2) := by ring
  rw [e]
  nlinarith [sq_nonneg (2 / t ^ 2)]

theorem kappa_pos (t : ℝ) (ht : 2 ≤ t) : 0 < 2 / Real.arcsin (2 / t) := by
  have ht0 : 0 < t := by linarith
  exact div_pos two_pos (Real.arcsin_pos.2 (div_pos two_pos ht0))

/-! ### The query step -/

theorem Vf_query (t C W C' : ℝ) (ht : 2 ≤ t) (hC : 0 ≤ C) (hCW : C ≤ W) (hC' : 0 ≤ C')
    (hC'W : C' ≤ W)
    (h : (1 - 2 / t ^ 2) * Real.sqrt C - 2 / t * Real.sqrt (W - C) ≤ Real.sqrt C') :
    (2 / Real.arcsin (2 / t)) * Vf C W - W ≤ (2 / Real.arcsin (2 / t)) * Vf C' W := by
  have ht0 : 0 < t := by linarith
  have hW0 : 0 ≤ W := hC.trans hCW
  rcases hW0.eq_or_lt with hW | hW
  · subst hW
    have h1 : C = 0 := le_antisymm hCW hC
    have h2 : C' = 0 := le_antisymm hC'W hC'
    subst h1; subst h2
    simp [Vf_00]
  · have h2t : 0 < 2 / t := div_pos two_pos ht0
    obtain ⟨β, hβ⟩ : ∃ β, β = Real.arcsin (2 / t) := ⟨_, rfl⟩
    have hβpos : 0 < β := by rw [hβ]; exact Real.arcsin_pos.2 h2t
    have hβle : β ≤ Real.pi / 2 := by rw [hβ]; exact Real.arcsin_le_pi_div_two _
    have hsinβ : Real.sin β = 2 / t := by
      rw [hβ]; exact Real.sin_arcsin (by linarith) ((div_le_one ht0).2 ht)
    have hcosβ : Real.cos β ≤ 1 - 2 / t ^ 2 := by rw [hβ]; exact cos_arcsin_le t ht
    have hr0 : 0 ≤ C / W := div_nonneg hC hW.le
    have hr1 : C / W ≤ 1 := (div_le_one hW).2 hCW
    have hr0' : 0 ≤ C' / W := div_nonneg hC' hW.le
    have hr1' : C' / W ≤ 1 := (div_le_one hW).2 hC'W
    have hs1 : Real.sqrt (C / W) ≤ 1 := (Real.sqrt_le_sqrt hr1).trans_eq Real.sqrt_one
    have hs1' : Real.sqrt (C' / W) ≤ 1 := (Real.sqrt_le_sqrt hr1').trans_eq Real.sqrt_one
    have hsW : 0 ≤ Real.sqrt W := Real.sqrt_nonneg W
    obtain ⟨φ, hφ⟩ : ∃ φ, φ = Real.arccos (Real.sqrt (C / W)) := ⟨_, rfl⟩
    obtain ⟨φ', hφ'⟩ : ∃ φ', φ' = Real.arccos (Real.sqrt (C' / W)) := ⟨_, rfl⟩
    have hφ0 : 0 ≤ φ := by rw [hφ]; exact Real.arccos_nonneg _
    have hφ0' : 0 ≤ φ' := by rw [hφ']; exact Real.arccos_nonneg _
    have hφ1 : φ ≤ Real.pi / 2 := by
      rw [hφ]; exact Real.arccos_le_pi_div_two.2 (Real.sqrt_nonneg _)
    have hφ1' : φ' ≤ Real.pi / 2 := by
      rw [hφ']; exact Real.arccos_le_pi_div_two.2 (Real.sqrt_nonneg _)
    have hcφ0 : Real.cos φ = Real.sqrt (C / W) := by
      rw [hφ]; exact Real.cos_arccos (by linarith [Real.sqrt_nonneg (C / W)]) hs1
    have hcφ0' : Real.cos φ' = Real.sqrt (C' / W) := by
      rw [hφ']; exact Real.cos_arccos (by linarith [Real.sqrt_nonneg (C' / W)]) hs1'
    have hsq : Real.cos φ ^ 2 = C / W := by rw [hcφ0, Real.sq_sqrt hr0]
    have hsq' : Real.cos φ' ^ 2 = C' / W := by rw [hcφ0', Real.sq_sqrt hr0']
    have hcφ : Real.cos φ = Real.sqrt C * (Real.sqrt W)⁻¹ := by
      rw [hcφ0, Real.sqrt_div hC, div_eq_mul_inv]
    have hcφ' : Real.cos φ' = Real.sqrt C' * (Real.sqrt W)⁻¹ := by
      rw [hcφ0', Real.sqrt_div hC', div_eq_mul_inv]
    have hsφ : Real.sin φ = Real.sqrt (W - C) * (Real.sqrt W)⁻¹ := by
      rw [hφ, Real.sin_arccos, Real.sq_sqrt hr0]
      have e : 1 - C / W = (W - C) / W := by field_simp
      rw [e, Real.sqrt_div (by linarith), div_eq_mul_inv]
    have hcφnn : 0 ≤ Real.cos φ := by rw [hcφ0]; exact Real.sqrt_nonneg _
    have h' : (1 - 2 / t ^ 2) * Real.cos φ - 2 / t * Real.sin φ ≤ Real.cos φ' := by
      rw [hcφ, hsφ, hcφ']
      have := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hsW)
      linarith
    have hcos : Real.cos (φ + β) ≤ Real.cos φ' := by
      rw [Real.cos_add, hsinβ]
      have h1 := mul_le_mul_of_nonneg_left hcosβ hcφnn
      linarith
    have hφφ' : φ' ≤ φ + β := by
      by_contra hlt
      push_neg at hlt
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := φ + β) (y := φ') (by linarith)
        (by linarith [Real.pi_pos]) hlt
      linarith
    have key : gf (C / W) - gf (C' / W) ≤ β / 2 := by
      rcases le_total φ φ' with hle | hle
      · have := gf_cos_sq_lip hφ0 hle hφ1'
        rw [hsq, hsq'] at this
        linarith
      · have hc : Real.cos φ ≤ Real.cos φ' :=
          Real.cos_le_cos_of_nonneg_of_le_pi hφ0' (by linarith [Real.pi_pos]) hle
        have hm : C / W ≤ C' / W := by
          rw [← hsq, ← hsq']
          exact pow_le_pow_left₀ hcφnn hc 2
        have := gf_monotoneOn ⟨hr0, hr1⟩ ⟨hr0', hr1'⟩ hm
        linarith
    rw [← hβ, Vf_of_pos hW, Vf_of_pos hW]
    have hk : 0 ≤ 2 / β := by positivity
    have e : (2 / β * W) * (β / 2) = W := by field_simp
    have := mul_le_mul_of_nonneg_left key (mul_nonneg hk hW.le)
    nlinarith [this, e]

/-! ### Numeric facts about `κ` -/

/-- κ is at least √(t² − 4). -/
theorem sqrt_le_kappa (t : ℝ) (ht : 2 ≤ t) : Real.sqrt (t ^ 2 - 4) ≤ 2 / Real.arcsin (2 / t) := by
  have ht0 : 0 < t := by linarith
  have h2t : 0 < 2 / t := div_pos two_pos ht0
  have hβpos : 0 < Real.arcsin (2 / t) := Real.arcsin_pos.2 h2t
  rw [le_div_iff₀ hβpos]
  rcases ht.eq_or_lt with h | h
  · subst h
    norm_num
  · have h1 : 2 / t < 1 := (div_lt_one ht0).2 h
    have hx : Real.arcsin (2 / t) < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 h1
    have hcpos : 0 < Real.cos (Real.arcsin (2 / t)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx⟩
    have hle := Real.le_tan hβpos.le hx
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcpos,
      Real.sin_arcsin (by linarith) h1.le, Real.cos_arcsin] at hle
    have h2 : t * (2 / t) = 2 := by field_simp
    have h3 : t ^ 2 - 4 = t ^ 2 * (1 - (2 / t) ^ 2) := by
      have : t ^ 2 * (2 / t) ^ 2 = 4 := by rw [← mul_pow, h2]; norm_num
      linear_combination this
    have e : Real.sqrt (t ^ 2 - 4) = t * Real.sqrt (1 - (2 / t) ^ 2) := by
      rw [h3, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0.le]
    rw [e]
    calc t * Real.sqrt (1 - (2 / t) ^ 2) * Real.arcsin (2 / t)
        = t * (Real.arcsin (2 / t) * Real.sqrt (1 - (2 / t) ^ 2)) := by ring
      _ ≤ t * (2 / t) := mul_le_mul_of_nonneg_left hle ht0.le
      _ = 2 := h2

/-- The end bound used by the assembly. -/
theorem kappa_end (t : ℝ) (ht : 2 ≤ t) :
    (Real.pi / 8 + 1 / 4) * t - 4 / t ≤
      (2 / Real.arcsin (2 / t)) * ((Real.pi / 8 + 1 / 4) * (1 - 2 / t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have hK := sqrt_le_kappa t ht
  have hs : t - 4 / t ≤ Real.sqrt (t ^ 2 - 4) := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have h1 : 16 / t ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e : (t - 4 / t) ^ 2 = t ^ 2 - 8 + 16 / t ^ 2 := by
      field_simp <;> ring
    rw [e]; linarith
  have hc0 : 0 ≤ Real.pi / 8 + 1 / 4 := by positivity
  have h1' : 0 ≤ 1 - 2 / t ^ 2 := by
    have : 2 / t ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hq : 0 ≤ (Real.pi / 8 + 1 / 4) * (1 - 2 / t ^ 2) := mul_nonneg hc0 h1'
  have h2 := mul_le_mul_of_nonneg_right (hs.trans hK) hq
  have e : (t - 4 / t) * ((Real.pi / 8 + 1 / 4) * (1 - 2 / t ^ 2))
      = (Real.pi / 8 + 1 / 4) * t - 6 * (Real.pi / 8 + 1 / 4) / t
        + 8 * (Real.pi / 8 + 1 / 4) / t ^ 3 := by
    field_simp <;> ring
  have h3 : 0 ≤ (4 - 6 * (Real.pi / 8 + 1 / 4)) / t :=
    div_nonneg (by linarith [Real.pi_lt_d2]) ht0.le
  have h4 : 0 ≤ 8 * (Real.pi / 8 + 1 / 4) / t ^ 3 := by positivity
  have e2 : (4 - 6 * (Real.pi / 8 + 1 / 4)) / t = 4 / t - 6 * (Real.pi / 8 + 1 / 4) / t := by
    ring
  linarith


/-- Subadditivity of `Vf` over a finite family (Lemma s-V(ii), finite case). -/
theorem Vf_finset_sum {ι : Type*} (s : Finset ι) (C W : ι → ℝ) (h0 : ∀ o ∈ s, 0 ≤ C o)
    (h1 : ∀ o ∈ s, C o ≤ W o) :
    Vf (∑ o ∈ s, C o) (∑ o ∈ s, W o) ≤ ∑ o ∈ s, Vf (C o) (W o) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Vf_00]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have hs0 : ∀ o ∈ s, 0 ≤ C o := fun o ho => h0 o (Finset.mem_insert_of_mem ho)
    have hs1 : ∀ o ∈ s, C o ≤ W o := fun o ho => h1 o (Finset.mem_insert_of_mem ho)
    have ha0 := h0 a (Finset.mem_insert_self a s)
    have ha1 := h1 a (Finset.mem_insert_self a s)
    have hS0 : 0 ≤ ∑ o ∈ s, C o := Finset.sum_nonneg hs0
    have hS1 : ∑ o ∈ s, C o ≤ ∑ o ∈ s, W o := Finset.sum_le_sum hs1
    calc Vf (C a + ∑ o ∈ s, C o) (W a + ∑ o ∈ s, W o)
        ≤ Vf (C a) (W a) + Vf (∑ o ∈ s, C o) (∑ o ∈ s, W o) := Vf_add _ _ _ _ ha0 ha1 hS0 hS1
      _ ≤ Vf (C a) (W a) + ∑ o ∈ s, Vf (C o) (W o) := by linarith [ih hs0 hs1]

end TheoremS
