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
Lemma lem:m-cell (one joint state) of the paper's section on measurable outcome spaces.

Notation of the paper and its Lean form, for `Y : Op N (RK N K)` positive trace class on `H' = H N (RK N K)`:
`W(Y) = tr Y` (`tr`), `C(Y) = tr((|u⟩⟨u| ⊗ I) Y)` (`Cf Y`), `p_x = tr β_x(Y)` (`tr (beta x Y)`), and
`U Y U*` is `ctrlU ∘L Y ∘L adjoint ctrlU`. All three are finite for `PosTC Y` (`Cf_le_tr`, `tr_eq_sum_beta`),
so the real inequalities are stated with `ENNReal.toReal`. `C ≤ W` is `Cf_le_tr` and `W(UYU*) = W` is
`tr_ctrlU` (both in `TheoremS/Meas/Joint.lean`), so (i) here is the inequality only.
-/
import TheoremS.Meas.Joint

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

/-! Helpers: copies of private lemmas of `TheoremS/Meas/Trace.lean`, and a limit lemma. -/

section CellGen

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] {ι ι' : Type*}

private lemma cl_summable_of_enn {α : Type*} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a)
    (h : ∑' a, ENNReal.ofReal (f a) ≠ ∞) : Summable f :=
  (ENNReal.summable_toReal h).congr fun a => ENNReal.toReal_ofReal (h0 a)

private lemma cl_hasSum_of_enn {α : Type*} {f : α → ℝ} {t : ℝ≥0∞}
    (h : ∑' a, ENNReal.ofReal (f a) = t) (ht : t ≠ ∞) (h0 : ∀ a, 0 ≤ f a) : HasSum f t.toReal := by
  have hs : Summable f := cl_summable_of_enn h0 (by rw [h]; exact ht)
  have e : t.toReal = ∑' a, f a := by
    rw [← h, ← ENNReal.ofReal_tsum_of_nonneg h0 hs, ENNReal.toReal_ofReal (tsum_nonneg h0)]
  rw [e]
  exact hs.hasSum

private lemma cl_hb_parseval (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using h

private lemma cl_hb_parseval_enn (b : HilbertBasis ι ℂ E) (x : E) :
    ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (cl_hb_parseval b x).summable,
    (cl_hb_parseval b x).tsum_eq]

private def cl_HS (b : HilbertBasis ι ℂ E) (S : E →L[ℂ] E') : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2)

private lemma cl_HS_adjoint [CompleteSpace E] [CompleteSpace E'] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis ι' ℂ E') (S : E →L[ℂ] E') :
    cl_HS b S = cl_HS c (ContinuousLinearMap.adjoint S) := by
  unfold cl_HS
  calc ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, S (b i)⟫_ℂ‖ ^ 2) :=
        tsum_congr fun i => (cl_hb_parseval_enn c _).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪c j, S (b i)⟫_ℂ‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪b i, ContinuousLinearMap.adjoint S (c j)⟫_ℂ‖ ^ 2) := by
        refine tsum_congr fun j => tsum_congr fun i => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left S (b i) (c j), norm_inner_symm]
    _ = ∑' j, ENNReal.ofReal (‖ContinuousLinearMap.adjoint S (c j)‖ ^ 2) :=
        tsum_congr fun j => cl_hb_parseval_enn b _

private lemma cl_exists_sqrt [CompleteSpace E] {Y : E →L[ℂ] E} (hY : Y.IsPositive) :
    ∃ T : E →L[ℂ] E, ContinuousLinearMap.adjoint T = T ∧ Y = T ∘L T := by
  have hY0 : 0 ≤ Y := ContinuousLinearMap.nonneg_iff_isPositive.mpr hY
  refine ⟨CFC.sqrt Y, ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)), ?_⟩
  rw [← ContinuousLinearMap.mul_def, CFC.sqrt_mul_sqrt_self Y hY0]

/-- Passing a finite-truncation inequality to the limit along `Finset α`. -/
private lemma cl_limit {α : Type*} {f g h : α → ℝ} {A W C a b : ℝ} (hf : HasSum f A)
    (hg : HasSum g W) (hh : HasSum h C)
    (hF : ∀ F : Finset α, a * Real.sqrt (∑ c ∈ F, f c)
      - b * Real.sqrt (∑ c ∈ F, g c - ∑ c ∈ F, f c) ≤ Real.sqrt (∑ c ∈ F, h c)) :
    a * Real.sqrt A - b * Real.sqrt (W - A) ≤ Real.sqrt C := by
  classical
  have tf : Filter.Tendsto (fun F : Finset α => ∑ c ∈ F, f c) Filter.atTop (nhds A) := hf
  have tg : Filter.Tendsto (fun F : Finset α => ∑ c ∈ F, g c) Filter.atTop (nhds W) := hg
  have th : Filter.Tendsto (fun F : Finset α => ∑ c ∈ F, h c) Filter.atTop (nhds C) := hh
  have t1 : Filter.Tendsto (fun F : Finset α => a * Real.sqrt (∑ c ∈ F, f c)
      - b * Real.sqrt (∑ c ∈ F, g c - ∑ c ∈ F, f c)) Filter.atTop
      (nhds (a * Real.sqrt A - b * Real.sqrt (W - A))) :=
    (tf.sqrt.const_mul a).sub ((tg.sub tf).sqrt.const_mul b)
  exact le_of_tendsto_of_tendsto' t1 th.sqrt hF

end CellGen

/-! Helpers: the argument of `TheoremS/Inf/Mean.lean` (around `Cm_query`) for vectors of
`H N L`, with `oracleL` in place of `oracle`. -/

section CellVec

variable {N : ℕ} {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L]

private def cl_bitflip (i : Idx N) : Idx N := (i.1, !i.2)

private def cl_bitflipEquiv : Idx N ≃ Idx N where
  toFun := cl_bitflip
  invFun := cl_bitflip
  left_inv := fun i => by rcases i with ⟨y, b⟩; simp [cl_bitflip]
  right_inv := fun i => by rcases i with ⟨y, b⟩; simp [cl_bitflip]

private def cl_bitflipOp : H N L ≃ₗᵢ[ℂ] H N L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ L (cl_bitflipEquiv (N := N))

private lemma cl_bitflipOp_apply (v : H N L) (i : Idx N) : cl_bitflipOp v i = v (cl_bitflip i) := rfl

private lemma cl_oracleL_apply (x : Fin N) (v : H N L) (i : Idx N) :
    oracleL x v i = v (TheoremS.Meas.flip x i) := rfl

private def cl_diagVec (v : Fin N → H N L) : H N L :=
  WithLp.toLp 2 (fun i : Idx N => v i.1 i)

private lemma cl_diagVec_apply (v : Fin N → H N L) (i : Idx N) : cl_diagVec v i = v i.1 i := rfl

private lemma cl_diagVec_eq_add (v : Fin N → H N L) (m : H N L) :
    cl_diagVec v = m + cl_diagVec (fun x => v x - m) := by
  ext i
  simp [cl_diagVec_apply]

private lemma cl_norm_diagVec_sq_le (d : Fin N → H N L) : ‖cl_diagVec d‖ ^ 2 ≤ ∑ x, ‖d x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [cl_diagVec_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun y _ => ?_
  calc ∑ b : Bool, ‖d (y, b).1 (y, b)‖ ^ 2 = ∑ b : Bool, ‖d y (y, b)‖ ^ 2 := rfl
    _ ≤ ∑ y' : Fin N, ∑ b : Bool, ‖d y (y', b)‖ ^ 2 :=
        Finset.single_le_sum (f := fun y' => ∑ b : Bool, ‖d y (y', b)‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ y)
    _ = ∑ i : Idx N, ‖d y i‖ ^ 2 := by rw [Fintype.sum_prod_type]
    _ = ‖d y‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ _).symm

private lemma cl_sum_oracle_sub (ψ : Fin N → H N L) :
    ∑ x, (oracleL x (ψ x) - ψ x) = cl_bitflipOp (cl_diagVec ψ) - cl_diagVec ψ := by
  ext i
  rcases i with ⟨y, b⟩
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply, WithLp.ofLp_sub, Pi.sub_apply,
    cl_oracleL_apply, cl_bitflipOp_apply, cl_diagVec_apply]
  rw [Finset.sum_eq_single y]
  · simp [TheoremS.Meas.flip, cl_bitflip]
  · intro x _ hx
    simp [TheoremS.Meas.flip, Ne.symm hx]
  · simp

private lemma cl_sum_norm_sub_sq (v : Fin N → H N L) (m : H N L) (hm : ∑ x, v x = ∑ _x : Fin N, m) :
    ∑ x, ‖v x - m‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 - N * ‖m‖ ^ 2 := by
  have h2 : ∑ x, inner ℂ (v x) m = ∑ _x : Fin N, inner ℂ m m := by
    rw [← sum_inner, ← sum_inner, hm]
  have h3 : RCLike.re (∑ x, inner ℂ (v x) m) = RCLike.re (∑ _x : Fin N, inner ℂ m m) := by
    rw [h2]
  rw [map_sum, map_sum] at h3
  have h1 : ∑ x, RCLike.re (inner ℂ (v x) m) = ∑ _x : Fin N, ‖m‖ ^ 2 := by
    rw [h3]
    simp only [inner_self_eq_norm_sq]
  simp_rw [norm_sub_sq (𝕜 := ℂ)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma cl_query_bound_aux (hn : (0 : ℝ) < N) {F : H N L ≃ₗᵢ[ℂ] H N L} {μ μ' Ψ G : H N L}
    {s : ℝ} (h1 : μ' = μ + ((N : ℂ)⁻¹) • (F Ψ - Ψ)) (h2 : Ψ = μ + G) (h3 : ‖G‖ ≤ Real.sqrt N * s) :
    (1 - 2 / (N : ℝ)) * ‖μ‖ - 2 / Real.sqrt N * s ≤ ‖μ'‖ := by
  have hD : ‖F Ψ - Ψ‖ ≤ 2 * (‖μ‖ + Real.sqrt N * s) := by
    calc ‖F Ψ - Ψ‖ ≤ ‖F Ψ‖ + ‖Ψ‖ := norm_sub_le _ _
      _ = 2 * ‖Ψ‖ := by rw [LinearIsometryEquiv.norm_map]; ring
      _ ≤ 2 * (‖μ‖ + ‖G‖) := by
          rw [h2]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ 2 * (‖μ‖ + Real.sqrt N * s) := by linarith
  have hsm : ‖((N : ℂ)⁻¹) • (F Ψ - Ψ)‖ = (N : ℝ)⁻¹ * ‖F Ψ - Ψ‖ := by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hμ : ‖μ‖ ≤ ‖μ'‖ + (N : ℝ)⁻¹ * ‖F Ψ - Ψ‖ := by
    rw [← hsm, h1]
    calc ‖μ‖ = ‖(μ + ((N : ℂ)⁻¹) • (F Ψ - Ψ)) - ((N : ℂ)⁻¹) • (F Ψ - Ψ)‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have hm : (N : ℝ)⁻¹ * ‖F Ψ - Ψ‖ ≤ (N : ℝ)⁻¹ * (2 * (‖μ‖ + Real.sqrt N * s)) :=
    mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr hn.le)
  have e : (N : ℝ)⁻¹ * (2 * (‖μ‖ + Real.sqrt N * s)) = 2 / N * ‖μ‖ + 2 / Real.sqrt N * s := by
    have h' : Real.sqrt N / N = 1 / Real.sqrt N := Real.sqrt_div_self'
    calc (N : ℝ)⁻¹ * (2 * (‖μ‖ + Real.sqrt N * s))
        = 2 / N * ‖μ‖ + 2 * (Real.sqrt N / N) * s := by ring
      _ = 2 / N * ‖μ‖ + 2 / Real.sqrt N * s := by rw [h']; ring
  have e2 : (1 - 2 / (N : ℝ)) * ‖μ‖ = ‖μ‖ - 2 / N * ‖μ‖ := by ring
  linarith

/-- The vector form of Lemma s-query (`Cm_query` of `TheoremS/Inf/Mean.lean`): `μ` the mean of `φ`, `V` the mean of `‖φ‖²`. -/
private lemma cl_vec_query (hN : 0 < N) (φ : Fin N → H N L) {μ μ' : H N L} {V : ℝ}
    (hμ : μ = (N : ℂ)⁻¹ • ∑ x, φ x) (hμ' : μ' = (N : ℂ)⁻¹ • ∑ x, oracleL x (φ x))
    (hV : (N : ℝ)⁻¹ * ∑ x, ‖φ x‖ ^ 2 = V) :
    (1 - 2 / (N : ℝ)) * ‖μ‖ - 2 / Real.sqrt N * Real.sqrt (V - ‖μ‖ ^ 2) ≤ ‖μ'‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : μ' = μ + ((N : ℂ)⁻¹) • (cl_bitflipOp (cl_diagVec φ) - cl_diagVec φ) := by
    rw [← cl_sum_oracle_sub, Finset.sum_sub_distrib, smul_sub, hμ, hμ']
    abel
  have hS : ∑ _x : Fin N, μ = ∑ x, φ x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, hμ,
      smul_smul, mul_inv_cancel₀ hNc, one_smul]
  have hvar : ∑ x, ‖φ x - μ‖ ^ 2 = N * (V - ‖μ‖ ^ 2) := by
    rw [cl_sum_norm_sub_sq _ _ hS.symm, ← hV, mul_sub, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  have hG : ‖cl_diagVec (fun x => φ x - μ)‖ ≤ Real.sqrt N * Real.sqrt (V - ‖μ‖ ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← hvar]
    calc ‖cl_diagVec (fun x => φ x - μ)‖
        = Real.sqrt (‖cl_diagVec (fun x => φ x - μ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (cl_norm_diagVec_sq_le _)
  exact cl_query_bound_aux hNr h1 (cl_diagVec_eq_add _ _) hG

/-- `cl_vec_query` for `φ = √N ψ`: the mean is `(1/√N) ∑ ψ` and the mean of `‖φ‖²` is `∑ ‖ψ‖²`. -/
private lemma cl_vec_query' (hN : 0 < N) (ψ : Fin N → H N L) :
    (1 - 2 / (N : ℝ)) * ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x‖
      - 2 / Real.sqrt N * Real.sqrt (∑ x, ‖ψ x‖ ^ 2
          - ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x‖ ^ 2)
      ≤ ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, oracleL x (ψ x)‖ := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    simp
  have hs0 : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hs
    exact hNc hs.symm
  have hc : (1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ)⁻¹ * (Real.sqrt (N : ℝ) : ℂ) := by
    rw [← hs, mul_inv, mul_assoc, inv_mul_cancel₀ hs0, mul_one, one_div]
  have hr : ‖(Real.sqrt (N : ℝ) : ℂ)‖ = Real.sqrt N := Complex.norm_of_nonneg (Real.sqrt_nonneg _)
  refine cl_vec_query hN (fun x => (Real.sqrt (N : ℝ) : ℂ) • ψ x) ?_ ?_ ?_
  · rw [← Finset.smul_sum, smul_smul, ← hc]
  · simp only [map_smul]
    rw [← Finset.smul_sum, smul_smul, ← hc]
  · simp only [norm_smul, hr, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]

/-- `‖∑ ψ‖² ≤ 2 ∑_{x ∈ T} ‖ψ x‖² + 2 N ∑_{x ∉ T} ‖ψ x‖²` for `|T| ≤ 1`. -/
private lemma cl_sq_split {F : Type*} [SeminormedAddCommGroup F] (ψ : Fin N → F) (T : Finset (Fin N))
    (hT : T.card ≤ 1) :
    ‖∑ x, ψ x‖ ^ 2 ≤ 2 * ∑ x ∈ T, ‖ψ x‖ ^ 2 + 2 * N * ∑ x ∈ Tᶜ, ‖ψ x‖ ^ 2 := by
  have hsplit : ∑ x, ψ x = ∑ x ∈ T, ψ x + ∑ x ∈ Tᶜ, ψ x := (Finset.sum_add_sum_compl T ψ).symm
  have hA : (∑ x ∈ T, ‖ψ x‖) ^ 2 ≤ ∑ x ∈ T, ‖ψ x‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := T) (f := fun x => ‖ψ x‖)
    have hc : (T.card : ℝ) ≤ 1 := by exact_mod_cast hT
    have h0 : 0 ≤ ∑ x ∈ T, ‖ψ x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have hB : (∑ x ∈ Tᶜ, ‖ψ x‖) ^ 2 ≤ N * ∑ x ∈ Tᶜ, ‖ψ x‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Tᶜ) (f := fun x => ‖ψ x‖)
    have hc : ((Tᶜ).card : ℝ) ≤ N := by
      have h' := Finset.card_le_univ Tᶜ
      rw [Fintype.card_fin] at h'
      exact_mod_cast h'
    have h0 : 0 ≤ ∑ x ∈ Tᶜ, ‖ψ x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have h1 : ‖∑ x, ψ x‖ ≤ ∑ x ∈ T, ‖ψ x‖ + ∑ x ∈ Tᶜ, ‖ψ x‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
  have h2 : 0 ≤ ‖∑ x, ψ x‖ := norm_nonneg _
  have h3 : ‖∑ x, ψ x‖ ^ 2 ≤ (∑ x ∈ T, ‖ψ x‖ + ∑ x ∈ Tᶜ, ‖ψ x‖) ^ 2 := pow_le_pow_left₀ h2 h1 2
  nlinarith [sq_nonneg (∑ x ∈ T, ‖ψ x‖ - ∑ x ∈ Tᶜ, ‖ψ x‖)]

private lemma cl_s_norm_sq : ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ))‖ ^ 2 = (N : ℝ)⁻¹ := by
  rw [norm_div, norm_one, Complex.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, one_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), one_div]

end CellVec

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! Helpers: packing a finite family of vectors of `H N K` into one vector of
`H N (PiLp 2 (fun _ : ι => K))`, on which `oracleL` acts coordinatewise. -/

private def cl_pk {ι : Type} [Fintype ι] (f : ι → H N K) : H N (PiLp 2 (fun _ : ι => K)) :=
  WithLp.toLp 2 (fun i : Idx N => WithLp.toLp 2 (fun c : ι => f c i))

omit [CompleteSpace K] in
private lemma cl_pk_apply {ι : Type} [Fintype ι] (f : ι → H N K) (i : Idx N) (c : ι) :
    cl_pk f i c = f c i := rfl

omit [CompleteSpace K] in
private lemma cl_pk_norm_sq {ι : Type} [Fintype ι] (f : ι → H N K) :
    ‖cl_pk f‖ ^ 2 = ∑ c, ‖f c‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, cl_pk_apply]
  exact Finset.sum_comm

omit [CompleteSpace K] in
private lemma cl_pk_norm {ι : Type} [Fintype ι] (f : ι → H N K) :
    ‖cl_pk f‖ = Real.sqrt (∑ c, ‖f c‖ ^ 2) := by
  rw [← cl_pk_norm_sq, Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace K] in
private lemma cl_pk_oracle {ι : Type} [Fintype ι] (x : Fin N) (f : ι → H N K) :
    oracleL x (cl_pk f) = cl_pk (fun c => oracleL x (f c)) := by
  ext i c
  rfl

omit [CompleteSpace K] in
private lemma cl_pk_smul_sum {ι : Type} [Fintype ι] (a : ℂ) (g : Fin N → ι → H N K) :
    a • ∑ x, cl_pk (g x) = cl_pk (fun c => a • ∑ x, g x c) := by
  ext i c
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, cl_pk_apply]

omit [CompleteSpace K] in
/-- (i) for a finite family. -/
private lemma cl_pack_query (hN : 0 < N) {ι : Type} [Fintype ι] (ψ : Fin N → ι → H N K) :
    (1 - 2 / (N : ℝ)) * Real.sqrt (∑ c, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2)
      - 2 / Real.sqrt N * Real.sqrt (∑ x, ∑ c, ‖ψ x c‖ ^ 2
          - ∑ c, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2)
      ≤ Real.sqrt (∑ c, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, oracleL x (ψ x c)‖ ^ 2) := by
  have h := cl_vec_query' hN (fun x => cl_pk (ψ x))
  simp only [cl_pk_oracle, cl_pk_smul_sum, cl_pk_norm_sq] at h
  simp only [cl_pk_norm] at h
  exact h

omit [CompleteSpace K] in
/-- (i) for families indexed by an arbitrary type, by truncation. -/
private lemma cl_query_core (hN : 0 < N) {α : Type} (ψ : Fin N → α → H N K) {A W C : ℝ}
    (hA : HasSum (fun c => ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2) A)
    (hW : HasSum (fun c => ∑ x, ‖ψ x c‖ ^ 2) W)
    (hC : HasSum (fun c => ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, oracleL x (ψ x c)‖ ^ 2) C) :
    (1 - 2 / (N : ℝ)) * Real.sqrt A - 2 / Real.sqrt N * Real.sqrt (W - A) ≤ Real.sqrt C := by
  refine cl_limit hA hW hC fun F => ?_
  have h := cl_pack_query hN (fun x (c : F) => ψ x c)
  have e1 : ∑ c : F, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2 =
      ∑ c ∈ F, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2 :=
    Finset.sum_coe_sort F (fun c => ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2)
  have e2 : ∑ x, ∑ c : F, ‖ψ x c‖ ^ 2 = ∑ c ∈ F, ∑ x, ‖ψ x c‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_coe_sort F (fun c => ∑ x, ‖ψ x c‖ ^ 2)
  have e3 : ∑ c : F, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, oracleL x (ψ x c)‖ ^ 2 =
      ∑ c ∈ F, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, oracleL x (ψ x c)‖ ^ 2 :=
    Finset.sum_coe_sort F (fun c => ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, oracleL x (ψ x c)‖ ^ 2)
  rw [e1, e2, e3] at h
  exact h

omit [CompleteSpace K] in
/-- (ii) for families indexed by an arbitrary type. -/
private lemma cl_end_core (hN : 0 < N) {α : Type} (ψ : Fin N → α → H N K) {Cr : ℝ} {q : Fin N → ℝ}
    (hA : HasSum (fun c => ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2) Cr)
    (hQ : ∀ x, HasSum (fun c => ‖ψ x c‖ ^ 2) (q x)) (T : Finset (Fin N)) (hT : T.card ≤ 1) :
    Cr ≤ 2 / (N : ℝ) * ∑ x ∈ T, q x + 2 * ∑ x ∈ Tᶜ, q x := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpt : ∀ c, ‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x, ψ x c‖ ^ 2
      ≤ 2 / (N : ℝ) * ∑ x ∈ T, ‖ψ x c‖ ^ 2 + 2 * ∑ x ∈ Tᶜ, ‖ψ x c‖ ^ 2 := by
    intro c
    rw [norm_smul, mul_pow, cl_s_norm_sq]
    have h := cl_sq_split (fun x => ψ x c) T hT
    have hinv : (N : ℝ)⁻¹ * N = 1 := inv_mul_cancel₀ hN0
    have e : 2 / (N : ℝ) * ∑ x ∈ T, ‖ψ x c‖ ^ 2 + 2 * ∑ x ∈ Tᶜ, ‖ψ x c‖ ^ 2
        = (N : ℝ)⁻¹ * (2 * ∑ x ∈ T, ‖ψ x c‖ ^ 2 + 2 * N * ∑ x ∈ Tᶜ, ‖ψ x c‖ ^ 2) := by
      linear_combination (-2 * ∑ x ∈ Tᶜ, ‖ψ x c‖ ^ 2) * hinv
    rw [e]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hR := ((hasSum_sum (s := T) fun x _ => hQ x).mul_left (2 / (N : ℝ))).add
    ((hasSum_sum (s := Tᶜ) fun x _ => hQ x).mul_left 2)
  exact hasSum_le hpt hA hR

/-! Helpers: the Hilbert-Schmidt form of the traces. -/

private lemma cl_tr_conj {T : Op N (RK N K)} (hT : ContinuousLinearMap.adjoint T = T)
    (A : H N (RK N K) →L[ℂ] H N K) :
    tr (A ∘L (T ∘L T) ∘L ContinuousLinearMap.adjoint A) =
      ∑' c, ENNReal.ofReal (‖A (T (hbasis N (RK N K) c))‖ ^ 2) := by
  rw [tr_eq_trB]
  have e : trB (hbasis N K) (A ∘L (T ∘L T) ∘L ContinuousLinearMap.adjoint A) =
      cl_HS (hbasis N K) (T ∘L ContinuousLinearMap.adjoint A) := by
    unfold trB cl_HS
    refine tsum_congr fun i => ?_
    congr 1
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left A
        (T (T (ContinuousLinearMap.adjoint A (hbasis N K i)))) (hbasis N K i),
      ← ContinuousLinearMap.adjoint_inner_left T (T (ContinuousLinearMap.adjoint A (hbasis N K i)))
        (ContinuousLinearMap.adjoint A (hbasis N K i)), hT]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [e, cl_HS_adjoint (hbasis N K) (hbasis N (RK N K)), ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hT]
  rfl

private lemma cl_tr_sq {T : Op N (RK N K)} (hT : ContinuousLinearMap.adjoint T = T) :
    tr (T ∘L T) = ∑' c, ENNReal.ofReal (‖T (hbasis N (RK N K) c)‖ ^ 2) := by
  rw [tr_eq_trB]
  unfold trB
  refine tsum_congr fun c => ?_
  congr 1
  rw [ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left T (T (hbasis N (RK N K) c)) (hbasis N (RK N K) c), hT]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

private lemma cl_norm_sq_blocks (ψ : H N (RK N K)) :
    ‖ψ‖ ^ 2 = ∑ x : Fin N, ‖ContinuousLinearMap.adjoint (slot x) ψ‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 _ ψ]
  simp only [PiLp.norm_sq_eq_of_L2, adjoint_slot_apply]
  exact Finset.sum_comm

private lemma cl_uEmb_adjoint :
    ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) =
      ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x : Fin N, ContinuousLinearMap.adjoint (slot (K := K) x) := by
  rw [uEmb, map_smulₛₗ, map_sum]
  congr 1
  simp [Complex.conj_ofReal]

private lemma cl_adjU_apply (w : H N (RK N K)) :
    ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) w =
      ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x : Fin N, ContinuousLinearMap.adjoint (slot (K := K) x) w := by
  rw [cl_uEmb_adjoint, smul_apply, sum_apply]

private lemma cl_adjU_ctrlU_apply (w : H N (RK N K)) :
    ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) (ctrlU w) =
      ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) •
        ∑ x : Fin N, oracleL x (ContinuousLinearMap.adjoint (slot (K := K) x) w) := by
  have h : ∀ x : Fin N, ContinuousLinearMap.adjoint (slot (K := K) x) (ctrlU w) =
      oracleL x (ContinuousLinearMap.adjoint (slot (K := K) x) w) := fun x => by
    have h1 := DFunLike.congr_fun (adjoint_slot_comp_ctrlU (N := N) (K := K) x) w
    simp only [ContinuousLinearMap.comp_apply] at h1
    exact h1
  rw [cl_adjU_apply]
  simp only [h]

private lemma cl_tr_nat_smul (n : ℕ) (Z : Op N K) : tr ((n : ℂ) • Z) = n * tr Z := by
  rw [tr_eq_trB, tr_eq_trB]
  have h := trB_smul (b := hbasis N K) (Y := Z) (n : NNReal)
  simpa using h

private lemma cl_Cf_eq {S : Op N (RK N K)} (hS : ContinuousLinearMap.adjoint S = S) :
    Cf (S ∘L S) = ∑' c, ENNReal.ofReal (‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) •
      ∑ x, ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c))‖ ^ 2) := by
  have h := cl_tr_conj hS (ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)))
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  unfold Cf
  rw [h]
  simp only [cl_adjU_apply]

private lemma cl_tr_eq {S : Op N (RK N K)} (hS : ContinuousLinearMap.adjoint S = S) :
    tr (S ∘L S) = ∑' c, ENNReal.ofReal
      (∑ x, ‖ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c))‖ ^ 2) := by
  rw [cl_tr_sq hS]
  simp only [cl_norm_sq_blocks]

private lemma cl_CfU_eq {S : Op N (RK N K)} (hS : ContinuousLinearMap.adjoint S = S) :
    Cf (ctrlU ∘L (S ∘L S) ∘L ContinuousLinearMap.adjoint ctrlU) =
      ∑' c, ENNReal.ofReal (‖((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) •
        ∑ x, oracleL x (ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c)))‖ ^ 2) := by
  have eop : ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) ∘L
      (ctrlU ∘L (S ∘L S) ∘L ContinuousLinearMap.adjoint ctrlU) ∘L uEmb =
      (ContinuousLinearMap.adjoint uEmb ∘L ctrlU) ∘L (S ∘L S) ∘L
        ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint uEmb ∘L ctrlU) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
    ext1 v
    simp only [ContinuousLinearMap.comp_apply]
  unfold Cf
  rw [eop, cl_tr_conj hS]
  simp only [ContinuousLinearMap.comp_apply, cl_adjU_ctrlU_apply]

/-- lem:m-cell (i): one oracle call on a joint state moves `√C` by at most `(2/N)√C + (2/√N)√(W - C)`:
`(1 - 2/N) √C - (2/√N) √(W - C) ≤ √C(U Y U*)`. -/
theorem cell_query (hN : 0 < N) {Y : Op N (RK N K)} (hY : PosTC Y) :
    (1 - 2 / (N : ℝ)) * Real.sqrt (Cf Y).toReal
        - 2 / Real.sqrt N * Real.sqrt ((tr Y).toReal - (Cf Y).toReal)
      ≤ Real.sqrt (Cf (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU)).toReal := by
  obtain ⟨S, hS, rfl⟩ := cl_exists_sqrt hY.1
  have hU : PosTC (ctrlU ∘L (S ∘L S) ∘L ContinuousLinearMap.adjoint ctrlU) :=
    ⟨hY.1.conj_adjoint ctrlU, by rw [tr_ctrlU hY]; exact hY.2⟩
  have hCfin : Cf (S ∘L S) ≠ ∞ := ((Cf_le_tr hY).trans_lt hY.2).ne
  have hCUfin : Cf (ctrlU ∘L (S ∘L S) ∘L ContinuousLinearMap.adjoint ctrlU) ≠ ∞ :=
    ((Cf_le_tr hU).trans_lt hU.2).ne
  have hA := cl_hasSum_of_enn (cl_Cf_eq hS).symm hCfin (fun _ => sq_nonneg _)
  have hW := cl_hasSum_of_enn (cl_tr_eq hS).symm hY.2.ne
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hC := cl_hasSum_of_enn (cl_CfU_eq hS).symm hCUfin (fun _ => sq_nonneg _)
  exact cl_query_core hN
    (fun x c => ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c))) hA hW hC

/-- lem:m-cell (ii): for `T ⊆ [N]` with `|T| ≤ 1`,
`C ≤ (2/N²) ∑_{x ∈ T} p_x + (2/N) ∑_{x ∉ T} p_x`. -/
theorem cell_end (hN : 0 < N) {Y : Op N (RK N K)} (hY : PosTC Y) (T : Finset (Fin N)) (hT : T.card ≤ 1) :
    (Cf Y).toReal ≤ 2 / (N : ℝ) ^ 2 * ∑ x ∈ T, (tr (beta x Y)).toReal
      + 2 / (N : ℝ) * ∑ x ∈ Tᶜ, (tr (beta x Y)).toReal := by
  obtain ⟨S, hS, rfl⟩ := cl_exists_sqrt hY.1
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNe : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hCfin : Cf (S ∘L S) ≠ ∞ := ((Cf_le_tr hY).trans_lt hY.2).ne
  have hA := cl_hasSum_of_enn (cl_Cf_eq hS).symm hCfin (fun _ => sq_nonneg _)
  have hbt : ∀ x, tr (beta x (S ∘L S)) ≠ ∞ := fun x => by
    have h1 : tr (beta x (S ∘L S)) ≤ ∑ x', tr (beta x' (S ∘L S)) :=
      Finset.single_le_sum (f := fun x' => tr (beta x' (S ∘L S))) (fun _ _ => zero_le)
        (Finset.mem_univ x)
    rw [← tr_eq_sum_beta hY.1] at h1
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hY.2.ne) h1
  have hQ : ∀ x, HasSum
      (fun c => ‖ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c))‖ ^ 2)
      ((tr (beta x (S ∘L S))).toReal / N) := fun x => by
    have h := cl_tr_conj hS (ContinuousLinearMap.adjoint (slot (K := K) x))
    rw [ContinuousLinearMap.adjoint_adjoint] at h
    have hb : tr (beta x (S ∘L S)) =
        (N : ℝ≥0∞) * tr (ContinuousLinearMap.adjoint (slot (K := K) x) ∘L (S ∘L S) ∘L slot x) := by
      rw [beta, cl_tr_nat_smul]
    have hfin : tr (ContinuousLinearMap.adjoint (slot (K := K) x) ∘L (S ∘L S) ∘L slot x) ≠ ∞ := by
      intro h'
      apply hbt x
      rw [hb, h', ENNReal.mul_top hNe]
    have e : (tr (beta x (S ∘L S))).toReal / N =
        (tr (ContinuousLinearMap.adjoint (slot (K := K) x) ∘L (S ∘L S) ∘L slot x)).toReal := by
      rw [hb, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_cancel_left₀ _ hN0]
    rw [e]
    exact cl_hasSum_of_enn h.symm hfin (fun _ => sq_nonneg _)
  have key := cl_end_core hN
    (fun x c => ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c))) hA hQ T hT
  have e2 : 2 / (N : ℝ) ^ 2 * ∑ x ∈ T, (tr (beta x (S ∘L S))).toReal
      + 2 / (N : ℝ) * ∑ x ∈ Tᶜ, (tr (beta x (S ∘L S))).toReal
      = 2 / (N : ℝ) * ∑ x ∈ T, (tr (beta x (S ∘L S))).toReal / N
        + 2 * ∑ x ∈ Tᶜ, (tr (beta x (S ∘L S))).toReal / N := by
    rw [← Finset.sum_div, ← Finset.sum_div]
    ring
  rw [e2]
  exact key

/-- lem:m-cell (iii): if `p_x = 0` for every `x ≠ y`, then `C = W/N`, stated as `N C = W`. -/
theorem cell_single {Y : Op N (RK N K)} (hY : PosTC Y) (y : Fin N)
    (hy : ∀ x, x ≠ y → tr (beta x Y) = 0) :
    (N : ℝ≥0∞) * Cf Y = tr Y := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by subst h; exact y.elim0
  obtain ⟨S, hS, rfl⟩ := cl_exists_sqrt hY.1
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hz : ∀ x, x ≠ y → ∀ c,
      ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c)) = 0 := by
    intro x hx c
    have h := cl_tr_conj hS (ContinuousLinearMap.adjoint (slot (K := K) x))
    rw [ContinuousLinearMap.adjoint_adjoint] at h
    have hb := hy x hx
    rw [beta, cl_tr_nat_smul, h] at hb
    have hq := (mul_eq_zero.mp hb).resolve_left (Nat.cast_ne_zero.mpr hN.ne')
    have hc := ENNReal.tsum_eq_zero.mp hq c
    rw [ENNReal.ofReal_eq_zero] at hc
    have h2 : ‖ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c))‖ ^ 2 = 0 :=
      le_antisymm hc (sq_nonneg _)
    simpa using h2
  have hsum : ∀ c, ∑ x, ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c)) =
      ContinuousLinearMap.adjoint (slot (K := K) y) (S (hbasis N (RK N K) c)) := fun c =>
    Finset.sum_eq_single y (fun x _ hx => hz x hx c) (fun h => absurd (Finset.mem_univ y) h)
  have hnsum : ∀ c,
      ∑ x, ‖ContinuousLinearMap.adjoint (slot (K := K) x) (S (hbasis N (RK N K) c))‖ ^ 2 =
        ‖ContinuousLinearMap.adjoint (slot (K := K) y) (S (hbasis N (RK N K) c))‖ ^ 2 := fun c =>
    Finset.sum_eq_single y (fun x _ hx => by simp [hz x hx c]) (fun h => absurd (Finset.mem_univ y) h)
  rw [cl_Cf_eq hS, cl_tr_eq hS, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun c => ?_
  rw [hsum c, hnsum c, norm_smul, mul_pow, cl_s_norm_sq, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]

end

end TheoremS.Meas
