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
The mean vector of an algorithm `A : Alg N K` and the one-step lemmas of the paper's proof of Theorem S
(the potential does not increase at operation nodes, the query step, the end bound), in finite dimension.

For a history `h`: `p x h = ‖ψ_x h‖²`, the mean `μ h = (1/N) ∑_x ψ_x h`, `Cm h = ‖μ h‖²`,
`Wm h = (1/N) ∑_x p x h`, and `sx x h = p x h` if `h` is a halt node with output `x`, else `0`.
-/
import TheoremS.Statement

namespace TheoremS

set_option autoImplicit false

open scoped ENNReal

namespace Alg

variable {N : ℕ} {K : Type} [Fintype K]

/-- The outcomes allowed after history `h`: `{0}` at a query node, `J` at an operation node, none at a halt. -/
def ch (A : Alg N K) (h : List ℕ) : Finset ℕ :=
  match A.node h with
  | .query => {0}
  | .op J _ => J
  | .halt _ => ∅

noncomputable def p (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ := ‖A.branch x h‖ ^ 2

noncomputable def mean (A : Alg N K) (h : List ℕ) : H N K := ((N : ℂ)⁻¹) • ∑ x, A.branch x h

noncomputable def Cm (A : Alg N K) (h : List ℕ) : ℝ := ‖A.mean h‖ ^ 2

noncomputable def Wm (A : Alg N K) (h : List ℕ) : ℝ := (N : ℝ)⁻¹ * ∑ x, A.p x h

noncomputable def sx (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ :=
  if (A.node h).output = some x then A.p x h else 0

theorem ch_query (A : Alg N K) {h : List ℕ} (hq : A.node h = .query) : A.ch h = {0} := by
  simp [ch, hq]

theorem ch_op (A : Alg N K) {h : List ℕ} {J : Finset ℕ} {B : ℕ → H N K →ₗ[ℂ] H N K}
    (hop : A.node h = .op J B) : A.ch h = J := by
  simp [ch, hop]

theorem ch_halt (A : Alg N K) {h : List ℕ} {y : Fin N} (hh : A.node h = .halt y) : A.ch h = ∅ := by
  simp [ch, hh]

theorem branch_cons_eq_zero (A : Alg N K) (x : Fin N) {h : List ℕ} {o : ℕ} (ho : o ∉ A.ch h) :
    A.branch x (o :: h) = 0 := by
  cases hn : A.node h <;> simp_all [ch, branch]

theorem branch_append_eq_zero (A : Alg N K) (x : Fin N) {h : List ℕ} (l : List ℕ)
    (h0 : A.branch x h = 0) : A.branch x (l ++ h) = 0 := by
  induction l with
  | nil => simpa using h0
  | cons a l ih =>
    simp only [List.cons_append, branch]
    split <;> simp [ih]

theorem p_nonneg (A : Alg N K) (x : Fin N) (h : List ℕ) : 0 ≤ A.p x h := by
  unfold p; positivity

/-- Helper: the branch below a query node. -/
theorem branch_cons_query (A : Alg N K) (x : Fin N) {h : List ℕ} (hq : A.node h = .query) :
    A.branch x (0 :: h) = oracle x (A.branch x h) := by
  simp [branch, hq]

/-- Helper: the branch below an operation node. -/
theorem branch_cons_op (A : Alg N K) (x : Fin N) {h : List ℕ} {J : Finset ℕ}
    {B : ℕ → H N K →ₗ[ℂ] H N K} (hop : A.node h = .op J B) {j : ℕ} (hj : j ∈ J) :
    A.branch x (j :: h) = B j (A.branch x h) := by
  simp [branch, hop, hj]

/-- Helper: a complete family of Kraus operators preserves the squared norm in total. -/
theorem sum_norm_sq_kraus (A : Alg N K) {h : List ℕ} {J : Finset ℕ} {B : ℕ → H N K →ₗ[ℂ] H N K}
    (hop : A.node h = .op J B) (v : H N K) : ∑ j ∈ J, ‖B j v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hc := A.complete h J B hop
  have key : ∑ j ∈ J, LinearMap.adjoint (B j) (B j v) = v := by
    calc ∑ j ∈ J, LinearMap.adjoint (B j) (B j v)
        = (∑ j ∈ J, LinearMap.adjoint (B j) ∘ₗ B j) v := by rw [LinearMap.sum_apply]; rfl
      _ = v := by rw [hc]; rfl
  calc ∑ j ∈ J, ‖B j v‖ ^ 2
      = ∑ j ∈ J, RCLike.re (inner ℂ v (LinearMap.adjoint (B j) (B j v))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]
    _ = RCLike.re (∑ j ∈ J, inner ℂ v (LinearMap.adjoint (B j) (B j v))) := by rw [map_sum]
    _ = RCLike.re (inner ℂ v v) := by rw [← inner_sum, key]
    _ = ‖v‖ ^ 2 := inner_self_eq_norm_sq v

theorem p_query (A : Alg N K) (x : Fin N) {h : List ℕ} (hq : A.node h = .query) :
    A.p x (0 :: h) = A.p x h := by
  simp [p, A.branch_cons_query x hq]

theorem p_op (A : Alg N K) (x : Fin N) {h : List ℕ} {J : Finset ℕ} {B : ℕ → H N K →ₗ[ℂ] H N K}
    (hop : A.node h = .op J B) : ∑ j ∈ J, A.p x (j :: h) = A.p x h := by
  calc ∑ j ∈ J, A.p x (j :: h) = ∑ j ∈ J, ‖B j (A.branch x h)‖ ^ 2 :=
        Finset.sum_congr rfl fun j hj => by rw [p, A.branch_cons_op x hop hj]
    _ = A.p x h := A.sum_norm_sq_kraus hop _

theorem p_root (A : Alg N K) (x : Fin N) : A.p x [] = 1 := by
  simp [p, branch, A.norm_psi0]

theorem Cm_nonneg (A : Alg N K) (h : List ℕ) : 0 ≤ A.Cm h := by
  unfold Cm; positivity

/-- `‖mean‖² ≤ mean of ‖·‖²`. -/
theorem Cm_le_Wm (A : Alg N K) (hN : 1 ≤ N) (h : List ℕ) : A.Cm h ≤ A.Wm h := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  unfold Cm Wm p mean
  rw [norm_smul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]
  have h1 : ‖∑ x, A.branch x h‖ ≤ ∑ x, ‖A.branch x h‖ := norm_sum_le _ _
  have h2 : (∑ x, ‖A.branch x h‖) ^ 2 ≤ (N : ℝ) * ∑ x, ‖A.branch x h‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun x => ‖A.branch x h‖)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have h3 : ‖∑ x, A.branch x h‖ ^ 2 ≤ (N : ℝ) * ∑ x, ‖A.branch x h‖ ^ 2 :=
    le_trans (by gcongr) h2
  calc ((N : ℝ) ^ 2)⁻¹ * ‖∑ x, A.branch x h‖ ^ 2
      ≤ ((N : ℝ) ^ 2)⁻¹ * ((N : ℝ) * ∑ x, ‖A.branch x h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (N : ℝ)⁻¹ * ∑ x, ‖A.branch x h‖ ^ 2 := by
        rw [sq, mul_inv, mul_assoc, inv_mul_cancel_left₀ hN0]

theorem Wm_query (A : Alg N K) {h : List ℕ} (hq : A.node h = .query) : A.Wm (0 :: h) = A.Wm h := by
  simp only [Wm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => A.p_query x hq

theorem Wm_op (A : Alg N K) {h : List ℕ} {J : Finset ℕ} {B : ℕ → H N K →ₗ[ℂ] H N K}
    (hop : A.node h = .op J B) : ∑ j ∈ J, A.Wm (j :: h) = A.Wm h := by
  simp only [Wm]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => A.p_op x hop

/-- Helper: the mean below an operation node. -/
theorem mean_cons_op (A : Alg N K) {h : List ℕ} {J : Finset ℕ} {B : ℕ → H N K →ₗ[ℂ] H N K}
    (hop : A.node h = .op J B) {j : ℕ} (hj : j ∈ J) : A.mean (j :: h) = B j (A.mean h) := by
  simp only [mean, A.branch_cons_op _ hop hj, map_smul, map_sum]

theorem Cm_op (A : Alg N K) {h : List ℕ} {J : Finset ℕ} {B : ℕ → H N K →ₗ[ℂ] H N K}
    (hop : A.node h = .op J B) : ∑ j ∈ J, A.Cm (j :: h) = A.Cm h := by
  calc ∑ j ∈ J, A.Cm (j :: h) = ∑ j ∈ J, ‖B j (A.mean h)‖ ^ 2 :=
        Finset.sum_congr rfl fun j hj => by rw [Cm, A.mean_cons_op hop hj]
    _ = A.Cm h := A.sum_norm_sq_kraus hop _

/-- Helper: the bit flip `(y, b, w) ↦ (y, !b, w)` at every address. -/
def bitflip (i : Idx N K) : Idx N K := (i.1, !i.2.1, i.2.2)

/-- Helper: `bitflip` as a permutation. -/
def bitflipEquiv : Idx N K ≃ Idx N K where
  toFun := bitflip
  invFun := bitflip
  left_inv := fun i => by rcases i with ⟨y, b, w⟩; simp [bitflip]
  right_inv := fun i => by rcases i with ⟨y, b, w⟩; simp [bitflip]

/-- Helper: the unitary of `bitflip`. -/
noncomputable def bitflipOp : H N K ≃ₗᵢ[ℂ] H N K :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (bitflipEquiv (N := N) (K := K))

theorem bitflipOp_apply (v : H N K) (i : Idx N K) : bitflipOp v i = v (bitflip i) := rfl

theorem oracle_apply (x : Fin N) (v : H N K) (i : Idx N K) : oracle x v i = v (flip x i) := rfl

/-- Helper: the vector whose address-`y` block is the address-`y` block of `v y`. -/
noncomputable def diagVec (v : Fin N → H N K) : H N K :=
  WithLp.toLp 2 (fun i : Idx N K => v i.1 i)

theorem diagVec_apply (v : Fin N → H N K) (i : Idx N K) : diagVec v i = v i.1 i := rfl

theorem diagVec_eq_add (v : Fin N → H N K) (m : H N K) :
    diagVec v = m + diagVec (fun x => v x - m) := by
  ext i
  simp [diagVec_apply]

theorem norm_diagVec_sq_le (d : Fin N → H N K) : ‖diagVec d‖ ^ 2 ≤ ∑ x, ‖d x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [diagVec_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun y _ => ?_
  calc ∑ bw : Bool × K, ‖d (y, bw).1 (y, bw)‖ ^ 2 = ∑ bw : Bool × K, ‖d y (y, bw)‖ ^ 2 := rfl
    _ ≤ ∑ y' : Fin N, ∑ bw : Bool × K, ‖d y (y', bw)‖ ^ 2 :=
        Finset.single_le_sum (f := fun y' => ∑ bw : Bool × K, ‖d y (y', bw)‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ y)
    _ = ∑ i : Idx N K, ‖d y i‖ ^ 2 := by rw [Fintype.sum_prod_type]
    _ = ‖d y‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ _).symm

/-- Helper: one oracle call on every branch, summed, is `bitflip` minus identity on `diagVec`. -/
theorem sum_oracle_sub (ψ : Fin N → H N K) :
    ∑ x, (oracle x (ψ x) - ψ x) = bitflipOp (diagVec ψ) - diagVec ψ := by
  ext i
  rcases i with ⟨y, b, w⟩
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply, WithLp.ofLp_sub, Pi.sub_apply,
    oracle_apply, bitflipOp_apply, diagVec_apply]
  rw [Finset.sum_eq_single y]
  · simp [flip, bitflip]
  · intro x _ hx
    simp [flip, Ne.symm hx]
  · simp

/-- Helper: `∑ ‖v x - m‖² = ∑ ‖v x‖² - N ‖m‖²` when `m` is the mean of `v`. -/
theorem sum_norm_sub_sq (v : Fin N → H N K) (m : H N K) (hm : ∑ x, v x = ∑ _x : Fin N, m) :
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

/-- Helper: the real-number step of Lemma s-query. -/
theorem query_bound_aux (hn : (0 : ℝ) < N) {F : H N K ≃ₗᵢ[ℂ] H N K} {μ μ' Ψ G : H N K} {s : ℝ}
    (h1 : μ' = μ + ((N : ℂ)⁻¹) • (F Ψ - Ψ)) (h2 : Ψ = μ + G) (h3 : ‖G‖ ≤ Real.sqrt N * s) :
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

/-- Lemma s-query: one oracle call moves the mean by at most `2√C/N + (2/√N)√(W - C)`. -/
theorem Cm_query (A : Alg N K) (hN : 1 ≤ N) {h : List ℕ} (hq : A.node h = .query) :
    (1 - 2 / (N : ℝ)) * Real.sqrt (A.Cm h) - 2 / Real.sqrt N * Real.sqrt (A.Wm h - A.Cm h)
      ≤ Real.sqrt (A.Cm (0 :: h)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e1 : Real.sqrt (A.Cm h) = ‖A.mean h‖ := by rw [Cm, Real.sqrt_sq (norm_nonneg _)]
  have e2 : Real.sqrt (A.Cm (0 :: h)) = ‖A.mean (0 :: h)‖ := by
    rw [Cm, Real.sqrt_sq (norm_nonneg _)]
  rw [e1, e2]
  have hμ' : A.mean (0 :: h) = A.mean h + ((N : ℂ)⁻¹) •
      (bitflipOp (diagVec fun x => A.branch x h) - diagVec fun x => A.branch x h) := by
    rw [← sum_oracle_sub]
    simp only [mean, A.branch_cons_query _ hq, Finset.sum_sub_distrib, smul_sub]
    abel
  have hS : ∑ _x : Fin N, A.mean h = ∑ x, A.branch x h := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, mean,
      smul_smul, mul_inv_cancel₀ hNc, one_smul]
  have hvar : ∑ x, ‖A.branch x h - A.mean h‖ ^ 2 = N * (A.Wm h - A.Cm h) := by
    rw [sum_norm_sub_sq _ _ hS.symm, Wm, Cm, mul_sub, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
    rfl
  have hG : ‖diagVec (fun x => A.branch x h - A.mean h)‖
      ≤ Real.sqrt N * Real.sqrt (A.Wm h - A.Cm h) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← hvar]
    calc ‖diagVec (fun x => A.branch x h - A.mean h)‖
        = Real.sqrt (‖diagVec (fun x => A.branch x h - A.mean h)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (norm_diagVec_sq_le _)
  exact query_bound_aux hNr hμ' (diagVec_eq_add _ _) hG

/-- Helper for Lemma s-end: for any address `y`, `C ≤ (2/N²) p_y + (2/N) ∑_{x ≠ y} p_x`. -/
theorem Cm_le_single (A : Alg N K) (hN : 1 ≤ N) (h : List ℕ) (y : Fin N) :
    A.Cm h ≤ 2 / (N : ℝ) ^ 2 * A.p y h + 2 / (N : ℝ) * (∑ x, A.p x h - A.p y h) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have hsplit : ∑ x, A.branch x h = A.branch y h + ∑ x ∈ Finset.univ.erase y, A.branch x h :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ y)).symm
  have hpsplit : ∑ x, A.p x h = A.p y h + ∑ x ∈ Finset.univ.erase y, A.p x h :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ y)).symm
  have hR : ‖∑ x ∈ Finset.univ.erase y, A.branch x h‖ ^ 2
      ≤ N * ∑ x ∈ Finset.univ.erase y, A.p x h := by
    have h1 : ‖∑ x ∈ Finset.univ.erase y, A.branch x h‖
        ≤ ∑ x ∈ Finset.univ.erase y, ‖A.branch x h‖ := norm_sum_le _ _
    have h2 : (∑ x ∈ Finset.univ.erase y, ‖A.branch x h‖) ^ 2
        ≤ ((Finset.univ.erase y).card : ℝ) * ∑ x ∈ Finset.univ.erase y, ‖A.branch x h‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ((Finset.univ.erase y).card : ℝ) ≤ N := by
      have : (Finset.univ.erase y).card ≤ N := by simp
      exact_mod_cast this
    have h4 : 0 ≤ ∑ x ∈ Finset.univ.erase y, ‖A.branch x h‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ‖∑ x ∈ Finset.univ.erase y, A.branch x h‖ ^ 2
        ≤ (∑ x ∈ Finset.univ.erase y, ‖A.branch x h‖) ^ 2 := by gcongr
      _ ≤ ((Finset.univ.erase y).card : ℝ) * ∑ x ∈ Finset.univ.erase y, ‖A.branch x h‖ ^ 2 := h2
      _ ≤ N * ∑ x ∈ Finset.univ.erase y, ‖A.branch x h‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h4
      _ = N * ∑ x ∈ Finset.univ.erase y, A.p x h := rfl
  have hC : A.Cm h = ((N : ℝ) ^ 2)⁻¹ *
      ‖A.branch y h + ∑ x ∈ Finset.univ.erase y, A.branch x h‖ ^ 2 := by
    rw [Cm, mean, hsplit, norm_smul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]
  have htri : ‖A.branch y h + ∑ x ∈ Finset.univ.erase y, A.branch x h‖ ^ 2
      ≤ 2 * A.p y h + 2 * ‖∑ x ∈ Finset.univ.erase y, A.branch x h‖ ^ 2 := by
    have h5 : ‖A.branch y h + ∑ x ∈ Finset.univ.erase y, A.branch x h‖ ^ 2
        ≤ (‖A.branch y h‖ + ‖∑ x ∈ Finset.univ.erase y, A.branch x h‖) ^ 2 := by
      gcongr
      exact norm_add_le _ _
    have hp : A.p y h = ‖A.branch y h‖ ^ 2 := rfl
    rw [hp]
    nlinarith [sq_nonneg (‖A.branch y h‖ - ‖∑ x ∈ Finset.univ.erase y, A.branch x h‖)]
  rw [hC, hpsplit]
  have hfin : 2 / (N : ℝ) ^ 2 * A.p y h
      + 2 / (N : ℝ) * (A.p y h + ∑ x ∈ Finset.univ.erase y, A.p x h - A.p y h)
      = ((N : ℝ) ^ 2)⁻¹ * (2 * A.p y h + 2 * (N * ∑ x ∈ Finset.univ.erase y, A.p x h)) := by
    field_simp
    ring
  rw [hfin]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- Lemma s-end, at every node: `C ≤ (2/N²) ∑_x p_x + (2/N) ∑_x (p_x - s_x)`. -/
theorem Cm_end (A : Alg N K) (hN : 1 ≤ N) (h : List ℕ) :
    A.Cm h ≤ 2 / (N : ℝ) ^ 2 * ∑ x, A.p x h + 2 / (N : ℝ) * ∑ x, (A.p x h - A.sx x h) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : ∀ x, 0 ≤ A.p x h := fun x => A.p_nonneg x h
  have hsum0 : 0 ≤ ∑ x, A.p x h := Finset.sum_nonneg fun x _ => hp0 x
  by_cases hh : ∃ y, A.node h = .halt y
  · obtain ⟨y, hy⟩ := hh
    have hsx : ∀ x, A.sx x h = if x = y then A.p y h else 0 := by
      intro x
      by_cases hxy : x = y
      · subst hxy; simp [sx, hy, Node.output]
      · simp [sx, hy, Node.output, Ne.symm hxy, hxy]
    have hs : ∑ x, A.sx x h = A.p y h := by simp [hsx]
    rw [Finset.sum_sub_distrib, hs]
    have hL := A.Cm_le_single hN h y
    have hy' : 2 / (N : ℝ) ^ 2 * A.p y h ≤ 2 / (N : ℝ) ^ 2 * ∑ x, A.p x h :=
      mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun x _ => hp0 x) (Finset.mem_univ y)) (by positivity)
    linarith
  · have hs0 : ∀ x, A.sx x h = 0 := by
      intro x
      unfold sx
      split_ifs with hout
      · exfalso
        apply hh
        cases hn : A.node h <;> simp_all [Node.output]
      · rfl
    simp only [hs0, sub_zero]
    have h1 := A.Cm_le_Wm hN h
    have h2 : A.Wm h ≤ 2 / (N : ℝ) * ∑ x, A.p x h := by
      unfold Wm
      have := mul_nonneg (inv_nonneg.mpr hNr.le) hsum0
      rw [div_eq_mul_inv, mul_assoc]
      linarith
    have h3 : 0 ≤ 2 / (N : ℝ) ^ 2 * ∑ x, A.p x h := mul_nonneg (by positivity) hsum0
    linarith

theorem Cm_root (A : Alg N K) (hN : 1 ≤ N) : A.Cm [] = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hm : A.mean [] = A.psi0 := by
    simp only [mean, branch, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNc, one_smul]
  rw [Cm, hm, A.norm_psi0, one_pow]

theorem Wm_root (A : Alg N K) (hN : 1 ≤ N) : A.Wm [] = 1 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Wm, p_root, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  exact inv_mul_cancel₀ hNr

end Alg

end TheoremS
