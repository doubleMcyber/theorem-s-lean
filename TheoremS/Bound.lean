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
Proof of Theorem S for finite-dimensional adaptive query algorithms (`TheoremSFin`, `TheoremSFin'` of
`TheoremS/Statement.lean`).

The argument is the paper's proof of Theorem S: the potential `κ V(C, W)` of the mean vector pays for each
query (`Vf_query`), does not increase at operation nodes (`Vf_finset_sum`), and is small at the end
(`Cm_end`), where `κ = 2 / arcsin (2/√N)`. Infinite paths are handled by truncating the tree at depth `M`
(`treeG`) and letting `M → ∞` (`tsum_le_iSup_treeR`).
-/
import TheoremS.Potential
import TheoremS.Tree
import TheoremS.Mean

namespace TheoremS

set_option autoImplicit false

open scoped ENNReal

/-! ### Algebra of the real truncated tree sums -/

section treeG

variable (ch : List ℕ → Finset ℕ)

theorem treeG_mono {b₁ b₂ f₁ f₂ : List ℕ → ℝ} (hb : ∀ l, b₁ l ≤ b₂ l) (hf : ∀ l, f₁ l ≤ f₂ l) :
    ∀ M h, treeG ch b₁ f₁ M h ≤ treeG ch b₂ f₂ M h := by
  intro M
  induction M with
  | zero => intro h; exact hb h
  | succ M ih =>
    intro h
    simp only [treeG]
    exact add_le_add (hf h) (Finset.sum_le_sum fun o _ => ih _)

theorem treeG_nonneg {b f : List ℕ → ℝ} (hb : ∀ l, 0 ≤ b l) (hf : ∀ l, 0 ≤ f l) :
    ∀ M h, 0 ≤ treeG ch b f M h := by
  intro M
  induction M with
  | zero => intro h; exact hb h
  | succ M ih =>
    intro h
    simp only [treeG]
    exact add_nonneg (hf h) (Finset.sum_nonneg fun o _ => ih _)

theorem treeG_add (b₁ b₂ f₁ f₂ : List ℕ → ℝ) :
    ∀ M h, treeG ch (b₁ + b₂) (f₁ + f₂) M h = treeG ch b₁ f₁ M h + treeG ch b₂ f₂ M h := by
  intro M
  induction M with
  | zero => intro h; rfl
  | succ M ih =>
    intro h
    simp only [treeG, ih, Pi.add_apply, Finset.sum_add_distrib]
    ring

theorem treeG_sub (b₁ b₂ f₁ f₂ : List ℕ → ℝ) :
    ∀ M h, treeG ch (b₁ - b₂) (f₁ - f₂) M h = treeG ch b₁ f₁ M h - treeG ch b₂ f₂ M h := by
  intro M
  induction M with
  | zero => intro h; rfl
  | succ M ih =>
    intro h
    simp only [treeG, ih, Pi.sub_apply, Finset.sum_sub_distrib]
    ring

theorem treeG_smul (c : ℝ) (b f : List ℕ → ℝ) :
    ∀ M h, treeG ch (c • b) (c • f) M h = c * treeG ch b f M h := by
  intro M
  induction M with
  | zero => intro h; rfl
  | succ M ih =>
    intro h
    simp only [treeG, ih, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring

theorem treeG_sum {ι : Type*} (s : Finset ι) (b f : ι → List ℕ → ℝ) :
    ∀ M h, treeG ch (∑ i ∈ s, b i) (∑ i ∈ s, f i) M h = ∑ i ∈ s, treeG ch (b i) (f i) M h := by
  intro M
  induction M with
  | zero => intro h; simp [treeG]
  | succ M ih =>
    intro h
    simp only [treeG, ih, Finset.sum_apply, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm

end treeG

namespace Alg

variable {N : ℕ} {K : Type} [Fintype K]

/-- A function on histories defined by the kind of node: `q` at query nodes, `o` at operation nodes,
`t` at halt nodes. -/
noncomputable def kindF (A : Alg N K) (q o t : List ℕ → ℝ) (h : List ℕ) : ℝ :=
  match A.node h with
  | .query => q h
  | .op _ _ => o h
  | .halt _ => t h

theorem kindF_query (A : Alg N K) (q o t : List ℕ → ℝ) {h : List ℕ} (hk : A.node h = .query) :
    A.kindF q o t h = q h := by
  simp [kindF, hk]

theorem kindF_op (A : Alg N K) (q o t : List ℕ → ℝ) {h : List ℕ} {J : Finset ℕ}
    {B : ℕ → H N K →ₗ[ℂ] H N K} (hk : A.node h = .op J B) : A.kindF q o t h = o h := by
  simp [kindF, hk]

theorem kindF_halt (A : Alg N K) (q o t : List ℕ → ℝ) {h : List ℕ} {y : Fin N}
    (hk : A.node h = .halt y) : A.kindF q o t h = t h := by
  simp [kindF, hk]

theorem sx_nonneg (A : Alg N K) (x : Fin N) (h : List ℕ) : 0 ≤ A.sx x h := by
  unfold sx; split_ifs
  · exact A.p_nonneg x h
  · exact le_rfl

theorem sx_of_not_halt (A : Alg N K) (x : Fin N) {h : List ℕ} (hk : ∀ y, A.node h ≠ .halt y) :
    A.sx x h = 0 := by
  unfold sx
  split_ifs with he
  · exfalso
    cases hn : A.node h with
    | query => simp [hn, Node.output] at he
    | op J B => simp [hn, Node.output] at he
    | halt y => exact hk y hn
  · rfl

/-- `p x h = ‖ψ_x h‖²` is conserved along the tree: the frontier-plus-halted mass is `p x h`. -/
theorem mass (A : Alg N K) (x : Fin N) :
    ∀ M h, treeG A.ch (A.p x) (A.kindF 0 0 (A.p x)) M h = A.p x h := by
  intro M
  induction M with
  | zero => intro h; rfl
  | succ M ih =>
    intro h
    simp only [treeG]
    cases hk : A.node h with
    | query =>
      rw [A.kindF_query _ _ _ hk, A.ch_query hk, Finset.sum_singleton, ih, A.p_query x hk]
      simp
    | op J B =>
      rw [A.kindF_op _ _ _ hk, A.ch_op hk]
      simp only [ih, Pi.zero_apply, zero_add]
      exact A.p_op x hk
    | halt y =>
      rw [A.kindF_halt _ _ _ hk, A.ch_halt hk, Finset.sum_empty, add_zero]

theorem p_eq_zero_off (A : Alg N K) (x : Fin N) (h : List ℕ) (o : ℕ) (l : List ℕ) (ho : o ∉ A.ch h) :
    A.p x (l ++ o :: h) = 0 := by
  unfold p
  rw [A.branch_append_eq_zero x l (A.branch_cons_eq_zero x ho)]
  simp

theorem ofReal_sx (A : Alg N K) (x : Fin N) (h : List ℕ) :
    ENNReal.ofReal (A.sx x h) = if (A.node h).output = some x then A.prob x h else 0 := by
  unfold sx; split_ifs
  · rfl
  · simp

theorem ofReal_qx (A : Alg N K) (x : Fin N) (h : List ℕ) :
    ENNReal.ofReal (A.kindF (A.p x) 0 0 h) = if (A.node h).isQuery then A.prob x h else 0 := by
  cases hk : A.node h with
  | query => rw [A.kindF_query _ _ _ hk]; simp [Node.isQuery, prob, p]
  | op J B => rw [A.kindF_op _ _ _ hk]; simp [Node.isQuery]
  | halt y => rw [A.kindF_halt _ _ _ hk]; simp [Node.isQuery]

/-- The truncated success probability tends to the success probability. -/
theorem success_le_iSup (A : Alg N K) (x : Fin N) :
    A.success x ≤ ⨆ M, ENNReal.ofReal (treeG A.ch 0 (A.sx x) M []) := by
  have hz : ∀ (h : List ℕ) (o : ℕ) (l : List ℕ), o ∉ A.ch h →
      ENNReal.ofReal (A.sx x (l ++ o :: h)) = 0 := by
    intro h o l ho
    have h1 := A.sx_nonneg x (l ++ o :: h)
    have h2 : A.sx x (l ++ o :: h) ≤ 0 := by
      unfold sx; split_ifs
      · exact (A.p_eq_zero_off x h o l ho).le
      · exact le_rfl
    simp [le_antisymm h2 h1]
  have key := tsum_le_iSup_treeR A.ch (fun l => ENNReal.ofReal (A.sx x l)) hz []
  simp only [List.append_nil] at key
  unfold success
  calc (∑' h : List ℕ, if (A.node h).output = some x then A.prob x h else 0)
      = ∑' h : List ℕ, ENNReal.ofReal (A.sx x h) := by
        congr 1; funext h; rw [A.ofReal_sx]
    _ ≤ ⨆ M, treeR A.ch (fun l => ENNReal.ofReal (A.sx x l)) M [] := key
    _ = ⨆ M, ENNReal.ofReal (treeG A.ch 0 (A.sx x) M []) := by
        congr 1; funext M; rw [ofReal_treeG_zero _ _ (A.sx_nonneg x)]

/-- The truncated expected number of queries is at most the cost. -/
theorem ofReal_query_le_cost (A : Alg N K) (x : Fin N) (M : ℕ) :
    ENNReal.ofReal (treeG A.ch 0 (A.kindF (A.p x) 0 0) M []) ≤ A.cost x := by
  have hq0 : ∀ l, 0 ≤ A.kindF (A.p x) 0 0 l := by
    intro l
    cases hk : A.node l with
    | query => rw [A.kindF_query _ _ _ hk]; exact A.p_nonneg x l
    | op J B => rw [A.kindF_op _ _ _ hk]; exact le_rfl
    | halt y => rw [A.kindF_halt _ _ _ hk]; exact le_rfl
  rw [ofReal_treeG_zero _ _ hq0]
  refine (treeR_le_tsum _ _ M []).trans (le_of_eq ?_)
  unfold cost
  congr 1; funext l; simp only [List.append_nil, A.ofReal_qx]

/-- The potential at a node, `κ V(C, W)` with `κ = 2 / arcsin (2/√N)`. -/
noncomputable def pot (A : Alg N K) (h : List ℕ) : ℝ :=
  2 / Real.arcsin (2 / Real.sqrt N) * Vf (A.Cm h) (A.Wm h)

section main

variable (A : Alg N K) (hN : 4 ≤ N)
include hN

theorem one_le_N : 1 ≤ N := by omega

theorem two_le_sqrt : 2 ≤ Real.sqrt N := by
  have : (4 : ℝ) ≤ N := by exact_mod_cast hN
  calc (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ ≤ Real.sqrt N := Real.sqrt_le_sqrt this

/-- Lemmas s-V and s-query, summed: the potential at `h` is at most the expected number of queries
in the depth-`M` truncation plus the potential at its frontier and halt nodes. -/
theorem pot_le : ∀ M h, A.pot h ≤ treeG A.ch A.pot (A.kindF A.Wm 0 A.pot) M h := by
  have hN1 := one_le_N hN
  have ht := two_le_sqrt hN
  have hκ := kappa_pos _ ht
  intro M
  induction M with
  | zero => intro h; exact le_rfl
  | succ M ih =>
    intro h
    simp only [treeG]
    cases hk : A.node h with
    | query =>
      rw [A.kindF_query _ _ _ hk, A.ch_query hk, Finset.sum_singleton]
      have h1 := ih (0 :: h)
      have hW := A.Wm_query hk
      have hq := A.Cm_query hN1 hk
      have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
      have hstep := Vf_query (Real.sqrt N) (A.Cm h) (A.Wm h) (A.Cm (0 :: h)) ht (A.Cm_nonneg h)
        (A.Cm_le_Wm hN1 h) (A.Cm_nonneg _) (by rw [← hW]; exact A.Cm_le_Wm hN1 _) (by rw [hsq]; exact hq)
      unfold pot at h1 ⊢
      rw [hW] at h1
      linarith
    | op J B =>
      rw [A.kindF_op _ _ _ hk, A.ch_op hk, Pi.zero_apply, zero_add]
      calc A.pot h = 2 / Real.arcsin (2 / Real.sqrt N) *
            Vf (∑ j ∈ J, A.Cm (j :: h)) (∑ j ∈ J, A.Wm (j :: h)) := by
            unfold pot; rw [A.Cm_op hk, A.Wm_op hk]
        _ ≤ 2 / Real.arcsin (2 / Real.sqrt N) * ∑ j ∈ J, Vf (A.Cm (j :: h)) (A.Wm (j :: h)) :=
            mul_le_mul_of_nonneg_left
              (Vf_finset_sum J _ _ (fun j _ => A.Cm_nonneg _) (fun j _ => A.Cm_le_Wm hN1 _)) hκ.le
        _ = ∑ j ∈ J, A.pot (j :: h) := by unfold pot; rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun j _ => ih _
    | halt y =>
      rw [A.kindF_halt _ _ _ hk, A.ch_halt hk, Finset.sum_empty, add_zero]

/-- Lemma s-end, summed: the frontier potential is at most `κγ (2/N + (2/N) ∑_x (1 - s_x^M))`. -/
theorem frontier_le (M : ℕ) :
    treeG A.ch A.pot (A.kindF A.Wm 0 A.pot) M [] ≤
      treeG A.ch 0 (A.kindF A.Wm 0 0) M [] +
        2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) *
          (2 / (N : ℝ) + 2 / (N : ℝ) * ∑ x, (1 - treeG A.ch 0 (A.sx x) M [])) := by
  have hN1 := one_le_N hN
  have ht := two_le_sqrt hN
  have hκ := kappa_pos _ ht
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hκγ0 : 0 ≤ 2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) :=
    mul_nonneg hκ.le (by positivity)
  set κγ := 2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) with hκγ
  -- the end bound, as functions on histories
  set e : Fin N → List ℕ → ℝ := fun x =>
    (2 / (N : ℝ) ^ 2) • A.p x + (2 / (N : ℝ)) • (A.p x - A.sx x) with he
  set fe : Fin N → List ℕ → ℝ := fun x =>
    (2 / (N : ℝ) ^ 2) • A.kindF 0 0 (A.p x) + (2 / (N : ℝ)) • (A.kindF 0 0 (A.p x) - A.sx x) with hfe
  have hend : ∀ l, A.Cm l ≤ (∑ x, e x) l := by
    intro l
    refine (A.Cm_end hN1 l).trans (le_of_eq ?_)
    simp only [he, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- step 1: potential ≤ queries + κγ · C
  have h1 : ∀ M h, treeG A.ch A.pot (A.kindF A.Wm 0 A.pot) M h ≤
      treeG A.ch (0 + κγ • A.Cm) (A.kindF A.Wm 0 0 + κγ • A.kindF 0 0 A.Cm) M h := by
    apply treeG_mono
    · intro l
      simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_add, pot, hκγ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (Vf_le _ _ (A.Cm_nonneg l) (A.Cm_le_Wm hN1 l)) hκ.le
    · intro l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      cases hk : A.node l with
      | query => simp only [A.kindF_query _ _ _ hk, Pi.zero_apply, mul_zero, add_zero, le_refl]
      | op J B => simp only [A.kindF_op _ _ _ hk, Pi.zero_apply, mul_zero, add_zero, le_refl]
      | halt y =>
        simp only [A.kindF_halt _ _ _ hk, Pi.zero_apply, zero_add, pot, hκγ, mul_assoc]
        exact mul_le_mul_of_nonneg_left (Vf_le _ _ (A.Cm_nonneg l) (A.Cm_le_Wm hN1 l)) hκ.le
  -- step 2: C ≤ the end bound, summed over the tree
  have h2 : ∀ M h, treeG A.ch A.Cm (A.kindF 0 0 A.Cm) M h ≤
      treeG A.ch (∑ x, e x) (∑ x, fe x) M h := by
    apply treeG_mono
    · exact hend
    · intro l
      cases hk : A.node l with
      | query =>
        have hs0 : ∀ x, A.sx x l = 0 := fun x => A.sx_of_not_halt x (by simp [hk])
        simp only [A.kindF_query _ _ _ hk, Pi.zero_apply, hfe, Finset.sum_apply, Pi.add_apply,
          Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs0, mul_zero, sub_zero, add_zero,
          Finset.sum_const_zero, le_refl]
      | op J B =>
        have hs0 : ∀ x, A.sx x l = 0 := fun x => A.sx_of_not_halt x (by simp [hk])
        simp only [A.kindF_op _ _ _ hk, Pi.zero_apply, hfe, Finset.sum_apply, Pi.add_apply,
          Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs0, mul_zero, sub_zero, add_zero,
          Finset.sum_const_zero, le_refl]
      | halt y =>
        have hfe_e : (∑ x, fe x) l = (∑ x, e x) l := by
          simp only [he, hfe, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
            smul_eq_mul, A.kindF_halt _ _ _ hk]
        rw [hfe_e, A.kindF_halt _ _ _ hk]
        exact hend l
  -- step 3: evaluate the end bound with mass conservation
  have h3 : ∀ x, treeG A.ch (e x) (fe x) M [] ≤
      2 / (N : ℝ) ^ 2 + 2 / (N : ℝ) * (1 - treeG A.ch 0 (A.sx x) M []) := by
    intro x
    simp only [he, hfe]
    rw [treeG_add, treeG_smul, treeG_smul, treeG_sub, A.mass x, A.p_root x]
    have hs : treeG A.ch 0 (A.sx x) M [] ≤ treeG A.ch (A.sx x) (A.sx x) M [] :=
      treeG_mono _ (fun l => A.sx_nonneg x l) (fun l => le_rfl) M []
    have h2N : 0 ≤ 2 / (N : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hs h2N
    linarith
  have hsum : treeG A.ch (∑ x, e x) (∑ x, fe x) M [] ≤
      2 / (N : ℝ) + 2 / (N : ℝ) * ∑ x, (1 - treeG A.ch 0 (A.sx x) M []) := by
    rw [treeG_sum]
    refine (Finset.sum_le_sum fun x _ => h3 x).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    congr 1
    field_simp
  calc treeG A.ch A.pot (A.kindF A.Wm 0 A.pot) M []
      ≤ treeG A.ch (0 + κγ • A.Cm) (A.kindF A.Wm 0 0 + κγ • A.kindF 0 0 A.Cm) M [] := h1 M []
    _ = treeG A.ch 0 (A.kindF A.Wm 0 0) M [] + κγ * treeG A.ch A.Cm (A.kindF 0 0 A.Cm) M [] := by
        rw [treeG_add, treeG_smul]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left ((h2 M []).trans hsum) hκγ0]

/-- The truncated expected number of queries, averaged over `x`, is at most the average cost. -/
theorem queries_le (M : ℕ) (hD : (∑ x, A.cost x) / (N : ℝ≥0∞) ≠ ⊤) :
    treeG A.ch 0 (A.kindF A.Wm 0 0) M [] ≤ ((∑ x, A.cost x) / (N : ℝ≥0∞)).toReal := by
  have hN1 := one_le_N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq0 : ∀ x l, 0 ≤ A.kindF (A.p x) 0 0 l := by
    intro x l
    cases hk : A.node l with
    | query => rw [A.kindF_query _ _ _ hk]; exact A.p_nonneg x l
    | op J B => rw [A.kindF_op _ _ _ hk]; exact le_rfl
    | halt y => rw [A.kindF_halt _ _ _ hk]; exact le_rfl
  have hle : treeG A.ch 0 (A.kindF A.Wm 0 0) M [] ≤
      treeG A.ch ((N : ℝ)⁻¹ • ∑ x : Fin N, (0 : List ℕ → ℝ))
        ((N : ℝ)⁻¹ • ∑ x, A.kindF (A.p x) 0 0) M [] := by
    apply treeG_mono
    · intro l; simp
    · intro l
      cases hk : A.node l with
      | query =>
        simp only [A.kindF_query _ _ _ hk, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Wm, le_refl]
      | op J B =>
        simp only [A.kindF_op _ _ _ hk, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.zero_apply,
          Finset.sum_const_zero, mul_zero, le_refl]
      | halt y =>
        simp only [A.kindF_halt _ _ _ hk, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.zero_apply,
          Finset.sum_const_zero, mul_zero, le_refl]
  rw [treeG_smul, treeG_sum] at hle
  refine hle.trans ?_
  rw [← ENNReal.ofReal_le_iff_le_toReal hD]
  have hnn : ∀ x, 0 ≤ treeG A.ch 0 (A.kindF (A.p x) 0 0) M [] :=
    fun x => treeG_nonneg _ (fun _ => le_rfl) (hq0 x) M []
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun x _ => hnn x),
    ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
  gcongr with x
  exact A.ofReal_query_le_cost x M

theorem average_bound (hA : A.ZeroError) :
    ENNReal.ofReal (2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / (N : ℝ)))
      ≤ (∑ x, A.cost x) / (N : ℝ≥0∞) := by
  have hN1 := one_le_N hN
  have ht := two_le_sqrt hN
  have hκ := kappa_pos _ ht
  have hγ0 : (0 : ℝ) < Real.pi / 8 + 1 / 4 := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  by_cases hD : (∑ x, A.cost x) / (N : ℝ≥0∞) = ⊤
  · rw [hD]; exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal hD]
  -- for every depth M: κγ ≤ D + κγ (2/N + (2/N) ∑_x (1 - s_x^M))
  have hM : ∀ M, 2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) ≤
      ((∑ x, A.cost x) / (N : ℝ≥0∞)).toReal + 2 / Real.arcsin (2 / Real.sqrt N) *
        (Real.pi / 8 + 1 / 4) * (2 / (N : ℝ) + 2 / (N : ℝ) * ∑ x, (1 - treeG A.ch 0 (A.sx x) M [])) := by
    intro M
    have hroot : A.pot [] = 2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) := by
      unfold pot; rw [A.Cm_root hN1, A.Wm_root hN1, Vf_self 1 zero_le_one, mul_one]
    have h1 := (A.pot_le hN M []).trans (A.frontier_le hN M)
    have hq := A.queries_le hN M hD
    rw [hroot] at h1
    linarith
  -- the truncated success probabilities tend to 1
  have hR : ∀ ε > 0, ∃ M, ∀ x, 1 - ε < treeG A.ch 0 (A.sx x) M [] := by
    intro ε hε
    have hx : ∀ x, ∃ M, 1 - ε < treeG A.ch 0 (A.sx x) M [] := by
      intro x
      have h1 : (1 : ℝ≥0∞) ≤ ⨆ M, ENNReal.ofReal (treeG A.ch 0 (A.sx x) M []) := by
        have hs := A.success_le_iSup x
        rwa [hA x] at hs
      have hlt : ENNReal.ofReal (1 - ε) < ⨆ M, ENNReal.ofReal (treeG A.ch 0 (A.sx x) M []) :=
        lt_of_lt_of_le (by rw [ENNReal.ofReal_lt_one]; linarith) h1
      obtain ⟨M, hM⟩ := lt_iSup_iff.1 hlt
      exact ⟨M, (ENNReal.ofReal_lt_ofReal_iff'.1 hM).1⟩
    choose Mx hMx using hx
    refine ⟨Finset.univ.sup Mx, fun x => ?_⟩
    have hle : Mx x ≤ Finset.univ.sup Mx := Finset.le_sup (Finset.mem_univ x)
    have hnn : ∀ M, 0 ≤ treeG A.ch 0 (A.sx x) M [] :=
      fun M => treeG_nonneg _ (fun _ => le_rfl) (A.sx_nonneg x) M []
    have hm : treeR A.ch (fun l => ENNReal.ofReal (A.sx x l)) (Mx x) [] ≤
        treeR A.ch (fun l => ENNReal.ofReal (A.sx x l)) (Finset.univ.sup Mx) [] :=
      treeR_mono A.ch _ [] hle
    rw [← ofReal_treeG_zero _ _ (A.sx_nonneg x), ← ofReal_treeG_zero _ _ (A.sx_nonneg x)] at hm
    exact lt_of_lt_of_le (hMx x) ((ENNReal.ofReal_le_ofReal_iff (hnn _)).1 hm)
  -- conclude with ε → 0
  generalize 2 / Real.arcsin (2 / Real.sqrt N) = κ at hM hκ ⊢
  generalize Real.pi / 8 + 1 / 4 = γ at hM hγ0 ⊢
  generalize ((∑ x, A.cost x) / (N : ℝ≥0∞)).toReal = D at hM ⊢
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 < κ * γ * (2 / (N : ℝ)) := mul_pos (mul_pos hκ hγ0) (div_pos two_pos hNpos)
  have hc0 := hc.ne'
  obtain ⟨M, hMx⟩ := hR (ε / (κ * γ * (2 / (N : ℝ))) / N) (div_pos (div_pos hε hc) hNpos)
  have hsum : ∑ x, (1 - treeG A.ch 0 (A.sx x) M []) ≤ ε / (κ * γ * (2 / (N : ℝ))) := by
    calc ∑ x, (1 - treeG A.ch 0 (A.sx x) M [])
        ≤ ∑ _x : Fin N, ε / (κ * γ * (2 / (N : ℝ))) / N :=
          Finset.sum_le_sum fun x _ => by linarith [hMx x]
      _ = ε / (κ * γ * (2 / (N : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have h2 : κ * γ * (2 / (N : ℝ)) * ∑ x, (1 - treeG A.ch 0 (A.sx x) M []) ≤ ε := by
    calc _ ≤ κ * γ * (2 / (N : ℝ)) * (ε / (κ * γ * (2 / (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsum hc.le
      _ = ε := by field_simp
  linarith [hM M]

end main

end Alg

theorem theoremSFin : TheoremSFin := by
  intro N hN K _ A hA
  exact A.average_bound hN hA

theorem theoremSFin' : TheoremSFin' := by
  intro N hN K _ A hA
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (theoremSFin N hN K A hA)
  have ht := Alg.two_le_sqrt (N := N) hN
  have h := kappa_end (Real.sqrt N) ht
  have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  rw [hsq] at h
  linarith

end TheoremS
