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
Proof of Theorem S for the countable model (`TheoremSInf`, `TheoremSInf'` of
`TheoremS/Inf/Statement.lean`).

The argument is the one of `TheoremS/Bound.lean`, with `κ = 2 / arcsin (2/√N)`, `γ = π/8 + 1/4`,
`pot h = κ V(C h, W h)`, and all tree sums in `ℝ≥0∞` (`treeE`, countably many children):
1. the potential pays for each query (`Vf_query`, `Cm_query`) and does not increase at operation
   nodes (`Vf_hasSum`, countable subadditivity), so `κγ = pot [] ≤` truncated queries + frontier;
2. at the frontier `pot ≤ κγ C` and `C ≤ (2/N²) ∑ p + (2/N) ∑ (p - s)` (`Cm_end`), and `p` is conserved;
3. the truncated queries are at most `(∑ x, cost x) / N`;
4. the truncated success probabilities tend to `success x = 1` (`tsum_le_iSup_treeE`);
5. an `ε`-argument in `ℝ` as in `average_bound` of `TheoremS/Bound.lean`.
`SeparableSpace K` is not used.
-/
import TheoremS.Inf.Statement
import TheoremS.Inf.Mean
import TheoremS.Inf.Tree
import TheoremS.Inf.Potential

namespace TheoremS.Inf

set_option autoImplicit false

open scoped ENNReal
open TheoremS

/-- `κγ = (2 / arcsin (2/√N)) (π/8 + 1/4)`. -/
noncomputable def kgI (N : ℕ) : ℝ := 2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4)

/-- `κγ · 2/N²`. -/
noncomputable def caI (N : ℕ) : ℝ := kgI N * (2 / (N : ℝ) ^ 2)

/-- `κγ · 2/N`. -/
noncomputable def ccI (N : ℕ) : ℝ := kgI N * (2 / (N : ℝ))

theorem sqrtN_ge_two {N : ℕ} (hN : 4 ≤ N) : 2 ≤ Real.sqrt N := by
  have : (4 : ℝ) ≤ N := by exact_mod_cast hN
  calc (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ ≤ Real.sqrt N := Real.sqrt_le_sqrt this

theorem kgI_pos {N : ℕ} (hN : 4 ≤ N) : 0 < kgI N :=
  mul_pos (kappa_pos _ (sqrtN_ge_two hN)) (by positivity)

namespace Alg

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Functions on histories -/

/-- A function on histories defined by the kind of node: `q` at query nodes, `o` at operation nodes,
`t` at halt nodes. -/
noncomputable def kindE (A : Alg N K) (q o t : List ℕ → ℝ≥0∞) (h : List ℕ) : ℝ≥0∞ :=
  match A.node h with
  | .query => q h
  | .op _ _ => o h
  | .halt _ => t h

theorem kindE_query (A : Alg N K) (q o t : List ℕ → ℝ≥0∞) {h : List ℕ} (hk : A.node h = .query) :
    A.kindE q o t h = q h := by
  simp [kindE, hk]

theorem kindE_op (A : Alg N K) (q o t : List ℕ → ℝ≥0∞) {h : List ℕ} {J : Set ℕ}
    {B : ℕ → H N K →L[ℂ] H N K} (hk : A.node h = .op J B) : A.kindE q o t h = o h := by
  simp [kindE, hk]

theorem kindE_halt (A : Alg N K) (q o t : List ℕ → ℝ≥0∞) {h : List ℕ} {y : Fin N}
    (hk : A.node h = .halt y) : A.kindE q o t h = t h := by
  simp [kindE, hk]

/-- The potential at a node, `κ V(C, W)` with `κ = 2 / arcsin (2/√N)`. -/
noncomputable def pot (A : Alg N K) (h : List ℕ) : ℝ :=
  2 / Real.arcsin (2 / Real.sqrt N) * Vf (A.Cm h) (A.Wm h)

noncomputable def potE (A : Alg N K) (h : List ℕ) : ℝ≥0∞ := ENNReal.ofReal (A.pot h)

noncomputable def WE (A : Alg N K) (h : List ℕ) : ℝ≥0∞ := ENNReal.ofReal (A.Wm h)

noncomputable def PE (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ≥0∞ := ENNReal.ofReal (A.p x h)

noncomputable def QE (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (A.p x h - A.sx x h)

noncomputable def SE (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ≥0∞ := ENNReal.ofReal (A.sx x h)

/-- `p_x` at query nodes, `0` elsewhere. -/
noncomputable def qE (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ≥0∞ := A.kindE (A.PE x) 0 0 h

/-- The end bound for item `x`, times `κγ`. -/
noncomputable def eF (A : Alg N K) (x : Fin N) : List ℕ → ℝ≥0∞ :=
  (fun l => ENNReal.ofReal (caI N) * A.PE x l) + (fun l => ENNReal.ofReal (ccI N) * A.QE x l)

/-- The end bound for item `x` at halt nodes, `0` elsewhere. -/
noncomputable def fF (A : Alg N K) (x : Fin N) : List ℕ → ℝ≥0∞ :=
  (fun l => ENNReal.ofReal (caI N) * A.kindE 0 0 (A.PE x) l) +
    (fun l => ENNReal.ofReal (ccI N) * A.kindE 0 0 (A.QE x) l)

/-- The truncated unfinished mass `∑ (p_x - s_x)` of item `x` at depth `M`. -/
noncomputable def Rq (A : Alg N K) (x : Fin N) (M : ℕ) : ℝ≥0∞ :=
  treeE A.ch (A.QE x) (A.kindE 0 0 (A.QE x)) M []

/-- The truncated success probability of item `x` at depth `M`. -/
noncomputable def St (A : Alg N K) (x : Fin N) (M : ℕ) : ℝ≥0∞ := treeE A.ch 0 (A.SE x) M []

/-! ### Elementary facts -/

theorem sx_nonneg (A : Alg N K) (x : Fin N) (h : List ℕ) : 0 ≤ A.sx x h := by
  unfold sx; split_ifs
  · exact A.p_nonneg x h
  · exact le_rfl

theorem sx_le_p (A : Alg N K) (x : Fin N) (h : List ℕ) : A.sx x h ≤ A.p x h := by
  unfold sx; split_ifs
  · exact le_rfl
  · exact A.p_nonneg x h

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

theorem pot_nonneg (A : Alg N K) (hN : 4 ≤ N) (h : List ℕ) : 0 ≤ A.pot h :=
  mul_nonneg (kappa_pos _ (sqrtN_ge_two hN)).le
    (Vf_nonneg _ _ (A.Cm_nonneg h) (A.Cm_le_Wm (by omega) h))

theorem potE_root (A : Alg N K) (hN : 4 ≤ N) : A.potE [] = ENNReal.ofReal (kgI N) := by
  have hN1 : 1 ≤ N := by omega
  unfold potE pot kgI
  rw [A.Cm_root hN1, A.Wm_root hN1, Vf_self 1 zero_le_one, mul_one]

theorem PE_root (A : Alg N K) (x : Fin N) : A.PE x [] = 1 := by
  unfold PE
  rw [A.p_root x, ENNReal.ofReal_one]

/-! ### Step 1: the potential is superharmonic up to the query term -/

theorem pot_super (A : Alg N K) (hN : 4 ≤ N) (h : List ℕ) :
    A.potE h ≤ A.kindE A.WE 0 A.potE h + ∑' o : A.ch h, A.potE (o :: h) := by
  have hN1 : 1 ≤ N := by omega
  have ht := sqrtN_ge_two hN
  have hκ := kappa_pos _ ht
  cases hk : A.node h with
  | query =>
    rw [A.kindE_query _ _ _ hk, A.ch_query hk, tsum_singleton (0 : ℕ) (fun o => A.potE (o :: h))]
    have hW := A.Wm_query hk
    have hq := A.Cm_query hN1 hk
    have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
    have hstep := Vf_query (Real.sqrt N) (A.Cm h) (A.Wm h) (A.Cm (0 :: h)) ht (A.Cm_nonneg h)
      (A.Cm_le_Wm hN1 h) (A.Cm_nonneg _) (by rw [← hW]; exact A.Cm_le_Wm hN1 _) (by rw [hsq]; exact hq)
    have hreal : A.pot h ≤ A.Wm h + A.pot (0 :: h) := by
      unfold pot
      rw [hW]
      linarith
    exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le
  | op J B =>
    rw [A.kindE_op _ _ _ hk, A.ch_op hk, Pi.zero_apply, zero_add]
    have hv := Vf_hasSum (fun j : J => A.Cm ((j : ℕ) :: h)) (fun j : J => A.Wm ((j : ℕ) :: h))
      (fun j => A.Cm_nonneg _) (fun j => A.Cm_le_Wm hN1 _) (A.Cm_op hk) (A.Wm_op hk)
    have hsum : Summable (fun j : J => A.pot ((j : ℕ) :: h)) :=
      hv.1.mul_left (2 / Real.arcsin (2 / Real.sqrt N))
    have hle : A.pot h ≤ ∑' j : J, A.pot ((j : ℕ) :: h) := by
      unfold pot
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left hv.2 hκ.le
    calc A.potE h ≤ ENNReal.ofReal (∑' j : J, A.pot ((j : ℕ) :: h)) := ENNReal.ofReal_le_ofReal hle
      _ = ∑' j : J, A.potE ((j : ℕ) :: h) :=
          ENNReal.ofReal_tsum_of_nonneg (fun j => A.pot_nonneg hN _) hsum
  | halt y =>
    rw [A.kindE_halt _ _ _ hk]
    exact le_self_add

/-! ### Step 2: the frontier -/

theorem potE_le_eF (A : Alg N K) (hN : 4 ≤ N) (l : List ℕ) : A.potE l ≤ ∑ x, A.eF x l := by
  have hN1 : 1 ≤ N := by omega
  have hκ := kappa_pos _ (sqrtN_ge_two hN)
  have hkg := kgI_pos hN
  have hca : 0 ≤ caI N := mul_nonneg hkg.le (by positivity)
  have hcc : 0 ≤ ccI N := mul_nonneg hkg.le (by positivity)
  have hreal : A.pot l ≤ ∑ x, (caI N * A.p x l + ccI N * (A.p x l - A.sx x l)) := by
    have h1 : A.pot l ≤ kgI N * A.Cm l := by
      unfold pot kgI
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Vf_le _ _ (A.Cm_nonneg l) (A.Cm_le_Wm hN1 l)) hκ.le
    have h2 := mul_le_mul_of_nonneg_left (A.Cm_end hN1 l) hkg.le
    refine h1.trans (h2.trans (le_of_eq ?_))
    unfold caI ccI
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hnn : ∀ x, 0 ≤ caI N * A.p x l + ccI N * (A.p x l - A.sx x l) := fun x =>
    add_nonneg (mul_nonneg hca (A.p_nonneg x l)) (mul_nonneg hcc (sub_nonneg.2 (A.sx_le_p x l)))
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hnn x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_add (mul_nonneg hca (A.p_nonneg x l))
    (mul_nonneg hcc (sub_nonneg.2 (A.sx_le_p x l))), ENNReal.ofReal_mul hca,
    ENNReal.ofReal_mul hcc]
  rfl

/-- `p_x` is conserved along the tree. -/
theorem mass (A : Alg N K) (x : Fin N) (M : ℕ) (h : List ℕ) :
    treeE A.ch (A.PE x) (A.kindE 0 0 (A.PE x)) M h = A.PE x h := by
  refine treeE_conserve _ _ _ (fun h => ?_) M h
  cases hk : A.node h with
  | query =>
    rw [A.kindE_query _ _ _ hk, A.ch_query hk, tsum_singleton (0 : ℕ) (fun o => A.PE x (o :: h)),
      Pi.zero_apply, zero_add]
    unfold PE
    rw [A.p_query x hk]
  | op J B =>
    rw [A.kindE_op _ _ _ hk, A.ch_op hk, Pi.zero_apply, zero_add]
    unfold PE
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun j : J => A.p x ((j : ℕ) :: h))
      (fun j => A.p_nonneg x _) (A.p_op x hk).summable, (A.p_op x hk).tsum_eq]
  | halt y =>
    rw [A.kindE_halt _ _ _ hk, A.ch_halt hk, tsum_empty, add_zero]

theorem PE_split (A : Alg N K) (x : Fin N) : A.PE x = A.QE x + A.SE x := by
  funext l
  rw [Pi.add_apply]
  unfold PE QE SE
  rw [← ENNReal.ofReal_add (sub_nonneg.2 (A.sx_le_p x l)) (A.sx_nonneg x l), sub_add_cancel]

theorem kindE_PE_split (A : Alg N K) (x : Fin N) :
    A.kindE 0 0 (A.PE x) = A.kindE 0 0 (A.QE x) + A.SE x := by
  funext l
  rw [Pi.add_apply]
  cases hk : A.node l with
  | query =>
    rw [A.kindE_query _ _ _ hk, A.kindE_query _ _ _ hk, Pi.zero_apply, zero_add]
    unfold SE
    rw [A.sx_of_not_halt x (by simp [hk]), ENNReal.ofReal_zero]
  | op J B =>
    rw [A.kindE_op _ _ _ hk, A.kindE_op _ _ _ hk, Pi.zero_apply, zero_add]
    unfold SE
    rw [A.sx_of_not_halt x (by simp [hk]), ENNReal.ofReal_zero]
  | halt y =>
    rw [A.kindE_halt _ _ _ hk, A.kindE_halt _ _ _ hk]
    exact congrFun (A.PE_split x) l

/-- Unfinished plus halted-with-`x` mass is at most `p_x [] = 1`. -/
theorem trunc_le (A : Alg N K) (x : Fin N) (M : ℕ) : A.Rq x M + A.St x M ≤ 1 := by
  calc A.Rq x M + A.St x M
      ≤ treeE A.ch (A.QE x) (A.kindE 0 0 (A.QE x)) M [] + treeE A.ch (A.SE x) (A.SE x) M [] :=
        add_le_add le_rfl (treeE_mono _ (fun l => by simp) (fun l => le_rfl) M [])
    _ = treeE A.ch (A.QE x + A.SE x) (A.kindE 0 0 (A.QE x) + A.SE x) M [] :=
        (treeE_add _ _ _ _ _ M []).symm
    _ = treeE A.ch (A.PE x) (A.kindE 0 0 (A.PE x)) M [] := by
        rw [← A.PE_split x, ← A.kindE_PE_split x]
    _ = 1 := by rw [A.mass x M [], A.PE_root x]

/-! ### Step 3: queries -/

theorem qE_eq (A : Alg N K) (x : Fin N) (l : List ℕ) :
    A.qE x l = if (A.node l).isQuery then A.prob x l else 0 := by
  unfold qE
  cases hk : A.node l with
  | query => rw [A.kindE_query _ _ _ hk]; simp [Node.isQuery, PE, prob, p]
  | op J B => rw [A.kindE_op _ _ _ hk]; simp [Node.isQuery]
  | halt y => rw [A.kindE_halt _ _ _ hk]; simp [Node.isQuery]

/-- The truncated expected number of queries, averaged over `x`, is at most the average cost. -/
theorem queries_le (A : Alg N K) (hN : 4 ≤ N) (M : ℕ) :
    treeE A.ch 0 (A.kindE A.WE 0 0) M [] ≤ (∑ x, A.cost x) / (N : ℝ≥0∞) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hle : treeE A.ch 0 (A.kindE A.WE 0 0) M [] ≤
      treeE A.ch (fun l => (N : ℝ≥0∞)⁻¹ * (0 : List ℕ → ℝ≥0∞) l)
        (fun l => (N : ℝ≥0∞)⁻¹ * (∑ x, A.qE x) l) M [] := by
    apply treeE_mono
    · intro l; simp
    · intro l
      simp only [Finset.sum_apply]
      cases hk : A.node l with
      | query =>
        unfold qE
        simp only [A.kindE_query _ _ _ hk]
        unfold WE Wm PE
        rw [ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg N)), ENNReal.ofReal_inv_of_pos hNpos,
          ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg (fun x _ => A.p_nonneg x l)]
      | op J B => rw [A.kindE_op _ _ _ hk]; exact zero_le
      | halt y => rw [A.kindE_halt _ _ _ hk]; exact zero_le
  rw [treeE_const_mul A.ch ((N : ℝ≥0∞)⁻¹) 0 (∑ x, A.qE x)] at hle
  refine hle.trans ?_
  rw [ENNReal.div_eq_inv_mul]
  gcongr
  refine (treeE_zero_le_tsum _ _ M []).trans (le_of_eq ?_)
  simp only [List.append_nil, Finset.sum_apply]
  rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold cost
  exact tsum_congr fun l => A.qE_eq x l

/-! ### Step 4: success -/

theorem success_le_iSup (A : Alg N K) (x : Fin N) : A.success x ≤ ⨆ M, A.St x M := by
  have hz : ∀ (h : List ℕ) (o : ℕ) (l : List ℕ), o ∉ A.ch h → A.SE x (l ++ o :: h) = 0 := by
    intro h o l ho
    unfold SE sx
    split_ifs
    · rw [A.p_eq_zero_off x h o l ho, ENNReal.ofReal_zero]
    · exact ENNReal.ofReal_zero
  have key := tsum_le_iSup_treeE A.ch (A.SE x) hz []
  simp only [List.append_nil] at key
  refine le_trans (le_of_eq ?_) key
  unfold success
  exact tsum_congr fun h => (A.ofReal_sx x h).symm

/-! ### Step 5: assembly -/

theorem key (A : Alg N K) (hN : 4 ≤ N) (M : ℕ) :
    ENNReal.ofReal (kgI N) ≤ (∑ x, A.cost x) / (N : ℝ≥0∞) +
      ∑ x, (ENNReal.ofReal (caI N) + ENNReal.ofReal (ccI N) * A.Rq x M) := by
  have h1 : A.potE [] ≤ treeE A.ch A.potE (A.kindE A.WE 0 A.potE) M [] :=
    treeE_super _ _ _ (A.pot_super hN) M []
  have h2 : treeE A.ch A.potE (A.kindE A.WE 0 A.potE) M [] ≤
      treeE A.ch (0 + ∑ x, A.eF x) (A.kindE A.WE 0 0 + ∑ x, A.fF x) M [] := by
    apply treeE_mono
    · intro l
      simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply]
      exact A.potE_le_eF hN l
    · intro l
      simp only [Pi.add_apply, Finset.sum_apply]
      cases hk : A.node l with
      | query =>
        simp only [A.kindE_query _ _ _ hk]
        exact le_self_add
      | op J B =>
        simp only [A.kindE_op _ _ _ hk, Pi.zero_apply, zero_add]
        exact zero_le
      | halt y =>
        simp only [A.kindE_halt _ _ _ hk, Pi.zero_apply, zero_add]
        have hfe : ∀ x, A.fF x l = A.eF x l := fun x => by
          unfold fF eF
          simp only [Pi.add_apply, A.kindE_halt _ _ _ hk]
        simp only [hfe]
        exact A.potE_le_eF hN l
  have h3 : ∀ x, treeE A.ch (A.eF x) (A.fF x) M [] =
      ENNReal.ofReal (caI N) + ENNReal.ofReal (ccI N) * A.Rq x M := by
    intro x
    unfold eF fF
    rw [treeE_add, treeE_const_mul, treeE_const_mul, A.mass x M [], A.PE_root x, mul_one]
    rfl
  rw [treeE_add, treeE_finset_sum] at h2
  simp only [h3] at h2
  rw [← A.potE_root hN]
  exact h1.trans (h2.trans (add_le_add (A.queries_le hN M) le_rfl))

theorem average_bound (A : Alg N K) (hN : 4 ≤ N) (hA : A.ZeroError) :
    ENNReal.ofReal (2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / (N : ℝ)))
      ≤ (∑ x, A.cost x) / (N : ℝ≥0∞) := by
  have hkg := kgI_pos hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hca : 0 ≤ caI N := mul_nonneg hkg.le (by positivity)
  have hcc : 0 ≤ ccI N := mul_nonneg hkg.le (by positivity)
  by_cases hD : (∑ x, A.cost x) / (N : ℝ≥0∞) = ⊤
  · rw [hD]; exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal hD]
  change kgI N * (1 - 2 / (N : ℝ)) ≤ _
  have hRt : ∀ x M, A.Rq x M ≠ ⊤ := fun x M =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans (A.trunc_le x M))
  have hSt : ∀ x M, A.St x M ≠ ⊤ := fun x M =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans (A.trunc_le x M))
  -- for every depth M: κγ ≤ D + κγ (2/N + (2/N) ∑_x (1 - s_x^M))
  have hM : ∀ M, kgI N ≤ ((∑ x, A.cost x) / (N : ℝ≥0∞)).toReal +
      kgI N * (2 / (N : ℝ) + 2 / (N : ℝ) * ∑ x, (1 - (A.St x M).toReal)) := by
    intro M
    have hterm : ∀ x, ENNReal.ofReal (caI N) + ENNReal.ofReal (ccI N) * A.Rq x M ≠ ⊤ := fun x =>
      ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hRt x M)⟩
    have hsum : ∑ x, (ENNReal.ofReal (caI N) + ENNReal.ofReal (ccI N) * A.Rq x M) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun x _ => hterm x
    have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hD, hsum⟩) (A.key hN M)
    rw [ENNReal.toReal_ofReal hkg.le, ENNReal.toReal_add hD hsum,
      ENNReal.toReal_sum fun x _ => hterm x] at h1
    have h2 : ∀ x, (ENNReal.ofReal (caI N) + ENNReal.ofReal (ccI N) * A.Rq x M).toReal ≤
        caI N + ccI N * (1 - (A.St x M).toReal) := by
      intro x
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hRt x M)),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hca, ENNReal.toReal_ofReal hcc]
      have h4 := ENNReal.toReal_mono ENNReal.one_ne_top (A.trunc_le x M)
      rw [ENNReal.toReal_add (hRt x M) (hSt x M), ENNReal.toReal_one] at h4
      have h5 : (A.Rq x M).toReal ≤ 1 - (A.St x M).toReal := by linarith
      have := mul_le_mul_of_nonneg_left h5 hcc
      linarith
    have h5 : ∑ x, (ENNReal.ofReal (caI N) + ENNReal.ofReal (ccI N) * A.Rq x M).toReal ≤
        ∑ x : Fin N, (caI N + ccI N * (1 - (A.St x M).toReal)) :=
      Finset.sum_le_sum fun x _ => h2 x
    have h6 : ∑ x : Fin N, (caI N + ccI N * (1 - (A.St x M).toReal)) =
        kgI N * (2 / (N : ℝ) + 2 / (N : ℝ) * ∑ x, (1 - (A.St x M).toReal)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum]
      unfold caI ccI
      field_simp
    linarith
  -- the truncated success probabilities tend to 1
  have hR : ∀ ε > 0, ∃ M, ∀ x, 1 - ε < (A.St x M).toReal := by
    intro ε hε
    have hx : ∀ x, ∃ M, 1 - ε < (A.St x M).toReal := by
      intro x
      have h1 : (1 : ℝ≥0∞) ≤ ⨆ M, A.St x M := by
        have hs := A.success_le_iSup x
        rwa [hA x] at hs
      have hlt : ENNReal.ofReal (1 - ε) < ⨆ M, A.St x M :=
        lt_of_lt_of_le (by rw [ENNReal.ofReal_lt_one]; linarith) h1
      obtain ⟨M, hM⟩ := lt_iSup_iff.1 hlt
      refine ⟨M, ?_⟩
      have h2 := ENNReal.toReal_strict_mono (hSt x M) hM
      rw [ENNReal.toReal_ofReal'] at h2
      exact lt_of_le_of_lt (le_max_left _ _) h2
    choose Mx hMx using hx
    refine ⟨Finset.univ.sup Mx, fun x => ?_⟩
    have hle : Mx x ≤ Finset.univ.sup Mx := Finset.le_sup (Finset.mem_univ x)
    exact lt_of_lt_of_le (hMx x)
      (ENNReal.toReal_mono (hSt x _) (treeE_zero_mono A.ch (A.SE x) [] hle))
  -- conclude with ε → 0
  generalize kgI N = κ at hM hkg ⊢
  generalize ((∑ x, A.cost x) / (N : ℝ≥0∞)).toReal = D at hM ⊢
  have hκ0 : κ ≠ 0 := hkg.ne'
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 < κ * (2 / (N : ℝ)) := mul_pos hkg (div_pos two_pos hNpos)
  have hc0 := hc.ne'
  obtain ⟨M, hMx⟩ := hR (ε / (κ * (2 / (N : ℝ))) / N) (div_pos (div_pos hε hc) hNpos)
  have hsum : ∑ x, (1 - (A.St x M).toReal) ≤ ε / (κ * (2 / (N : ℝ))) := by
    calc ∑ x, (1 - (A.St x M).toReal)
        ≤ ∑ _x : Fin N, ε / (κ * (2 / (N : ℝ))) / N :=
          Finset.sum_le_sum fun x _ => by linarith [hMx x]
      _ = ε / (κ * (2 / (N : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have h2 : κ * (2 / (N : ℝ)) * ∑ x, (1 - (A.St x M).toReal) ≤ ε := by
    calc _ ≤ κ * (2 / (N : ℝ)) * (ε / (κ * (2 / (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsum hc.le
      _ = ε := by field_simp
  linarith [hM M]

end Alg

theorem theoremSInf : TheoremSInf := by
  intro N hN K _ _ _ _ A hA
  exact A.average_bound hN hA

theorem theoremSInf' : TheoremSInf' := by
  intro N hN K _ _ _ _ A hA
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (theoremSInf N hN K A hA)
  have ht := sqrtN_ge_two hN
  have h := kappa_end (Real.sqrt N) ht
  have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  rw [hsq] at h
  linarith

end TheoremS.Inf
