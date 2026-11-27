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
Truncated sums over a tree of histories with countably many children (Mathlib only, nothing about
quantum algorithms).

Histories are `List ℕ`, newest outcome first; `ch h : Set ℕ` is the (possibly infinite) set of outcomes
allowed after `h`. `treeE ch b f M h` is the `ℝ≥0∞` tree sum of the node term `f` over the nodes of depth
`< M` below `h`, plus the frontier term `b` at depth `M`. `tsum_list_decomp`, `tr_succ` and `tr_le_tsum`
are as in `TheoremS/Tree.lean`.
-/
import Mathlib

namespace TheoremS.Inf

set_option autoImplicit false

open scoped ENNReal

/-- Tree sum with frontier term `b` at depth `M` and node term `f`, countably many children. -/
noncomputable def treeE (ch : List ℕ → Set ℕ) (b f : List ℕ → ℝ≥0∞) : ℕ → List ℕ → ℝ≥0∞
  | 0, h => b h
  | M + 1, h => f h + ∑' o : ch h, treeE ch b f M (o :: h)

/-! ### Algebraic properties -/

theorem treeE_mono (ch : List ℕ → Set ℕ) {b₁ b₂ f₁ f₂ : List ℕ → ℝ≥0∞}
    (hb : ∀ l, b₁ l ≤ b₂ l) (hf : ∀ l, f₁ l ≤ f₂ l) (M : ℕ) (h : List ℕ) :
    treeE ch b₁ f₁ M h ≤ treeE ch b₂ f₂ M h := by
  induction M generalizing h with
  | zero => exact hb h
  | succ M ih =>
    show f₁ h + ∑' o : ch h, treeE ch b₁ f₁ M (o :: h) ≤
      f₂ h + ∑' o : ch h, treeE ch b₂ f₂ M (o :: h)
    exact add_le_add (hf h) (ENNReal.tsum_le_tsum (fun o => ih (o :: h)))

theorem treeE_add (ch : List ℕ → Set ℕ) (b₁ b₂ f₁ f₂ : List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    treeE ch (b₁ + b₂) (f₁ + f₂) M h = treeE ch b₁ f₁ M h + treeE ch b₂ f₂ M h := by
  induction M generalizing h with
  | zero => rfl
  | succ M ih =>
    show (f₁ + f₂) h + ∑' o : ch h, treeE ch (b₁ + b₂) (f₁ + f₂) M (o :: h) =
      (f₁ h + ∑' o : ch h, treeE ch b₁ f₁ M (o :: h)) +
        (f₂ h + ∑' o : ch h, treeE ch b₂ f₂ M (o :: h))
    simp only [Pi.add_apply, ih, ENNReal.tsum_add]
    ring

theorem treeE_const_mul (ch : List ℕ → Set ℕ) (c : ℝ≥0∞) (b f : List ℕ → ℝ≥0∞) (M : ℕ)
    (h : List ℕ) :
    treeE ch (fun l => c * b l) (fun l => c * f l) M h = c * treeE ch b f M h := by
  induction M generalizing h with
  | zero => rfl
  | succ M ih =>
    show c * f h + ∑' o : ch h, treeE ch (fun l => c * b l) (fun l => c * f l) M (o :: h) =
      c * (f h + ∑' o : ch h, treeE ch b f M (o :: h))
    simp only [ih, ENNReal.tsum_mul_left, mul_add]

theorem treeE_zero_zero (ch : List ℕ → Set ℕ) (M : ℕ) (h : List ℕ) : treeE ch 0 0 M h = 0 := by
  induction M generalizing h with
  | zero => rfl
  | succ M ih =>
    show (0 : List ℕ → ℝ≥0∞) h + ∑' o : ch h, treeE ch 0 0 M (o :: h) = 0
    simp only [ih, Pi.zero_apply, tsum_zero, add_zero]

theorem treeE_finset_sum (ch : List ℕ → Set ℕ) {ι : Type*} (s : Finset ι)
    (b f : ι → List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    treeE ch (∑ i ∈ s, b i) (∑ i ∈ s, f i) M h = ∑ i ∈ s, treeE ch (b i) (f i) M h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact treeE_zero_zero ch M h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, treeE_add, ih]

/-! ### Conserved and superharmonic frontier terms -/

theorem treeE_conserve (ch : List ℕ → Set ℕ) (b f : List ℕ → ℝ≥0∞)
    (hb : ∀ h, b h = f h + ∑' o : ch h, b (o :: h)) (M : ℕ) (h : List ℕ) :
    treeE ch b f M h = b h := by
  induction M generalizing h with
  | zero => rfl
  | succ M ih =>
    show f h + ∑' o : ch h, treeE ch b f M (o :: h) = b h
    rw [hb h]
    simp only [ih]

theorem treeE_super (ch : List ℕ → Set ℕ) (b f : List ℕ → ℝ≥0∞)
    (hb : ∀ h, b h ≤ f h + ∑' o : ch h, b (o :: h)) (M : ℕ) (h : List ℕ) :
    b h ≤ treeE ch b f M h := by
  induction M generalizing h with
  | zero => exact le_rfl
  | succ M ih =>
    show b h ≤ f h + ∑' o : ch h, treeE ch b f M (o :: h)
    exact (hb h).trans (add_le_add le_rfl (ENNReal.tsum_le_tsum (fun o => ih (o :: h))))

/-! ### Zero frontier: monotone in the depth, and the sum over all histories -/

theorem treeE_zero_le_succ (ch : List ℕ → Set ℕ) (f : List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    treeE ch 0 f M h ≤ treeE ch 0 f (M + 1) h := by
  induction M generalizing h with
  | zero =>
    show (0 : List ℕ → ℝ≥0∞) h ≤ _
    simp
  | succ M ih =>
    show f h + ∑' o : ch h, treeE ch 0 f M (o :: h) ≤
      f h + ∑' o : ch h, treeE ch 0 f (M + 1) (o :: h)
    exact add_le_add le_rfl (ENNReal.tsum_le_tsum (fun o => ih (o :: h)))

theorem treeE_zero_mono (ch : List ℕ → Set ℕ) (f : List ℕ → ℝ≥0∞) (h : List ℕ) :
    Monotone (fun M => treeE ch 0 f M h) :=
  monotone_nat_of_le_succ (fun M => treeE_zero_le_succ ch f M h)

/-- Every history list is `[]` or `l ++ [o]` (uniquely): the sum over lists splits off the last element.
(As in `TheoremS/Tree.lean`.) -/
theorem tsum_list_decomp (g : List ℕ → ℝ≥0∞) :
    ∑' l : List ℕ, g l = g [] + ∑' o : ℕ, ∑' l : List ℕ, g (l ++ [o]) := by
  have hinj : Function.Injective (fun p : ℕ × List ℕ => p.2 ++ [p.1]) := by
    rintro ⟨o, l⟩ ⟨o', l'⟩ hh
    have h2 := congrArg List.reverse hh
    simp at h2
    obtain ⟨h3, h4⟩ := h2
    subst h3
    subst h4
    rfl
  have hsupp : Function.support
      (fun x : List ℕ => @ite ℝ≥0∞ (x = []) (Classical.propDecidable _) 0 (g x)) ⊆
      Set.range (fun p : ℕ × List ℕ => p.2 ++ [p.1]) := by
    intro l hl
    by_cases h0 : l = []
    · exfalso
      rw [Function.mem_support] at hl
      apply hl
      simp [h0]
    · have hr : l = (l.reverse).reverse := (List.reverse_reverse l).symm
      cases hl2 : l.reverse with
      | nil =>
        rw [hl2] at hr
        simp at hr
        exact absurd hr h0
      | cons o t =>
        rw [hl2] at hr
        refine ⟨(o, t.reverse), ?_⟩
        show t.reverse ++ [o] = l
        rw [hr]
        simp
  rw [ENNReal.tsum_eq_add_tsum_ite (f := g) []]
  congr 1
  rw [← hinj.tsum_eq hsupp]
  refine (tsum_congr (fun p : ℕ × List ℕ => ?_)).trans
    (ENNReal.tsum_prod' (f := fun p : ℕ × List ℕ => g (p.2 ++ [p.1])))
  have hne : p.2 ++ [p.1] ≠ [] := by simp
  simp [hne]

/-- Splitting the truncated sum `∑' l, if l.length < M + 1 then f (l ++ h) else 0` at the root.
(As in `TheoremS/Tree.lean`.) -/
theorem tr_succ (f : List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    ∑' l : List ℕ, (if l.length < M + 1 then f (l ++ h) else 0) =
      f h + ∑' o : ℕ, ∑' l : List ℕ, (if l.length < M then f (l ++ o :: h) else 0) := by
  rw [tsum_list_decomp]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp
  · refine tsum_congr (fun o => tsum_congr (fun l => ?_))
    simp [List.append_assoc]

theorem tr_le_tsum (f : List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    ∑' l : List ℕ, (if l.length < M then f (l ++ h) else 0) ≤ ∑' l : List ℕ, f (l ++ h) :=
  ENNReal.tsum_le_tsum (fun l => by split_ifs <;> simp)

theorem treeE_le_tr (ch : List ℕ → Set ℕ) (f : List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    treeE ch 0 f M h ≤ ∑' l : List ℕ, (if l.length < M then f (l ++ h) else 0) := by
  induction M generalizing h with
  | zero =>
    show (0 : List ℕ → ℝ≥0∞) h ≤ _
    simp
  | succ M ih =>
    rw [tr_succ]
    show f h + ∑' o : ch h, treeE ch 0 f M (o :: h) ≤ _
    refine add_le_add le_rfl ?_
    calc ∑' o : ch h, treeE ch 0 f M (o :: h)
        ≤ ∑' o : ch h, ∑' l : List ℕ, (if l.length < M then f (l ++ (o : ℕ) :: h) else 0) :=
          ENNReal.tsum_le_tsum (fun o => ih (o :: h))
      _ ≤ ∑' o : ℕ, ∑' l : List ℕ, (if l.length < M then f (l ++ o :: h) else 0) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun o : ℕ => ∑' l : List ℕ, (if l.length < M then f (l ++ o :: h) else 0))

theorem tr_eq_treeE (ch : List ℕ → Set ℕ) (f : List ℕ → ℝ≥0∞)
    (hz : ∀ (h : List ℕ) (o : ℕ) (l : List ℕ), o ∉ ch h → f (l ++ o :: h) = 0)
    (M : ℕ) (h : List ℕ) :
    ∑' l : List ℕ, (if l.length < M then f (l ++ h) else 0) = treeE ch 0 f M h := by
  induction M generalizing h with
  | zero =>
    show _ = (0 : List ℕ → ℝ≥0∞) h
    simp
  | succ M ih =>
    rw [tr_succ]
    show _ = f h + ∑' o : ch h, treeE ch 0 f M (o :: h)
    congr 1
    have hsupp : Function.support
        (fun o : ℕ => ∑' l : List ℕ, (if l.length < M then f (l ++ o :: h) else 0)) ⊆ ch h := by
      intro o ho
      by_contra hn
      apply (Function.mem_support.1 ho)
      refine (tsum_congr (fun l => ?_)).trans tsum_zero
      split_ifs
      · exact hz h o l hn
      · rfl
    exact (tsum_subtype_eq_of_support_subset hsupp).symm.trans
      (tsum_congr (fun o => ih (o :: h)))

/-- The easy direction: a truncated tree sum is at most the full sum over all histories. -/
theorem treeE_zero_le_tsum (ch : List ℕ → Set ℕ) (f : List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    treeE ch 0 f M h ≤ ∑' l : List ℕ, f (l ++ h) :=
  (treeE_le_tr ch f M h).trans (tr_le_tsum f M h)

/-- The hard direction: if `f` vanishes on every history that leaves the tree, the full sum is at
most the supremum of the truncated tree sums. -/
theorem tsum_le_iSup_treeE (ch : List ℕ → Set ℕ) (f : List ℕ → ℝ≥0∞)
    (hz : ∀ (h : List ℕ) (o : ℕ) (l : List ℕ), o ∉ ch h → f (l ++ o :: h) = 0) (h : List ℕ) :
    ∑' l : List ℕ, f (l ++ h) ≤ ⨆ M, treeE ch 0 f M h := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s => ?_)
  have key : ∑ l ∈ s, f (l ++ h) ≤
      ∑' l : List ℕ, (if l.length < s.sup List.length + 1 then f (l ++ h) else 0) := by
    calc ∑ l ∈ s, f (l ++ h)
        = ∑ l ∈ s, (if l.length < s.sup List.length + 1 then f (l ++ h) else 0) := by
          refine Finset.sum_congr rfl (fun l hl => ?_)
          have hlt : l.length < s.sup List.length + 1 :=
            Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hl)
          simp [hlt]
      _ ≤ _ := ENNReal.sum_le_tsum s
  rw [tr_eq_treeE ch f hz] at key
  exact key.trans (le_iSup (fun M => treeE ch 0 f M h) _)

end TheoremS.Inf
