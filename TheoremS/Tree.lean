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
Truncated sums over a tree of histories (Mathlib only, nothing about quantum algorithms).

Histories are `List ℕ`, newest outcome first; `ch h` is the finite set of outcomes allowed after `h`.
`treeR ch f M h` sums `f` over the nodes of depth `< M` below `h` (recursively); `treeG ch b f M h` is the
real version with a frontier term `b` at depth `M`.
-/
import Mathlib

namespace TheoremS

set_option autoImplicit false

open scoped ENNReal

/-- `treeR ch f M h = ∑` of `f` over the descendants `l ++ h` of `h` (inside the tree `ch`) of depth `< M`. -/
noncomputable def treeR (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ≥0∞) : ℕ → List ℕ → ℝ≥0∞
  | 0, _ => 0
  | M + 1, h => f h + ∑ o ∈ ch h, treeR ch f M (o :: h)

/-- Real truncated tree sum with frontier term `b` at depth `M`. -/
noncomputable def treeG (ch : List ℕ → Finset ℕ) (b f : List ℕ → ℝ) : ℕ → List ℕ → ℝ
  | 0, h => b h
  | M + 1, h => f h + ∑ o ∈ ch h, treeG ch b f M (o :: h)

/-- Every history list is `[]` or `l ++ [o]` (uniquely): the sum over lists splits off the last element. -/
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

/-- Splitting the truncated sum `∑' l, if l.length < M + 1 then f (l ++ h) else 0` at the root. -/
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

theorem treeR_le_tr (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ≥0∞) :
    ∀ (M : ℕ) (h : List ℕ),
      treeR ch f M h ≤ ∑' l : List ℕ, (if l.length < M then f (l ++ h) else 0) := by
  intro M
  induction M with
  | zero => intro h; simp [treeR]
  | succ M ih =>
    intro h
    rw [tr_succ]
    show f h + ∑ o ∈ ch h, treeR ch f M (o :: h) ≤ _
    refine add_le_add le_rfl ?_
    calc ∑ o ∈ ch h, treeR ch f M (o :: h)
        ≤ ∑ o ∈ ch h, ∑' l : List ℕ, (if l.length < M then f (l ++ o :: h) else 0) :=
          Finset.sum_le_sum (fun o _ => ih (o :: h))
      _ ≤ ∑' o : ℕ, ∑' l : List ℕ, (if l.length < M then f (l ++ o :: h) else 0) :=
          ENNReal.sum_le_tsum _

theorem tr_eq_treeR (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ≥0∞)
    (hz : ∀ (h : List ℕ) (o : ℕ) (l : List ℕ), o ∉ ch h → f (l ++ o :: h) = 0) :
    ∀ (M : ℕ) (h : List ℕ),
      ∑' l : List ℕ, (if l.length < M then f (l ++ h) else 0) = treeR ch f M h := by
  intro M
  induction M with
  | zero => intro h; simp [treeR]
  | succ M ih =>
    intro h
    rw [tr_succ]
    show _ = f h + ∑ o ∈ ch h, treeR ch f M (o :: h)
    congr 1
    refine (tsum_eq_sum (s := ch h) ?_).trans
      (Finset.sum_congr rfl (fun o _ => ih (o :: h)))
    intro o ho
    refine (tsum_congr (fun l => ?_)).trans tsum_zero
    split_ifs
    · exact hz h o l ho
    · rfl

theorem treeR_le_succ (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ≥0∞) :
    ∀ (M : ℕ) (h : List ℕ), treeR ch f M h ≤ treeR ch f (M + 1) h := by
  intro M
  induction M with
  | zero => intro h; simp [treeR]
  | succ M ih =>
    intro h
    show f h + ∑ o ∈ ch h, treeR ch f M (o :: h) ≤
      f h + ∑ o ∈ ch h, treeR ch f (M + 1) (o :: h)
    exact add_le_add le_rfl (Finset.sum_le_sum (fun o _ => ih (o :: h)))

theorem treeG_zero_nonneg (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ) (hf : ∀ h, 0 ≤ f h) :
    ∀ (M : ℕ) (h : List ℕ), 0 ≤ treeG ch 0 f M h := by
  intro M
  induction M with
  | zero => intro h; simp [treeG]
  | succ M ih =>
    intro h
    show 0 ≤ f h + ∑ o ∈ ch h, treeG ch 0 f M (o :: h)
    exact add_nonneg (hf h) (Finset.sum_nonneg (fun o _ => ih (o :: h)))

theorem treeR_mono (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ≥0∞) (h : List ℕ) :
    Monotone (fun M => treeR ch f M h) := by
  exact monotone_nat_of_le_succ (fun M => treeR_le_succ ch f M h)

/-- The easy direction: a truncated tree sum is at most the full sum over all histories. -/
theorem treeR_le_tsum (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ≥0∞) (M : ℕ) (h : List ℕ) :
    treeR ch f M h ≤ ∑' l : List ℕ, f (l ++ h) :=
  (treeR_le_tr ch f M h).trans (tr_le_tsum f M h)

/-- The hard direction: if `f` vanishes on every history that leaves the tree, the full sum is the
supremum of the truncated tree sums. -/
theorem tsum_le_iSup_treeR (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ≥0∞)
    (hz : ∀ (h : List ℕ) (o : ℕ) (l : List ℕ), o ∉ ch h → f (l ++ o :: h) = 0) (h : List ℕ) :
    ∑' l : List ℕ, f (l ++ h) ≤ ⨆ M, treeR ch f M h := by
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
  rw [tr_eq_treeR ch f hz] at key
  exact key.trans (le_iSup (fun M => treeR ch f M h) _)

/-- The real sum with zero frontier term is the ENNReal sum of a nonnegative function. -/
theorem ofReal_treeG_zero (ch : List ℕ → Finset ℕ) (f : List ℕ → ℝ) (hf : ∀ h, 0 ≤ f h)
    (M : ℕ) (h : List ℕ) :
    ENNReal.ofReal (treeG ch 0 f M h) = treeR ch (fun l => ENNReal.ofReal (f l)) M h := by
  induction M generalizing h with
  | zero => simp [treeG, treeR]
  | succ M ih =>
    show ENNReal.ofReal (f h + ∑ o ∈ ch h, treeG ch 0 f M (o :: h)) =
      ENNReal.ofReal (f h) + ∑ o ∈ ch h, treeR ch (fun l => ENNReal.ofReal (f l)) M (o :: h)
    rw [ENNReal.ofReal_add (hf h)
        (Finset.sum_nonneg (fun o _ => treeG_zero_nonneg ch f hf M (o :: h))),
      ENNReal.ofReal_sum_of_nonneg (fun o _ => treeG_zero_nonneg ch f hf M (o :: h))]
    congr 1
    exact Finset.sum_congr rfl (fun o _ => ih (o :: h))

end TheoremS
