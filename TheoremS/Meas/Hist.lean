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
`historyExists` and `historyUnique`: the side conditions `HistoryExists` and `HistoryUnique` of
`TheoremS/Meas/Statement.lean`, from Lemmas lem:m-dens and lem:m-comp (`TheoremS/Meas/Dens.lean`,
`TheoremS/Meas/Comp.lean`). Every algorithm has a history family for every marked item, and any two history
families agree on measurable sets.
-/
import TheoremS.Meas.Comp

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

/-! ### Helpers -/

section HistHelpers

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

omit [∀ m, MeasurableSpace (Ω m)] in
/-- The one-point space of histories of depth `0`. -/
private theorem hist0_subsingleton : Subsingleton (Hist Ω 0) :=
  ⟨fun u v => Subsingleton.elim (α := Unit) u v⟩

open Classical in
/-- `ρ^{(0)}`: `ρ₀` on the nonempty sets (i.e. on `{∅} = univ`), `0` on `∅`. -/
private def hist0 (A : Alg N K Ω) : Set (Hist Ω 0) → Op N K :=
  fun E => if E.Nonempty then A.rho0 else 0

private theorem hist_tr_zero : tr (0 : Op N K) = 0 := by
  simp [tr]

private theorem hist0_pom (A : Alg N K Ω) : IsPOM (hist0 A) where
  pos E _ := by
    unfold hist0
    split_ifs
    · exact A.rho0_pos
    · exact ContinuousLinearMap.isPositive_zero
  trace_lt_top E _ := by
    unfold hist0
    split_ifs
    · rw [A.rho0_tr]; exact ENNReal.one_lt_top
    · rw [hist_tr_zero]; exact ENNReal.zero_lt_top
  additive E _ hdisj a b := by
    have := hist0_subsingleton (Ω := Ω)
    by_cases hex : ∃ n, (E n).Nonempty
    · obtain ⟨n, hn⟩ := hex
      have hU : (⋃ m, E m).Nonempty := hn.mono (Set.subset_iUnion E n)
      have hzero : ∀ m, m ≠ n → ⟪a, hist0 A (E m) b⟫_ℂ = 0 := by
        intro m hm
        have hm' : ¬ (E m).Nonempty := by
          rintro ⟨u, hu⟩
          obtain ⟨v, hv⟩ := hn
          have huv : u = v := Subsingleton.elim u v
          subst huv
          exact Set.disjoint_left.1 (hdisj hm) hu hv
        simp [hist0, hm']
      have h := hasSum_single (f := fun m => ⟪a, hist0 A (E m) b⟫_ℂ) n hzero
      convert h using 1
      simp only [hist0, hU, hn, ↓reduceIte]
    · simp only [not_exists, Set.not_nonempty_iff_eq_empty] at hex
      have hU : ¬ (⋃ m, E m).Nonempty := by
        rintro ⟨u, hu⟩
        obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hu
        exact Set.not_nonempty_iff_eq_empty.2 (hex m) ⟨u, hm⟩
      have hE : ∀ m, ¬ (E m).Nonempty := fun m => Set.not_nonempty_iff_eq_empty.2 (hex m)
      have hf : (fun m => ⟪a, hist0 A (E m) b⟫_ℂ) = fun _ => 0 := by
        funext m
        simp [hist0, hE m]
      rw [hf]
      simp only [hist0, hU, ↓reduceIte, zero_apply, inner_zero_right]
      exact hasSum_zero

variable [TopologicalSpace.SeparableSpace K]

/-- Positive operator measures on histories of depth `M`. -/
private abbrev PomAt (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)] (M : ℕ) :=
  {Λ : Set (Hist Ω M) → Op N K // IsPOM Λ}

/-- The density measure `τ` chosen for `Λ` (Lemma lem:m-dens). -/
private def stTau (A : Alg N K Ω) {M : ℕ} (Λ : PomAt N K Ω M) : Measure (Hist Ω M) :=
  Classical.choose (exists_density Λ.2 A.rho0 A.rho0_pos A.rho0_tr)

/-- The density field `σ` chosen for `Λ` (Lemma lem:m-dens). -/
private def stSig (A : Alg N K Ω) {M : ℕ} (Λ : PomAt N K Ω M) : Hist Ω M → Op N K :=
  Classical.choose (Classical.choose_spec (exists_density Λ.2 A.rho0 A.rho0_pos A.rho0_tr))

private theorem stDens (A : Alg N K Ω) {M : ℕ} (Λ : PomAt N K Ω M) :
    IsDensity Λ.1 (stTau A Λ) (stSig A Λ) :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_density Λ.2 A.rho0 A.rho0_pos A.rho0_tr))).1

/-- The next history measure `Ξ^x_M ∘ Λ` (Lemma lem:m-comp(ii)). -/
private def stNextFun (A : Alg N K Ω) (x : Fin N) {M : ℕ} (Λ : PomAt N K Ω M) :
    Set (Hist Ω M × Ω M) → Op N K :=
  Classical.choose ((A.isKrausKernel_stepKraus x M).exists_comp (stDens A Λ))

private theorem stNextFun_spec (A : Alg N K Ω) (x : Fin N) {M : ℕ} (Λ : PomAt N K Ω M) :
    IsPOM (stNextFun A x Λ) ∧ ∀ G : Set (Hist Ω M × Ω M), MeasurableSet G → ∀ a b : H N K,
      ⟪a, stNextFun A x Λ G b⟫_ℂ =
        ∫ h, krausMat (A.stepKraus x M h (Prod.mk h ⁻¹' G)) (stSig A Λ h) a b ∂(stTau A Λ) :=
  Classical.choose_spec ((A.isKrausKernel_stepKraus x M).exists_comp (stDens A Λ))

private def stNext (A : Alg N K Ω) (x : Fin N) {M : ℕ} (Λ : PomAt N K Ω M) :
    PomAt N K Ω (M + 1) :=
  ⟨stNextFun A x Λ, (stNextFun_spec A x Λ).1⟩

private theorem stNext_eq (A : Alg N K Ω) (x : Fin N) {M : ℕ} (Λ : PomAt N K Ω M)
    (G : Set (Hist Ω (M + 1))) (hG : MeasurableSet G) (a b : H N K) :
    ⟪a, (stNext A x Λ).1 G b⟫_ℂ =
      ∫ h, A.stepMat x M h (Hist.sect G h) (stSig A Λ h) a b ∂(stTau A Λ) := by
  simp only [A.stepMat_eq]
  exact (stNextFun_spec A x Λ).2 G hG a b

/-- The history family, by recursion on the depth. -/
private def histSeq (A : Alg N K Ω) (x : Fin N) : (M : ℕ) → PomAt N K Ω M
  | 0 => ⟨hist0 A, hist0_pom A⟩
  | M + 1 => stNext A x (histSeq A x M)

private theorem isHistory_histSeq (A : Alg N K Ω) (x : Fin N) :
    A.IsHistory x (fun M => (histSeq A x M).1) where
  init := by
    show hist0 A Set.univ = A.rho0
    have hne : (Set.univ : Set (Hist Ω 0)).Nonempty := ⟨(() : Unit), Set.mem_univ _⟩
    simp only [hist0, hne, ↓reduceIte]
  pom M := (histSeq A x M).2
  step M := ⟨stTau A (histSeq A x M), stSig A (histSeq A x M), stDens A (histSeq A x M),
    fun G hG a b => stNext_eq A x (histSeq A x M) G hG a b⟩

end HistHelpers

/-! ### The targets -/

/-- Every algorithm has a history family for every marked item (`HistoryExists` of `TheoremS/Meas/Statement.lean`;
Lemmas lem:m-dens and lem:m-comp(ii), by induction on the depth). -/
theorem historyExists : HistoryExists := by
  intro N K _ _ _ _ Ω _ _ A x
  exact ⟨fun M => (histSeq A x M).1, isHistory_histSeq A x⟩

/-- History families agree on measurable sets (`HistoryUnique` of `TheoremS/Meas/Statement.lean`; Lemma
lem:m-comp(iii), by induction on the depth). -/
theorem historyUnique : HistoryUnique := by
  intro N K _ _ _ _ Ω _ _ A x ρ ρ' hρ hρ' M
  induction M with
  | zero =>
    intro E _
    have := hist0_subsingleton (Ω := Ω)
    rcases Set.eq_empty_or_nonempty E with rfl | hne
    · rw [(hρ.pom 0).empty, (hρ'.pom 0).empty]
    · rw [Subsingleton.eq_univ_of_nonempty hne, hρ.init, hρ'.init]
  | succ M ih =>
    intro G hG
    obtain ⟨τ, σ, hd, heq⟩ := hρ.step M
    obtain ⟨τ', σ', hd', heq'⟩ := hρ'.step M
    have := hd'.finite
    ext1 b
    refine ext_inner_left ℂ fun a => ?_
    rw [heq G hG, heq' G hG]
    simp only [A.stepMat_eq]
    have hint : ∫⁻ h, tr (σ' h) ∂τ' < ∞ := by
      simp_rw [hd'.trace_one]
      rw [lintegral_const, one_mul]
      exact measure_lt_top τ' _
    have hfin : ∀ h, tr (σ' h) < ∞ := fun h => by rw [hd'.trace_one h]; exact ENNReal.one_lt_top
    have hrepr : ∀ E, MeasurableSet E → ∀ a b : H N K,
        ⟪a, ρ M E b⟫_ℂ = ∫ h in E, ⟪a, σ' h b⟫_ℂ ∂τ' := by
      intro E hE a b
      rw [ih E hE]
      exact hd'.repr E hE a b
    exact ((A.isKrausKernel_stepKraus x M).integral_sect_eq hd τ' hd'.pos hfin hd'.meas hint hrepr
      (G := G) hG a b).symm

end

end TheoremS.Meas
