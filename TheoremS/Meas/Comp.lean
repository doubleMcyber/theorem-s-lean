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
Lemma lem:m-comp (one step) of the paper's section on measurable outcome spaces, for measurable CP kernels in
Kraus form, and the step kernel `Ξ^x` of an `Alg` as such a kernel (the consequences for history families are
in `TheoremS/Meas/Hist.lean`).
-/
import TheoremS.Meas.Dens

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

section Kernel

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {X Ω' : Type} [MeasurableSpace X] [MeasurableSpace Ω']

/-- A measurable CP kernel from `X` to `Ω'` on `H` in Kraus form (paragraph "Kernels" and lem:m-comp):
`Γ_h(F)(Y) = ∑_k A_k Y A_k†` with `A = Kr h F`, with the conditions of the fields `bounded`, `additive`,
`measurable` of `Alg` (see its docstring for their equivalence with the paper's conditions; for a kernel
`Γ_h(Ω')` need not preserve the trace, and the same argument applies with `≤` at `Ω'`). -/
structure IsKrausKernel (Kr : X → Set Ω' → ℕ → Op N K) : Prop where
  bounded : ∀ h (F : Set Ω'), MeasurableSet F → ∀ ψ : H N K,
    ∑' k, ENNReal.ofReal (‖Kr h F k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2)
  additive : ∀ h (F : ℕ → Set Ω'), (∀ n, MeasurableSet (F n)) →
    Pairwise (fun i j => Disjoint (F i) (F j)) → ∀ Y : Op N K, PosTC Y → ∀ a b : H N K,
    HasSum (fun n => krausMat (Kr h (F n)) Y a b) (krausMat (Kr h (⋃ n, F n)) Y a b)
  measurable : ∀ F : Set Ω', MeasurableSet F → ∀ Y : Op N K, PosTC Y → ∀ a b : H N K,
    Measurable (fun h => krausMat (Kr h F) Y a b)

/-! #### Helpers -/

private theorem kc_trB_lt {Y : Op N K} (hY : tr Y < ∞) : trB (hbasis N K) Y < ∞ := by
  rwa [tr_eq_trB] at hY

private theorem kc_rk1_posTC (w : H N K) : PosTC (rk1 w w) :=
  ⟨rk1_isPositive w, by rw [tr_eq_trB, trB_rk1_self]; exact ENNReal.ofReal_lt_top⟩

private theorem kc_tr_smul_real (Y : Op N K) {r : ℝ} (hr : 0 ≤ r) :
    tr ((r : ℂ) • Y) = ENNReal.ofReal r * tr Y := by
  unfold tr
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun e => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul, ENNReal.ofReal_mul hr]

private theorem kc_norm_le_re_add {Z : Op N K} (hZ : Z.IsPositive) (a c : H N K) :
    ‖⟪a, Z c⟫_ℂ‖ ≤ (⟪a, Z a⟫_ℂ).re + (⟪c, Z c⟫_ℂ).re :=
  bd_le_add_of_sq_le (norm_nonneg _) (bd_re_nonneg hZ a) (bd_re_nonneg hZ c) (bd_op_cs hZ a c)

private theorem kc_dens_posTC {Λ : Set X → Op N K} {τ : Measure X} {σ : X → Op N K}
    (hd : IsDensity Λ τ σ) (h : X) : PosTC (σ h) :=
  ⟨hd.pos h, by rw [hd.trace_one h]; exact ENNReal.one_lt_top⟩

private theorem kc_dens_lint {Λ : Set X → Op N K} {τ : Measure X} {σ : X → Op N K}
    (hd : IsDensity Λ τ σ) : ∫⁻ h, tr (σ h) ∂τ < ∞ := by
  haveI := hd.finite
  simp only [hd.trace_one, lintegral_const, one_mul]
  exact measure_lt_top τ _

private theorem kc_empty {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr) (h : X)
    {Y : Op N K} (hY : PosTC Y) (a b : H N K) : krausMat (Kr h ∅) Y a b = 0 := by
  have hs := hK.additive h (fun _ => ∅) (fun _ => MeasurableSet.empty) (fun i j _ => by simp) Y hY a b
  rw [Set.iUnion_empty] at hs
  exact (summable_const_iff _).1 hs.summable

private theorem kc_bdSeq2 {E F : Set Ω'} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : Disjoint E F) : (∀ n, MeasurableSet (bdSeq2 E F n)) ∧
      Pairwise (fun i j => Disjoint (bdSeq2 E F i) (bdSeq2 E F j)) ∧
      (⋃ n, bdSeq2 E F n) = E ∪ F := by
  refine ⟨?_, ?_, ?_⟩
  · intro n; unfold bdSeq2; split_ifs <;> simp [hE, hF]
  · intro i j hij
    unfold bdSeq2
    split_ifs <;> subst_vars <;> simp_all [hEF.symm]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_union, bdSeq2]
    constructor
    · rintro ⟨n, hn⟩
      split_ifs at hn <;> simp_all
    · rintro (hx | hx)
      · exact ⟨0, by simpa using hx⟩
      · exact ⟨1, by simpa using hx⟩

private theorem kc_union {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr) (h : X)
    {E F : Set Ω'} (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : Disjoint E F)
    {Y : Op N K} (hY : PosTC Y) (a b : H N K) :
    krausMat (Kr h (E ∪ F)) Y a b = krausMat (Kr h E) Y a b + krausMat (Kr h F) Y a b := by
  obtain ⟨hm, hdj, hU⟩ := kc_bdSeq2 hE hF hEF
  have hs0 := hK.additive h (bdSeq2 E F) hm hdj Y hY a b
  rw [hU] at hs0
  have hs : HasSum (fun n => krausMat (Kr h (bdSeq2 E F n)) Y a b)
      (∑ n ∈ Finset.range 2, krausMat (Kr h (bdSeq2 E F n)) Y a b) :=
    hasSum_sum_of_ne_finset_zero (by
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have h1 : n ≠ 0 := by omega
      have h2 : n ≠ 1 := by omega
      simp only [bdSeq2, h1, h2, ↓reduceIte]
      exact kc_empty hK h hY a b)
  have e : ∑ n ∈ Finset.range 2, krausMat (Kr h (bdSeq2 E F n)) Y a b =
      krausMat (Kr h E) Y a b + krausMat (Kr h F) Y a b := by
    simp [Finset.sum_range_succ, bdSeq2]
  rw [e] at hs
  exact hs0.unique hs

private theorem kc_compl {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr) (h : X)
    {F : Set Ω'} (hF : MeasurableSet F) {Y : Op N K} (hY : PosTC Y) (a b : H N K) :
    krausMat (Kr h Fᶜ) Y a b = krausMat (Kr h Set.univ) Y a b - krausMat (Kr h F) Y a b := by
  have hu := kc_union hK h hF hF.compl disjoint_compl_right hY a b
  rw [Set.union_compl_self] at hu
  rw [hu]
  ring

/-- Lemma lem:m-comp(i), first function (π-λ over rectangles): for measurable `G ⊆ X × Ω'`,
`h ↦ ⟪a, Γ_h(G_h)(Y) b⟫` is measurable. -/
theorem IsKrausKernel.measurable_sect {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr)
    {G : Set (X × Ω')} (hG : MeasurableSet G) {Y : Op N K} (hY : PosTC Y) (a b : H N K) :
    Measurable (fun h => krausMat (Kr h (Prod.mk h ⁻¹' G)) Y a b) := by
  induction G, hG using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty =>
    simp only [Set.preimage_empty]
    exact hK.measurable ∅ MeasurableSet.empty Y hY a b
  | basic t ht =>
    obtain ⟨E, hE, F, hF, rfl⟩ := ht
    classical
    show Measurable (fun h => krausMat (Kr h (Prod.mk h ⁻¹' E ×ˢ F)) Y a b)
    have hfun : (fun h => krausMat (Kr h (Prod.mk h ⁻¹' E ×ˢ F)) Y a b) =
        fun h => if h ∈ E then krausMat (Kr h F) Y a b else krausMat (Kr h ∅) Y a b := by
      funext h
      by_cases hh : h ∈ E
      · rw [if_pos hh, Set.mk_preimage_prod_right hh]
      · rw [if_neg hh, Set.mk_preimage_prod_right_eq_empty hh]
    rw [hfun]
    exact Measurable.ite hE (hK.measurable F hF Y hY a b)
      (hK.measurable ∅ MeasurableSet.empty Y hY a b)
  | compl t htm iht =>
    have iht' : Measurable (fun h => krausMat (Kr h (Prod.mk h ⁻¹' t)) Y a b) := iht
    have hfun : (fun h => krausMat (Kr h (Prod.mk h ⁻¹' tᶜ)) Y a b) =
        fun h => krausMat (Kr h Set.univ) Y a b - krausMat (Kr h (Prod.mk h ⁻¹' t)) Y a b := by
      funext h
      rw [Set.preimage_compl]
      exact kc_compl hK h (htm.preimage measurable_prodMk_left) hY a b
    show Measurable (fun h => krausMat (Kr h (Prod.mk h ⁻¹' tᶜ)) Y a b)
    rw [hfun]
    exact (hK.measurable _ MeasurableSet.univ Y hY a b).sub iht'
  | iUnion f hfd hfm ihf =>
    have hs : ∀ h, HasSum (fun i => krausMat (Kr h (Prod.mk h ⁻¹' f i)) Y a b)
        (krausMat (Kr h (Prod.mk h ⁻¹' ⋃ i, f i)) Y a b) := by
      intro h
      rw [Set.preimage_iUnion]
      exact hK.additive h _ (fun i => (hfm i).preimage measurable_prodMk_left)
        (fun i j hij => Disjoint.preimage _ (hfd hij)) Y hY a b
    show Measurable (fun h => krausMat (Kr h (Prod.mk h ⁻¹' ⋃ i, f i)) Y a b)
    refine measurable_of_tendsto_metrizable
      (f := fun n h => ∑ i ∈ Finset.range n, krausMat (Kr h (Prod.mk h ⁻¹' f i)) Y a b)
      (fun n => Finset.measurable_sum _ (fun i _ => ihf i)) ?_
    exact tendsto_pi_nhds.2 (fun h => (hs h).tendsto_sum_nat)

/-- Lemma lem:m-comp(i), second function: for a field `ξ` of positive operators with finite traces and
measurable matrix elements, `h ↦ ⟪a, Γ_h(G_h)(ξ(h)) b⟫` is measurable (via (M1) over the countable basis
of a separable `H`; false for non-separable `K`). -/
theorem IsKrausKernel.measurable_sect_field {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr)
    [TopologicalSpace.SeparableSpace K] {G : Set (X × Ω')} (hG : MeasurableSet G) {ξ : X → Op N K} (hpos : ∀ h, (ξ h).IsPositive)
    (hfin : ∀ h, tr (ξ h) < ∞) (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, ξ h b⟫_ℂ))
    (a b : H N K) :
    Measurable (fun h => krausMat (Kr h (Prod.mk h ⁻¹' G)) (ξ h) a b) := by
  haveI : Countable (basisSet N K) := basisSet_countable.to_subtype
  have hsec : ∀ h : X, MeasurableSet (Prod.mk h ⁻¹' G) := fun h => hG.preimage measurable_prodMk_left
  have hlim : ∀ h, Filter.Tendsto (fun s : Finset (basisSet N K) => ∑ i ∈ s, ∑ j ∈ s,
      ⟪(hbasis N K) i, ξ h ((hbasis N K) j)⟫_ℂ *
        krausMatG (Kr h (Prod.mk h ⁻¹' G)) (rk1 ((hbasis N K) i) ((hbasis N K) j)) a b)
      Filter.atTop (nhds (krausMat (Kr h (Prod.mk h ⁻¹' G)) (ξ h) a b)) := fun h =>
    krausMatG_tendsto_matrix (hK.bounded h _ (hsec h)) (hpos h) (kc_trB_lt (hfin h)) a b
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset (basisSet N K)))
  refine measurable_of_tendsto_metrizable
    (f := fun n h => ∑ i ∈ u n, ∑ j ∈ u n, ⟪(hbasis N K) i, ξ h ((hbasis N K) j)⟫_ℂ *
        krausMatG (Kr h (Prod.mk h ⁻¹' G)) (rk1 ((hbasis N K) i) ((hbasis N K) j)) a b)
    (fun n => ?_) (tendsto_pi_nhds.2 (fun h => (hlim h).comp hu))
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  refine (hmeas _ _).mul ?_
  have hpol : (fun h => krausMatG (Kr h (Prod.mk h ⁻¹' G))
      (rk1 ((hbasis N K) i) ((hbasis N K) j)) a b) = fun h =>
      (1 / 4 : ℂ) * ∑ m : Fin 4, Complex.I ^ (m : ℕ) * krausMatG (Kr h (Prod.mk h ⁻¹' G))
        (rk1 ((hbasis N K) i + Complex.I ^ (m : ℕ) • (hbasis N K) j)
          ((hbasis N K) i + Complex.I ^ (m : ℕ) • (hbasis N K) j)) a b := by
    funext h
    exact krausMatG_rk1_polar (hK.bounded h _ (hsec h)) _ _ a b
  rw [hpol]
  refine Measurable.const_mul (Finset.measurable_sum _ fun m _ => Measurable.const_mul ?_ _) _
  exact hK.measurable_sect hG (kc_rk1_posTC _) a b

/-- Integrability of the integrand of lem:m-comp(ii) and (iii): `|⟪a, Γ_h(G_h)(ξ(h)) b⟫| ≤ ‖a‖ ‖b‖ tr ξ(h)`
and `∫ tr ξ dν < ∞`. -/
theorem IsKrausKernel.integrable_sect_field {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr)
    [TopologicalSpace.SeparableSpace K] {G : Set (X × Ω')} (hG : MeasurableSet G) (ν : Measure X)
    {ξ : X → Op N K} (hpos : ∀ h, (ξ h).IsPositive) (hfin : ∀ h, tr (ξ h) < ∞)
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, ξ h b⟫_ℂ)) (hint : ∫⁻ h, tr (ξ h) ∂ν < ∞)
    (a b : H N K) :
    Integrable (fun h => krausMat (Kr h (Prod.mk h ⁻¹' G)) (ξ h) a b) ν := by
  have hb : Integrable (fun h => ‖a‖ * ‖b‖ * (tr (ξ h)).toReal) ν :=
    (integrable_toReal_of_lintegral_ne_top (measurable_tr hmeas).aemeasurable hint.ne).const_mul _
  refine hb.mono' (hK.measurable_sect_field hG hpos hfin hmeas a b).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun h => ?_)
  have hle := norm_krausMatG_le (hK.bounded h (Prod.mk h ⁻¹' G) (hG.preimage measurable_prodMk_left)) (hpos h)
    (kc_trB_lt (hfin h)) a b
  rw [tr_eq_trB]
  exact hle

/-- Lemma lem:m-comp(ii): for a density `(σ, τ)` of `Λ` (no `IsPOM Λ` is needed),
`Λ'(G) = ∫ Γ_h(G_h)(σ(h)) τ(dh)` (weakly) defines a positive operator measure `Γ ∘ Λ` on `X × Ω'`. -/
theorem IsKrausKernel.exists_comp {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr)
    [TopologicalSpace.SeparableSpace K] {Λ : Set X → Op N K} {τ : Measure X} {σ : X → Op N K}
    (hd : IsDensity Λ τ σ) :
    ∃ Λ' : Set (X × Ω') → Op N K, IsPOM Λ' ∧ ∀ G : Set (X × Ω'), MeasurableSet G → ∀ a b : H N K,
      ⟪a, Λ' G b⟫_ℂ = ∫ h, krausMat (Kr h (Prod.mk h ⁻¹' G)) (σ h) a b ∂τ := by
  classical
  haveI := hd.finite
  have hsec : ∀ {G : Set (X × Ω')}, MeasurableSet G → ∀ h : X, MeasurableSet (Prod.mk h ⁻¹' G) :=
    fun hG h => hG.preimage measurable_prodMk_left
  have hσfin : ∀ h, tr (σ h) < ∞ := fun h => (kc_dens_posTC hd h).2
  have hσint := kc_dens_lint hd
  have hex : ∀ (G : Set (X × Ω')) (h : X), ∃ Z : Op N K, MeasurableSet G →
      Z.IsPositive ∧ ∀ a c, ⟪a, Z c⟫_ℂ = krausMat (Kr h (Prod.mk h ⁻¹' G)) (σ h) a c := by
    intro G h
    by_cases hG : MeasurableSet G
    · obtain ⟨Z, hZp, hZe⟩ :=
        exists_krausOp (hK.bounded h _ (hsec hG h)) (hd.pos h) (kc_trB_lt (hσfin h))
      exact ⟨Z, fun _ => ⟨hZp, hZe⟩⟩
    · exact ⟨0, fun h' => absurd h' hG⟩
  choose Z hZ using hex
  have hZtr : ∀ {G : Set (X × Ω')}, MeasurableSet G → ∀ h, tr (Z G h) ≤ 1 := by
    intro G hG h
    rw [tr_eq_trB, ← hd.trace_one h, tr_eq_trB]
    exact trB_le_of_krausMatG (hK.bounded h _ (hsec hG h)) (hd.pos h) (kc_trB_lt (hσfin h))
      (hZ G h hG).2
  have hZm : ∀ {G : Set (X × Ω')}, MeasurableSet G → ∀ a c : H N K,
      Measurable (fun h => ⟪a, Z G h c⟫_ℂ) := by
    intro G hG a c
    have e : (fun h => ⟪a, Z G h c⟫_ℂ) = fun h => krausMat (Kr h (Prod.mk h ⁻¹' G)) (σ h) a c :=
      funext fun h => (hZ G h hG).2 a c
    rw [e]
    exact hK.measurable_sect_field hG hd.pos hσfin hd.meas a c
  have hZint : ∀ {G : Set (X × Ω')}, MeasurableSet G → ∫⁻ h, tr (Z G h) ∂τ < ∞ := by
    intro G hG
    calc ∫⁻ h, tr (Z G h) ∂τ ≤ ∫⁻ _, 1 ∂τ := lintegral_mono fun h => hZtr hG h
      _ = τ Set.univ := lintegral_one
      _ < ∞ := measure_lt_top τ _
  have hexL : ∀ G : Set (X × Ω'), ∃ L : Op N K, MeasurableSet G →
      PosTC L ∧ ∀ a c, ⟪a, L c⟫_ℂ = ∫ h, ⟪a, Z G h c⟫_ℂ ∂τ := by
    intro G
    by_cases hG : MeasurableSet G
    · obtain ⟨L, hL1, -, hL3⟩ :=
        exists_weakInt (τ := τ) (fun h => (hZ G h hG).1) (hZm hG) (hZint hG)
      exact ⟨L, fun _ => ⟨hL1, hL3⟩⟩
    · exact ⟨0, fun h' => absurd h' hG⟩
  choose L hL using hexL
  have hLrepr : ∀ G : Set (X × Ω'), MeasurableSet G → ∀ a c : H N K,
      ⟪a, L G c⟫_ℂ = ∫ h, krausMat (Kr h (Prod.mk h ⁻¹' G)) (σ h) a c ∂τ := by
    intro G hG a c
    rw [(hL G hG).2 a c]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => (hZ G h hG).2 a c)
  refine ⟨L, ⟨fun G hG => (hL G hG).1.1, fun G hG => (hL G hG).1.2, ?_⟩, hLrepr⟩
  intro Fs hFm hFd a c
  have e : (fun n => ⟪a, L (Fs n) c⟫_ℂ) =
      fun n => ∫ h, krausMat (Kr h (Prod.mk h ⁻¹' Fs n)) (σ h) a c ∂τ :=
    funext fun n => hLrepr _ (hFm n) a c
  rw [e, hLrepr _ (MeasurableSet.iUnion hFm)]
  have hadd : ∀ h (x y : H N K), HasSum (fun n => krausMat (Kr h (Prod.mk h ⁻¹' Fs n)) (σ h) x y)
      (krausMat (Kr h (Prod.mk h ⁻¹' ⋃ n, Fs n)) (σ h) x y) := by
    intro h x y
    rw [Set.preimage_iUnion]
    exact hK.additive h _ (fun n => hsec (hFm n) h)
      (fun i j hij => Disjoint.preimage _ (hFd hij)) (σ h) (kc_dens_posTC hd h) x y
  have hbs : ∀ h, HasSum (fun n => (krausMat (Kr h (Prod.mk h ⁻¹' Fs n)) (σ h) a a).re +
      (krausMat (Kr h (Prod.mk h ⁻¹' Fs n)) (σ h) c c).re)
      ((krausMat (Kr h (Prod.mk h ⁻¹' ⋃ n, Fs n)) (σ h) a a).re +
        (krausMat (Kr h (Prod.mk h ⁻¹' ⋃ n, Fs n)) (σ h) c c).re) := fun h =>
    (Complex.hasSum_re (hadd h a a)).add (Complex.hasSum_re (hadd h c c))
  have hIa := hK.integrable_sect_field (MeasurableSet.iUnion hFm) τ hd.pos hσfin hd.meas hσint a a
  have hIc := hK.integrable_sect_field (MeasurableSet.iUnion hFm) τ hd.pos hσfin hd.meas hσint c c
  have hIre : Integrable (fun h => (krausMat (Kr h (Prod.mk h ⁻¹' ⋃ n, Fs n)) (σ h) a a).re +
      (krausMat (Kr h (Prod.mk h ⁻¹' ⋃ n, Fs n)) (σ h) c c).re) τ :=
    hIa.re.add hIc.re
  refine MeasureTheory.hasSum_integral_of_dominated_convergence
    (F := fun n h => krausMat (Kr h (Prod.mk h ⁻¹' Fs n)) (σ h) a c)
    (f := fun h => krausMat (Kr h (Prod.mk h ⁻¹' ⋃ n, Fs n)) (σ h) a c)
    (fun n h => (krausMat (Kr h (Prod.mk h ⁻¹' Fs n)) (σ h) a a).re +
      (krausMat (Kr h (Prod.mk h ⁻¹' Fs n)) (σ h) c c).re)
    (fun n => (hK.measurable_sect_field (hFm n) hd.pos hσfin hd.meas a c).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun h => ?_)
    (Filter.Eventually.of_forall fun h => (hbs h).summable)
    (hIre.congr (Filter.Eventually.of_forall fun h => (hbs h).tsum_eq.symm))
    (Filter.Eventually.of_forall fun h => hadd h a c)
  have hb := kc_norm_le_re_add (hZ (Fs n) h (hFm n)).1 a c
  rw [(hZ (Fs n) h (hFm n)).2 a c, (hZ (Fs n) h (hFm n)).2 a a,
    (hZ (Fs n) h (hFm n)).2 c c] at hb
  exact hb

/-- Lemma lem:m-comp(iii): if a finite measure `ν` and a field `ξ` (positive, finite traces, measurable
matrix elements, `∫ tr ξ dν < ∞`) also represent `Λ`, `Λ(E) = ∫_E ξ dν` weakly, then the integral of
(ii) may be taken with `(ξ, ν)` in place of `(σ, τ)`; so `Γ ∘ Λ` does not depend on the density. -/
theorem IsKrausKernel.integral_sect_eq {Kr : X → Set Ω' → ℕ → Op N K} (hK : IsKrausKernel Kr)
    [TopologicalSpace.SeparableSpace K] {Λ : Set X → Op N K} {τ : Measure X} {σ : X → Op N K}
    (hd : IsDensity Λ τ σ) (ν : Measure X) [IsFiniteMeasure ν] {ξ : X → Op N K}
    (hpos : ∀ h, (ξ h).IsPositive) (hfin : ∀ h, tr (ξ h) < ∞)
    (hmeas : ∀ a b : H N K, Measurable (fun h => ⟪a, ξ h b⟫_ℂ)) (hint : ∫⁻ h, tr (ξ h) ∂ν < ∞)
    (hrepr : ∀ E, MeasurableSet E → ∀ a b : H N K, ⟪a, Λ E b⟫_ℂ = ∫ h in E, ⟪a, ξ h b⟫_ℂ ∂ν)
    {G : Set (X × Ω')} (hG : MeasurableSet G) (a b : H N K) :
    ∫ h, krausMat (Kr h (Prod.mk h ⁻¹' G)) (ξ h) a b ∂ν =
      ∫ h, krausMat (Kr h (Prod.mk h ⁻¹' G)) (σ h) a b ∂τ := by
  haveI := hd.finite
  have hνac : ν ≪ ν + τ := (Measure.AbsolutelyContinuous.refl ν).add_right τ
  have hτac : τ ≪ ν + τ := (Measure.AbsolutelyContinuous.refl τ).add_right' ν
  -- change of measure for a weakly measurable field
  have hchange : ∀ (μ : Measure X) [IsFiniteMeasure μ], μ ≪ ν + τ → ∀ (Yf : X → Op N K)
      (E : Set X), MeasurableSet E → ∀ x y : H N K,
      ∫ h in E, ⟪x, Yf h y⟫_ℂ ∂μ =
        ∫ h in E, ⟪x, (((μ.rnDeriv (ν + τ) h).toReal : ℂ) • Yf h) y⟫_ℂ ∂(ν + τ) := by
    intro μ _ hac Yf E hE x y
    rw [← integral_indicator hE, ← integral_indicator hE, ← integral_rnDeriv_smul hac]
    congr 1
    funext h
    by_cases hh : h ∈ E
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, ContinuousLinearMap.smul_apply,
        inner_smul_right, Complex.real_smul]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, smul_zero]
  have hposS : ∀ (μ : Measure X) (Yf : X → Op N K), (∀ h, (Yf h).IsPositive) →
      ∀ h, ((((μ.rnDeriv (ν + τ) h).toReal : ℂ) • Yf h)).IsPositive := fun μ Yf hp h =>
    (hp h).smul_of_nonneg (Complex.zero_le_real.2 ENNReal.toReal_nonneg)
  have hmS : ∀ (μ : Measure X) (Yf : X → Op N K), (∀ x y : H N K, Measurable (fun h => ⟪x, Yf h y⟫_ℂ)) →
      ∀ x y : H N K, Measurable (fun h => ⟪x, (((μ.rnDeriv (ν + τ) h).toReal : ℂ) • Yf h) y⟫_ℂ) := by
    intro μ Yf hm x y
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
    exact (Complex.measurable_ofReal.comp (Measure.measurable_rnDeriv μ (ν + τ)).ennreal_toReal).mul
      (hm x y)
  have hiS : ∀ (μ : Measure X) [IsFiniteMeasure μ], μ ≪ ν + τ → ∀ (Yf : X → Op N K),
      (∀ x y : H N K, Measurable (fun h => ⟪x, Yf h y⟫_ℂ)) → ∫⁻ h, tr (Yf h) ∂μ < ∞ →
      ∫⁻ h, tr ((((μ.rnDeriv (ν + τ) h).toReal : ℂ) • Yf h)) ∂(ν + τ) < ∞ := by
    intro μ _ hac Yf hm hi
    calc ∫⁻ h, tr ((((μ.rnDeriv (ν + τ) h).toReal : ℂ) • Yf h)) ∂(ν + τ)
        = ∫⁻ h, ENNReal.ofReal (μ.rnDeriv (ν + τ) h).toReal * tr (Yf h) ∂(ν + τ) :=
          lintegral_congr fun h => kc_tr_smul_real (Yf h) ENNReal.toReal_nonneg
      _ ≤ ∫⁻ h, μ.rnDeriv (ν + τ) h * tr (Yf h) ∂(ν + τ) :=
          lintegral_mono fun h => mul_le_mul_of_nonneg_right ENNReal.ofReal_toReal_le zero_le
      _ = ∫⁻ h, tr (Yf h) ∂μ := lintegral_rnDeriv_mul hac (measurable_tr hm).aemeasurable
      _ < ∞ := hi
  have hEq : ∀ E, MeasurableSet E → ∀ x y : H N K,
      ∫ h in E, ⟪x, (((ν.rnDeriv (ν + τ) h).toReal : ℂ) • ξ h) y⟫_ℂ ∂(ν + τ) =
        ∫ h in E, ⟪x, (((τ.rnDeriv (ν + τ) h).toReal : ℂ) • σ h) y⟫_ℂ ∂(ν + τ) := by
    intro E hE x y
    rw [← hchange ν hνac ξ E hE x y, ← hchange τ hτac σ E hE x y, ← hrepr E hE x y,
      ← hd.repr E hE x y]
  have hae := density_ae_eq (ν + τ) _ _ (hposS ν ξ hpos) (hposS τ σ hd.pos) (hmS ν ξ hmeas)
    (hmS τ σ hd.meas) (hiS ν hνac ξ hmeas hint) (hiS τ hτac σ hd.meas (kc_dens_lint hd)) hEq
  rw [← integral_rnDeriv_smul hνac, ← integral_rnDeriv_smul hτac]
  refine integral_congr_ae ?_
  filter_upwards [hae] with h hh
  have hh' : krausMatG (Kr h (Prod.mk h ⁻¹' G)) (((ν.rnDeriv (ν + τ) h).toReal : ℂ) • ξ h) a b =
      krausMatG (Kr h (Prod.mk h ⁻¹' G)) (((τ.rnDeriv (ν + τ) h).toReal : ℂ) • σ h) a b :=
    congrArg (fun Z : Op N K => krausMatG (Kr h (Prod.mk h ⁻¹' G)) Z a b) hh
  rw [Complex.real_smul, Complex.real_smul, krausMat_eq_krausMatG, krausMat_eq_krausMatG,
    ← krausMatG_smul, ← krausMatG_smul, hh']

/-- Lemma lem:m-comp(iv): `(Γ ∘ Λ)(E × Ω') = ∫_E Γ_h(Ω')(σ(h)) τ(dh)` (weakly). -/
theorem IsKrausKernel.integral_sect_prod_univ {Kr : X → Set Ω' → ℕ → Op N K}
    (hK : IsKrausKernel Kr) {Λ : Set X → Op N K} {τ : Measure X} {σ : X → Op N K}
    (hd : IsDensity Λ τ σ) {E : Set X} (hE : MeasurableSet E) (a b : H N K) :
    ∫ h, krausMat (Kr h (Prod.mk h ⁻¹' (E ×ˢ (Set.univ : Set Ω')))) (σ h) a b ∂τ =
      ∫ h in E, krausMat (Kr h Set.univ) (σ h) a b ∂τ := by
  rw [← integral_indicator hE]
  congr 1
  funext h
  by_cases hh : h ∈ E
  · rw [Set.indicator_of_mem hh, Set.mk_preimage_prod_right hh]
  · rw [Set.indicator_of_notMem hh, Set.mk_preimage_prod_right_eq_empty hh]
    exact kc_empty hK h (kc_dens_posTC hd h) a b

end Kernel

namespace Alg

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

/-- The Kraus operators of the step kernel `Ξ^x_{M,h}(F)`: `A_k` after an operation kind, `A_k O_x` after
a query kind, none (all `0`) after a halt kind (the docstring of `stepMat`). -/
def stepKraus (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M) (F : Set (Ω M)) : ℕ → Op N K :=
  match A.kind M h with
  | .op => A.kraus M h F
  | .query => fun k => A.kraus M h F k ∘L oracleL x
  | .halt _ => fun _ => 0

private theorem kc_kind_cases (k : Kind N) : k = Kind.op ∨ k = Kind.query ∨ ∃ y, k = Kind.halt y := by
  cases k with
  | op => exact Or.inl rfl
  | query => exact Or.inr (Or.inl rfl)
  | halt y => exact Or.inr (Or.inr ⟨y, rfl⟩)

private theorem kc_stepKraus_op (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M)
    (hk : A.kind M h = Kind.op) : A.stepKraus x M h = A.kraus M h := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem kc_stepKraus_query (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M)
    (hk : A.kind M h = Kind.query) :
    A.stepKraus x M h = fun F k => A.kraus M h F k ∘L oracleL x := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem kc_stepKraus_halt (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M) {y : Fin N}
    (hk : A.kind M h = Kind.halt y) : A.stepKraus x M h = fun _ _ => 0 := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem kc_oracleL_norm (x : Fin N) (ψ : H N K) : ‖oracleL x ψ‖ = ‖ψ‖ :=
  (oracle x).norm_map ψ

private theorem kc_oracleL_adjoint (x : Fin N) :
    ContinuousLinearMap.adjoint (oracleL (K := K) x) =
      (oracle x).symm.toLinearIsometry.toContinuousLinearMap := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  show ⟪(oracle x).symm u, v⟫_ℂ = ⟪u, (oracle x) v⟫_ℂ
  rw [← (oracle x).inner_map_map ((oracle x).symm u) v, LinearIsometryEquiv.apply_symm_apply]

private theorem kc_oracle_posTC (x : Fin N) {Y : Op N K} (hY : PosTC Y) :
    PosTC (oracleL x ∘L Y ∘L ContinuousLinearMap.adjoint (oracleL x)) := by
  refine ⟨hY.1.conj_adjoint (oracleL x), ?_⟩
  rw [kc_oracleL_adjoint, tr_eq_trB]
  unfold oracleL
  rw [trB_conj (b := hbasis N K) (oracle x) hY.1, ← tr_eq_trB]
  exact hY.2

private theorem kc_krausMat_zero (Y : Op N K) (a b : H N K) :
    krausMat (fun _ => (0 : Op N K)) Y a b = 0 := by
  simp [krausMat]

/-- `stepMat` is the Kraus matrix element of `stepKraus`. -/
theorem stepMat_eq (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M) (F : Set (Ω M)) (Y : Op N K)
    (a b : H N K) : A.stepMat x M h F Y a b = krausMat (A.stepKraus x M h F) Y a b := by
  rcases kc_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
  · rw [kc_stepKraus_op A x M h hk]
    unfold stepMat
    simp only [hk]
  · rw [kc_stepKraus_query A x M h hk]
    unfold stepMat
    simp only [hk]
  · rw [kc_stepKraus_halt A x M h hk, kc_krausMat_zero]
    unfold stepMat
    simp only [hk]

/-- The step kernel `Ξ^x_M` is a measurable CP kernel from `Hist Ω M` to `Ω M` (def:s-meas: the query
kind composes the instrument with the unitary `O_x`; the kind is measurable). -/
theorem isKrausKernel_stepKraus (A : Alg N K Ω) (x : Fin N) (M : ℕ) :
    IsKrausKernel (A.stepKraus x M) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro h F hF ψ
    rcases kc_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
    · rw [kc_stepKraus_op A x M h hk]
      exact A.bounded M h F hF ψ
    · rw [kc_stepKraus_query A x M h hk]
      simp only [ContinuousLinearMap.comp_apply]
      have hb := A.bounded M h F hF (oracleL x ψ)
      rwa [kc_oracleL_norm] at hb
    · rw [kc_stepKraus_halt A x M h hk]
      simp
  · intro h Fs hFm hFd Y hY a b
    rcases kc_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
    · rw [kc_stepKraus_op A x M h hk]
      exact A.additive M h Fs hFm hFd Y hY a b
    · rw [kc_stepKraus_query A x M h hk]
      simp only [krausMat_eq_krausMatG, krausMatG_comp]
      exact A.additive M h Fs hFm hFd _ (kc_oracle_posTC x hY) a b
    · rw [kc_stepKraus_halt A x M h hk]
      simp only [kc_krausMat_zero]
      exact hasSum_zero
  · intro F hF Y hY a b
    have hop : MeasurableSet (A.kind M ⁻¹' {Kind.op}) :=
      A.kind_meas M MeasurableSpace.measurableSet_top
    have hq : MeasurableSet (A.kind M ⁻¹' {Kind.query}) :=
      A.kind_meas M MeasurableSpace.measurableSet_top
    have hfun : (fun h => krausMat (A.stepKraus x M h F) Y a b) = fun h =>
        if h ∈ A.kind M ⁻¹' {Kind.op} then krausMat (A.kraus M h F) Y a b
        else if h ∈ A.kind M ⁻¹' {Kind.query} then
          krausMat (A.kraus M h F) (oracleL x ∘L Y ∘L ContinuousLinearMap.adjoint (oracleL x)) a b
        else 0 := by
      funext h
      rcases kc_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
      · rw [kc_stepKraus_op A x M h hk]
        simp [hk]
      · rw [kc_stepKraus_query A x M h hk]
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hk, reduceCtorEq, ↓reduceIte]
        exact krausMatG_comp (A.kraus M h F) (oracleL x) Y a b
      · rw [kc_stepKraus_halt A x M h hk, kc_krausMat_zero]
        simp [hk]
    rw [hfun]
    exact Measurable.ite hop (A.measurable M F hF Y hY a b)
      (Measurable.ite hq (A.measurable M F hF _ (kc_oracle_posTC x hY) a b) measurable_const)

end Alg

end

end TheoremS.Meas
