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
Theorem thm:S-meas of the paper: the proofs `theoremSMeasGen`, `theoremSMeasGen'`, `theoremSMeas` and
`theoremSMeas'` of the claims `TheoremSMeasGen`, `TheoremSMeasGen'`, `TheoremSMeas`, `TheoremSMeas'` of
`TheoremS/Meas/Statement.lean`, from Lemmas lem:m-front, lem:m-joint, lem:m-cell (`TheoremS/Meas/Front.lean`,
`TheoremS/Meas/Joint.lean`, `TheoremS/Meas/Cell.lean`) and the potential calculus of
`TheoremS/Potential.lean`.

Cells. A cell of depth `M` is a word `w : Fin M → Bool` (the non-halt kinds taken before depth `M`,
`true` = query) and a kind `s : Bool ⊕ Fin N` at depth `M`. `cP A M w` (histories that followed `w`) is
defined by recursion on `M`, so that `cP A (M+1) (snoc w b) = cX A M w (inl b) ×ˢ univ` holds by
definition; `cX A M w s = cP A M w ∩ kind⁻¹ (kOf s)`. The potential is
`Φ_M = κ (∑_{m<M} ∑_{halt cells of depth m} V + ∑_w V(cP M w)) + ∑_{m<M} ∑_w W(query cell)`.
-/
import TheoremS.Meas.Front
import TheoremS.Meas.Cell
import TheoremS.Potential

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

namespace Bound

open Filter Topology

/-! ### Kinds and constants -/

section Kinds

variable {N : ℕ}

/-- The non-halt kinds: `true` = query, `false` = operation. -/
def ofB : Bool → Kind N
  | true => Kind.query
  | false => Kind.op

/-- All kinds, indexed by the finite type `Bool ⊕ Fin N`. -/
def kOf : Bool ⊕ Fin N → Kind N
  | Sum.inl b => ofB b
  | Sum.inr y => Kind.halt y

theorem ofB_injective : Function.Injective (ofB (N := N)) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [ofB] at h)

theorem kOf_injective : Function.Injective (kOf (N := N)) := by
  rintro (a | y) (b | y') h
  · have h' : ofB a = ofB b := h
    exact congrArg Sum.inl (ofB_injective h')
  · cases a <;> simp [kOf, ofB] at h
  · cases b <;> simp [kOf, ofB] at h
  · have h' : (Kind.halt y : Kind N) = Kind.halt y' := h
    exact congrArg Sum.inr (Kind.halt.inj h')

theorem kOf_surjective : Function.Surjective (kOf (N := N)) := by
  intro k
  cases k with
  | op => exact ⟨Sum.inl false, rfl⟩
  | query => exact ⟨Sum.inl true, rfl⟩
  | halt y => exact ⟨Sum.inr y, rfl⟩

theorem two_le_sqrt (hN : 4 ≤ N) : (2 : ℝ) ≤ Real.sqrt N := by
  calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ = Real.sqrt 4 := by norm_num
    _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hN)

/-- `κ = 2 / arcsin (2/√N)`. -/
def kap (N : ℕ) : ℝ := 2 / Real.arcsin (2 / Real.sqrt N)

theorem kap_pos (hN : 4 ≤ N) : 0 < kap N := TheoremS.kappa_pos _ (two_le_sqrt hN)

end Kinds

/-! ### Cells -/

section Cells

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

theorem kmeas (A : Alg N K Ω) (M : ℕ) (S : Set (Kind N)) : MeasurableSet (A.kind M ⁻¹' S) :=
  A.kind_meas M MeasurableSpace.measurableSet_top

/-- The histories of depth `M` whose kinds at depths `< M` are the non-halt kinds of `w`. -/
def cP (A : Alg N K Ω) : (M : ℕ) → (Fin M → Bool) → Set (Hist Ω M)
  | 0, _ => Set.univ
  | M + 1, w => ((cP A M (Fin.init w) ∩ A.kind M ⁻¹' {ofB (w (Fin.last M))}) ×ˢ
      (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1)))

theorem cP_zero (A : Alg N K Ω) (w : Fin 0 → Bool) : cP A 0 w = Set.univ := rfl

theorem cP_succ (A : Alg N K Ω) (M : ℕ) (w : Fin (M + 1) → Bool) :
    cP A (M + 1) w = ((cP A M (Fin.init w) ∩ A.kind M ⁻¹' {ofB (w (Fin.last M))}) ×ˢ
      (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1))) := rfl

/-- The cell `(w, s)` of depth `M`. -/
def cX (A : Alg N K Ω) (M : ℕ) (w : Fin M → Bool) (s : Bool ⊕ Fin N) : Set (Hist Ω M) :=
  cP A M w ∩ A.kind M ⁻¹' {kOf s}

theorem measurableSet_cP (A : Alg N K Ω) (M : ℕ) (w : Fin M → Bool) : MeasurableSet (cP A M w) := by
  induction M with
  | zero => rw [cP_zero]; exact MeasurableSet.univ
  | succ M ih =>
    rw [cP_succ]
    exact ((ih (Fin.init w)).inter (kmeas A M _)).prod MeasurableSet.univ

theorem measurableSet_cX (A : Alg N K Ω) (M : ℕ) (w : Fin M → Bool) (s : Bool ⊕ Fin N) :
    MeasurableSet (cX A M w s) :=
  (measurableSet_cP A M w).inter (kmeas A M _)

theorem cP_snoc (A : Alg N K Ω) (M : ℕ) (w : Fin M → Bool) (b : Bool) :
    cP A (M + 1) (Fin.snoc (α := fun _ => Bool) w b) =
      (cX A M w (Sum.inl b) ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1))) := by
  rw [cP_succ, Fin.init_snoc, Fin.snoc_last]
  rfl

theorem cP_eq_of_mem (A : Alg N K Ω) {M : ℕ} {w w' : Fin M → Bool} {h : Hist Ω M}
    (h1 : h ∈ cP A M w) (h2 : h ∈ cP A M w') : w = w' := by
  induction M with
  | zero => funext i; exact i.elim0
  | succ M ih =>
    rw [cP_succ] at h1 h2
    obtain ⟨⟨a1, a1k⟩, -⟩ := h1
    obtain ⟨⟨a2, a2k⟩, -⟩ := h2
    have hi := ih a1 a2
    have e1 : A.kind M (Prod.fst (α := Hist Ω M) (β := Ω M) h) = ofB (w (Fin.last M)) := a1k
    have e2 : A.kind M (Prod.fst (α := Hist Ω M) (β := Ω M) h) = ofB (w' (Fin.last M)) := a2k
    have el : w (Fin.last M) = w' (Fin.last M) := ofB_injective (e1.symm.trans e2)
    rw [← Fin.snoc_init_self w, ← Fin.snoc_init_self w', hi, el]

theorem cX_sub (A : Alg N K Ω) (M : ℕ) (w : Fin M → Bool) (s : Bool ⊕ Fin N) :
    cX A M w s ⊆ A.kind M ⁻¹' {kOf s} := fun _ hh => hh.2

end Cells

/-! ### Finite additivity, `C` and `W` -/

section Measures

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

theorem isPOM_Cf {α : Type} [MeasurableSpace α] {Λ' : Set α → Op N (RK N K)} (hP : IsPOM Λ') :
    IsPOM (fun E => ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) ∘L Λ' E ∘L uEmb) where
  pos E hE := (hP.pos E hE).adjoint_conj uEmb
  trace_lt_top E hE :=
    lt_of_le_of_lt (Cf_le_tr ⟨hP.pos E hE, hP.trace_lt_top E hE⟩) (hP.trace_lt_top E hE)
  additive E hE hd a b := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right] using
      hP.additive E hE hd (uEmb a) (uEmb b)

theorem measure_partition {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → Kind N)
    (hf : ∀ S, MeasurableSet (f ⁻¹' S)) (S : Set α) (hS : MeasurableSet S) :
    μ S = ∑ s : Bool ⊕ Fin N, μ (S ∩ f ⁻¹' {kOf s}) := by
  have hU : S = ⋃ s : Bool ⊕ Fin N, S ∩ f ⁻¹' {kOf s} := by
    ext h
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hh
      obtain ⟨s, hs⟩ := kOf_surjective (f h)
      exact ⟨s, hh, hs.symm⟩
    · rintro ⟨s, hh, -⟩
      exact hh
  have hd : Pairwise (Function.onFun Disjoint fun s : Bool ⊕ Fin N => S ∩ f ⁻¹' {kOf s}) := by
    intro i j hij
    show Disjoint _ _
    refine Set.disjoint_left.2 fun h hi hj => hij (kOf_injective ?_)
    have e1 : f h = kOf i := hi.2
    have e2 : f h = kOf j := hj.2
    exact e1.symm.trans e2
  calc μ S = μ (⋃ s : Bool ⊕ Fin N, S ∩ f ⁻¹' {kOf s}) := by rw [← hU]
    _ = ∑' s, μ (S ∩ f ⁻¹' {kOf s}) := measure_iUnion hd (fun s => hS.inter (hf _))
    _ = ∑ s, μ (S ∩ f ⁻¹' {kOf s}) := tsum_fintype _

variable {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

theorem posTC_of {α : Type} [MeasurableSpace α] {Λ' : Set α → Op N K'} (hP : IsPOM Λ')
    {E : Set α} (hE : MeasurableSet E) : PosTC (Λ' E) :=
  ⟨hP.pos E hE, hP.trace_lt_top E hE⟩

theorem tr_ne_top {α : Type} [MeasurableSpace α] {Λ' : Set α → Op N K'} (hP : IsPOM Λ')
    {E : Set α} (hE : MeasurableSet E) : tr (Λ' E) ≠ ⊤ :=
  (hP.trace_lt_top E hE).ne

theorem tr_mono_pom {α : Type} [MeasurableSpace α] {Λ' : Set α → Op N K'} (hP : IsPOM Λ')
    {E F : Set α} (hE : MeasurableSet E) (hF : MeasurableSet F) (h : E ⊆ F) :
    tr (Λ' E) ≤ tr (Λ' F) := by
  rw [← bdTrMeas_apply hP hE, ← bdTrMeas_apply hP hF]
  exact measure_mono h

theorem pom_partition (A : Alg N K Ω) {M : ℕ} {Λ' : Set (Hist Ω M) → Op N K'} (hP : IsPOM Λ')
    (w : Fin M → Bool) : tr (Λ' (cP A M w)) = ∑ s : Bool ⊕ Fin N, tr (Λ' (cX A M w s)) := by
  rw [← bdTrMeas_apply hP (measurableSet_cP A M w),
    measure_partition (bdTrMeas hP) (A.kind M) (kmeas A M) _ (measurableSet_cP A M w)]
  exact Finset.sum_congr rfl fun s _ => bdTrMeas_apply hP (measurableSet_cX A M w s)

theorem sum_cP_le (A : Alg N K Ω) {M : ℕ} {Λ' : Set (Hist Ω M) → Op N K'} (hP : IsPOM Λ')
    {S : Set (Hist Ω M)} (hS : MeasurableSet S) :
    ∑ w : Fin M → Bool, tr (Λ' (cP A M w ∩ S)) ≤ tr (Λ' S) := by
  have hm : ∀ w, MeasurableSet (cP A M w ∩ S) := fun w => (measurableSet_cP A M w).inter hS
  have hd : Pairwise (Function.onFun Disjoint fun w : Fin M → Bool => cP A M w ∩ S) := by
    intro w w' hww'
    show Disjoint _ _
    exact Set.disjoint_left.2 fun h h1 h2 => hww' (cP_eq_of_mem A h1.1 h2.1)
  calc ∑ w : Fin M → Bool, tr (Λ' (cP A M w ∩ S))
      = ∑ w : Fin M → Bool, bdTrMeas hP (cP A M w ∩ S) :=
        Finset.sum_congr rfl fun w _ => (bdTrMeas_apply hP (hm w)).symm
    _ = ∑' w : Fin M → Bool, bdTrMeas hP (cP A M w ∩ S) := (tsum_fintype _).symm
    _ = bdTrMeas hP (⋃ w : Fin M → Bool, cP A M w ∩ S) := (measure_iUnion hd hm).symm
    _ ≤ bdTrMeas hP S := measure_mono (Set.iUnion_subset fun w => Set.inter_subset_right)
    _ = tr (Λ' S) := bdTrMeas_apply hP hS

theorem toReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∑ i ∈ s, f i ≤ c) : ∑ i ∈ s, (f i).toReal ≤ c.toReal := by
  have hf : ∀ i ∈ s, f i ≠ ⊤ := fun i hi =>
    ne_top_of_le_ne_top hc ((Finset.single_le_sum (fun j _ => zero_le) hi).trans h)
  rw [← ENNReal.toReal_sum hf]
  exact ENNReal.toReal_mono hc h

theorem sumR_cP_le (A : Alg N K Ω) {M : ℕ} {Λ' : Set (Hist Ω M) → Op N K'} (hP : IsPOM Λ')
    {S : Set (Hist Ω M)} (hS : MeasurableSet S) :
    ∑ w : Fin M → Bool, (tr (Λ' (cP A M w ∩ S))).toReal ≤ (tr (Λ' S)).toReal :=
  toReal_sum_le _ _ (tr_ne_top hP hS) (sum_cP_le A hP hS)

theorem Cf_partition (A : Alg N K Ω) {M : ℕ} {Λ' : Set (Hist Ω M) → Op N (RK N K)} (hP : IsPOM Λ')
    (w : Fin M → Bool) : Cf (Λ' (cP A M w)) = ∑ s : Bool ⊕ Fin N, Cf (Λ' (cX A M w s)) :=
  pom_partition A (isPOM_Cf hP) w

theorem Cf_ne_top {α : Type} [MeasurableSpace α] {Λ' : Set α → Op N (RK N K)} (hP : IsPOM Λ')
    {E : Set α} (hE : MeasurableSet E) : Cf (Λ' E) ≠ ⊤ :=
  ne_top_of_le_ne_top (tr_ne_top hP hE) (Cf_le_tr (posTC_of hP hE))

theorem C_le_W {α : Type} [MeasurableSpace α] {Λ' : Set α → Op N (RK N K)} (hP : IsPOM Λ')
    {E : Set α} (hE : MeasurableSet E) : (Cf (Λ' E)).toReal ≤ (tr (Λ' E)).toReal :=
  ENNReal.toReal_mono (tr_ne_top hP hE) (Cf_le_tr (posTC_of hP hE))

/-- `V(Λ_M(E)) = Vf (C, W)`. -/
def VL (Λ : HistFam N (RK N K) Ω) (M : ℕ) (E : Set (Hist Ω M)) : ℝ :=
  TheoremS.Vf (Cf (Λ M E)).toReal (tr (Λ M E)).toReal

theorem V_partition (A : Alg N K Ω) {Λ : HistFam N (RK N K) Ω} {M : ℕ} (hP : IsPOM (Λ M))
    (w : Fin M → Bool) : VL Λ M (cP A M w) ≤ ∑ s : Bool ⊕ Fin N, VL Λ M (cX A M w s) := by
  have hC : (Cf (Λ M (cP A M w))).toReal = ∑ s : Bool ⊕ Fin N, (Cf (Λ M (cX A M w s))).toReal := by
    rw [Cf_partition A hP w, ENNReal.toReal_sum fun s _ => Cf_ne_top hP (measurableSet_cX A M w s)]
  have hW : (tr (Λ M (cP A M w))).toReal = ∑ s : Bool ⊕ Fin N, (tr (Λ M (cX A M w s))).toReal := by
    rw [pom_partition A hP w, ENNReal.toReal_sum fun s _ => tr_ne_top hP (measurableSet_cX A M w s)]
  unfold VL
  rw [hC, hW]
  exact TheoremS.Vf_finset_sum _ _ _ (fun s _ => ENNReal.toReal_nonneg)
    fun s _ => C_le_W hP (measurableSet_cX A M w s)

theorem VL_le_C {Λ : HistFam N (RK N K) Ω} {M : ℕ} (hP : IsPOM (Λ M)) {E : Set (Hist Ω M)}
    (hE : MeasurableSet E) : VL Λ M E ≤ (Real.pi / 8 + 1 / 4) * (Cf (Λ M E)).toReal :=
  TheoremS.Vf_le _ _ ENNReal.toReal_nonneg (C_le_W hP hE)

theorem VL_le_W {Λ : HistFam N (RK N K) Ω} {M : ℕ} (hP : IsPOM (Λ M)) {E : Set (Hist Ω M)}
    (hE : MeasurableSet E) : VL Λ M E ≤ (Real.pi / 8 + 1 / 4) * (tr (Λ M E)).toReal :=
  (VL_le_C hP hE).trans (mul_le_mul_of_nonneg_left (C_le_W hP hE) (by positivity))

end Measures

/-! ### (M3): one step of a non-halt cell -/

section Step

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

theorem step_op {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ) {M : ℕ}
    {E : Set (Hist Ω M)} (hE : MeasurableSet E) (hEk : E ⊆ A.kind M ⁻¹' {Kind.op}) :
    VL Λ M E = VL Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1))) := by
  obtain ⟨h1, h2⟩ := Alg.joint_op hΛ hE hEk
  unfold VL
  rw [h1, h2]

theorem step_query {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hN : 4 ≤ N) (hΛ : A.IsJoint Λ)
    {M : ℕ} {E : Set (Hist Ω M)} (hE : MeasurableSet E) (hEk : E ⊆ A.kind M ⁻¹' {Kind.query}) :
    kap N * VL Λ M E ≤
      kap N * VL Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1))) +
        (tr (Λ M E)).toReal := by
  obtain ⟨h1, h2⟩ := Alg.joint_query hΛ hE hEk
  have hY : PosTC (Λ M E) := posTC_of (hΛ.pom M) hE
  have hUY : PosTC (ctrlU ∘L Λ M E ∘L ContinuousLinearMap.adjoint ctrlU) :=
    ⟨hY.1.conj_adjoint ctrlU, by rw [tr_ctrlU hY]; exact hY.2⟩
  have hC : (Cf (Λ M E)).toReal ≤ (tr (Λ M E)).toReal := C_le_W (hΛ.pom M) hE
  have hC' : (Cf (ctrlU ∘L Λ M E ∘L ContinuousLinearMap.adjoint ctrlU)).toReal ≤
      (tr (Λ M E)).toReal := by
    have h := ENNReal.toReal_mono hUY.2.ne (Cf_le_tr hUY)
    rwa [tr_ctrlU hY] at h
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have key := TheoremS.Vf_query (Real.sqrt N) _ _ _ (two_le_sqrt hN) ENNReal.toReal_nonneg hC
    ENNReal.toReal_nonneg hC' (by rw [hsq]; exact cell_query (by omega) hY)
  unfold VL kap
  rw [h1, h2]
  linarith

end Step

/-! ### The potential -/

section Potential

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

/-- `∑_w V(cP M w)`: all non-halted cells of depth `M`. -/
def dSum (A : Alg N K Ω) (Λ : HistFam N (RK N K) Ω) (M : ℕ) : ℝ :=
  ∑ w : Fin M → Bool, VL Λ M (cP A M w)

/-- `∑` of `V` over the halt cells of depth `m`. -/
def hSum (A : Alg N K Ω) (Λ : HistFam N (RK N K) Ω) (m : ℕ) : ℝ :=
  ∑ w : Fin m → Bool, ∑ y : Fin N, VL Λ m (cX A m w (Sum.inr y))

/-- `∑` of `W` over the query cells of depth `m`. -/
def qSum (A : Alg N K Ω) (Λ : HistFam N (RK N K) Ω) (m : ℕ) : ℝ :=
  ∑ w : Fin m → Bool, (tr (Λ m (cX A m w (Sum.inl true)))).toReal

/-- The potential `Φ_M`. -/
def Phi (A : Alg N K Ω) (Λ : HistFam N (RK N K) Ω) (M : ℕ) : ℝ :=
  kap N * (∑ m ∈ Finset.range M, hSum A Λ m + dSum A Λ M) + ∑ m ∈ Finset.range M, qSum A Λ m

theorem sum_snoc {M : ℕ} (g : (Fin (M + 1) → Bool) → ℝ) :
    ∑ w, g w = ∑ w : Fin M → Bool, ∑ b : Bool, g (Fin.snoc (α := fun _ => Bool) w b) := by
  have h1 := Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (M + 1) => Bool))
    (fun p => g (Fin.snoc (α := fun _ => Bool) p.2 p.1)) g (fun p => rfl)
  rw [← h1, Fintype.sum_prod_type]
  exact Finset.sum_comm

variable [TopologicalSpace.SeparableSpace K]

theorem dSum_step {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hN : 4 ≤ N) (hΛ : A.IsJoint Λ)
    (M : ℕ) : kap N * dSum A Λ M ≤ kap N * (hSum A Λ M + dSum A Λ (M + 1)) + qSum A Λ M := by
  have hk := kap_pos hN
  have hw : ∀ w : Fin M → Bool, kap N * VL Λ M (cP A M w) ≤
      kap N * (∑ y : Fin N, VL Λ M (cX A M w (Sum.inr y)) +
        ∑ b : Bool, VL Λ (M + 1) (cP A (M + 1) (Fin.snoc (α := fun _ => Bool) w b))) +
      (tr (Λ M (cX A M w (Sum.inl true)))).toReal := by
    intro w
    have hsplit := V_partition A (hΛ.pom M) w
    rw [Fintype.sum_sum_type, Fintype.sum_bool] at hsplit
    have hop := step_op hΛ (measurableSet_cX A M w (Sum.inl false)) (cX_sub A M w (Sum.inl false))
    have hq := step_query hN hΛ (measurableSet_cX A M w (Sum.inl true))
      (cX_sub A M w (Sum.inl true))
    rw [Fintype.sum_bool, cP_snoc, cP_snoc, ← hop]
    have h3 := mul_le_mul_of_nonneg_left hsplit hk.le
    linarith
  have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hw w
  have hD1 : dSum A Λ (M + 1) = ∑ w : Fin M → Bool, ∑ b : Bool,
      VL Λ (M + 1) (cP A (M + 1) (Fin.snoc (α := fun _ => Bool) w b)) :=
    sum_snoc (fun w => VL Λ (M + 1) (cP A (M + 1) w))
  rw [hD1]
  simp only [dSum, hSum, qSum, mul_add, Finset.mul_sum, Finset.sum_add_distrib] at hsum ⊢
  linarith

theorem Phi_mono {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hN : 4 ≤ N) (hΛ : A.IsJoint Λ)
    (M : ℕ) : Phi A Λ M ≤ Phi A Λ (M + 1) := by
  have h := dSum_step hN hΛ M
  simp only [Phi, Finset.sum_range_succ]
  linarith

omit [TopologicalSpace.SeparableSpace K] in
theorem Phi_zero {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ) :
    Phi A Λ 0 = kap N * (Real.pi / 8 + 1 / 4) := by
  have hy : ∀ z, ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) (uEmb z) = z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, adjoint_uEmb_comp_uEmb, ContinuousLinearMap.id_apply]
  have hid : ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) ∘L
      (uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb) ∘L uEmb = A.rho0 := by
    ext1 v
    simp only [ContinuousLinearMap.comp_apply, hy]
  have hC : Cf (Λ 0 Set.univ) = 1 := by rw [hΛ.init, Cf, hid, A.rho0_tr]
  have hW : tr (Λ 0 Set.univ) = 1 := by rw [hΛ.init, tr_uEmb_conj A.rho0_pos, A.rho0_tr]
  have hD : dSum A Λ 0 = Real.pi / 8 + 1 / 4 := by
    rw [dSum, Fintype.sum_unique]
    show TheoremS.Vf (Cf (Λ 0 Set.univ)).toReal (tr (Λ 0 Set.univ)).toReal = _
    rw [hC, hW, ENNReal.toReal_one, TheoremS.Vf_self 1 zero_le_one, mul_one]
  simp only [Phi, Finset.range_zero, Finset.sum_empty, zero_add, add_zero, hD]

end Potential

/-! ### The end: halt cells, query cells, the non-halted rest -/

section End

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

theorem haltR0 {A : Alg N K Ω} {x : Fin N} {ρx : HistFam N K Ω} (hρx : A.IsHistory x ρx) (M : ℕ) :
    (∑ m ∈ Finset.range M, ∑ y : Fin N, tr (ρx m (A.kind m ⁻¹' {Kind.halt y}))).toReal +
      (tr (ρx M Set.univ)).toReal = 1 := by
  have h := congrArg ENNReal.toReal (Alg.sum_halt_add_tr_univ hρx M)
  have hs : ∑ m ∈ Finset.range M, ∑ y : Fin N, tr (ρx m (A.kind m ⁻¹' {Kind.halt y})) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun m _ => ENNReal.sum_ne_top.2 fun y _ => tr_ne_top (hρx.pom m) (kmeas A m _)
  rwa [ENNReal.toReal_add hs (tr_ne_top (hρx.pom M) MeasurableSet.univ), ENNReal.toReal_one] at h

theorem haltR {A : Alg N K Ω} {x : Fin N} {ρx : HistFam N K Ω} (hρx : A.IsHistory x ρx) (M : ℕ) :
    ∑ m ∈ Finset.range M, ∑ y : Fin N, (tr (ρx m (A.kind m ⁻¹' {Kind.halt y}))).toReal +
      (tr (ρx M Set.univ)).toReal = 1 := by
  have e : ∀ m, (∑ y : Fin N, tr (ρx m (A.kind m ⁻¹' {Kind.halt y}))).toReal =
      ∑ y : Fin N, (tr (ρx m (A.kind m ⁻¹' {Kind.halt y}))).toReal :=
    fun m => ENNReal.toReal_sum fun y _ => tr_ne_top (hρx.pom m) (kmeas A m _)
  have h := haltR0 hρx M
  rw [ENNReal.toReal_sum fun m _ =>
    ENNReal.sum_ne_top.2 fun y _ => tr_ne_top (hρx.pom m) (kmeas A m _)] at h
  simpa only [e] using h

/-- Under zero error, the non-halted mass `∑_x tr ρ_x^{(M)}(X_M)` tends to `0`. -/
theorem eps_tendsto {A : Alg N K Ω} {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x))
    (hz : A.ZeroError ρ) :
    Tendsto (fun M => ∑ x : Fin N, (tr (ρ x M Set.univ)).toReal) atTop (𝓝 0) := by
  have h : ∀ x : Fin N, Tendsto (fun M => (tr (ρ x M Set.univ)).toReal) atTop (𝓝 0) := by
    intro x
    have hsum1 : ∑' m, ∑ y : Fin N, tr (ρ x m (A.kind m ⁻¹' {Kind.halt y})) = 1 := by
      refine le_antisymm (Alg.tsum_halt_le_one (hρ x)) ?_
      calc (1 : ℝ≥0∞) = A.success (ρ x) x := (hz x).symm
        _ ≤ ∑' m, ∑ y : Fin N, tr (ρ x m (A.kind m ⁻¹' {Kind.halt y})) :=
          ENNReal.tsum_le_tsum fun m =>
            Finset.single_le_sum (f := fun y => tr (ρ x m (A.kind m ⁻¹' {Kind.halt y})))
              (fun y _ => zero_le) (Finset.mem_univ x)
    have hs : Tendsto (fun n => ∑ m ∈ Finset.range n, ∑ y : Fin N,
        tr (ρ x m (A.kind m ⁻¹' {Kind.halt y}))) atTop (𝓝 1) := by
      have h0 := ENNReal.tendsto_nat_tsum
        (fun m => ∑ y : Fin N, tr (ρ x m (A.kind m ⁻¹' {Kind.halt y})))
      rw [hsum1] at h0
      exact h0
    have hs' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hs
    rw [ENNReal.toReal_one] at hs'
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hlim := hc.sub hs'
    rw [sub_self] at hlim
    refine Filter.Tendsto.congr (fun M => ?_) hlim
    show (1 : ℝ) - (∑ m ∈ Finset.range M, ∑ y : Fin N,
      tr (ρ x m (A.kind m ⁻¹' {Kind.halt y}))).toReal = (tr (ρ x M Set.univ)).toReal
    linarith [haltR0 (hρ x) M]
  have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun x _ => h x
  rw [Finset.sum_const_zero] at h2
  exact h2

variable [∀ m, Nonempty (Ω m)]

theorem trR_joint {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ)
    {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x)) (m : ℕ) (E : Set (Hist Ω m))
    (hE : MeasurableSet E) : (N : ℝ) * (tr (Λ m E)).toReal = ∑ x : Fin N, (tr (ρ x m E)).toReal := by
  have h := congrArg ENNReal.toReal (Alg.tr_joint hΛ hρ m E hE)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun x _ => tr_ne_top ((hρ x).pom m) hE] at h

/-- A halt cell with output `y`: `p_x = 0` for `x ≠ y`, so `N C = W` (`cell_single`). -/
theorem halt_cell {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ)
    {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x)) (hz : A.ZeroError ρ) (M : ℕ)
    (w : Fin M → Bool) (y : Fin N) :
    (N : ℝ) * (Cf (Λ M (cX A M w (Sum.inr y)))).toReal = (tr (Λ M (cX A M w (Sum.inr y)))).toReal := by
  have hE := measurableSet_cX A M w (Sum.inr y)
  have h := cell_single (posTC_of (hΛ.pom M) hE) y fun x hxy => by
    rw [Alg.beta_joint hΛ (hρ x) M _ hE]
    refine le_antisymm ?_ zero_le
    calc tr (ρ x M (cX A M w (Sum.inr y))) ≤ tr (ρ x M (A.kind M ⁻¹' {Kind.halt y})) :=
          tr_mono_pom ((hρ x).pom M) hE (kmeas A M _) (cX_sub A M w (Sum.inr y))
      _ = 0 := Alg.halt_ne_eq_zero (hρ x) (hz x) M y (Ne.symm hxy)
  have h2 := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2

theorem hSum_le {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ)
    {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x)) (hz : A.ZeroError ρ) (m : ℕ) :
    (N : ℝ) * hSum A Λ m ≤ (Real.pi / 8 + 1 / 4) *
      ∑ w : Fin m → Bool, ∑ y : Fin N, (tr (Λ m (cX A m w (Sum.inr y)))).toReal := by
  unfold hSum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h1 := VL_le_C (hΛ.pom m) (measurableSet_cX A m w (Sum.inr y))
  have h2 := halt_cell hΛ hρ hz m w y
  have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h4 : (Real.pi / 8 + 1 / 4) * ((N : ℝ) * (Cf (Λ m (cX A m w (Sum.inr y)))).toReal) =
      (Real.pi / 8 + 1 / 4) * (tr (Λ m (cX A m w (Sum.inr y)))).toReal := by rw [h2]
  linarith

/-- The halt cells of depth `< M` carry total `W ≤ 1`. -/
theorem halt_total {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hN : 4 ≤ N) (hΛ : A.IsJoint Λ)
    {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x)) (M : ℕ) :
    ∑ m ∈ Finset.range M, ∑ w : Fin m → Bool, ∑ y : Fin N,
      (tr (Λ m (cX A m w (Sum.inr y)))).toReal ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : ∑ m ∈ Finset.range M, ∑ w : Fin m → Bool, ∑ y : Fin N,
      (tr (Λ m (cX A m w (Sum.inr y)))).toReal ≤
      ∑ m ∈ Finset.range M, ∑ y : Fin N, (tr (Λ m (A.kind m ⁻¹' {Kind.halt y}))).toReal := by
    refine Finset.sum_le_sum fun m _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun y _ => sumR_cP_le A (hΛ.pom m) (kmeas A m {Kind.halt y})
  have h2 : (N : ℝ) * ∑ m ∈ Finset.range M, ∑ y : Fin N,
      (tr (Λ m (A.kind m ⁻¹' {Kind.halt y}))).toReal ≤ (N : ℝ) * 1 := by
    calc (N : ℝ) * ∑ m ∈ Finset.range M, ∑ y : Fin N, (tr (Λ m (A.kind m ⁻¹' {Kind.halt y}))).toReal
        = ∑ m ∈ Finset.range M, ∑ y : Fin N, ∑ x : Fin N,
            (tr (ρ x m (A.kind m ⁻¹' {Kind.halt y}))).toReal := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => trR_joint hΛ hρ m _ (kmeas A m _)
      _ = ∑ m ∈ Finset.range M, ∑ x : Fin N, ∑ y : Fin N,
            (tr (ρ x m (A.kind m ⁻¹' {Kind.halt y}))).toReal :=
          Finset.sum_congr rfl fun m _ => Finset.sum_comm
      _ = ∑ x : Fin N, ∑ m ∈ Finset.range M, ∑ y : Fin N,
            (tr (ρ x m (A.kind m ⁻¹' {Kind.halt y}))).toReal := Finset.sum_comm
      _ ≤ ∑ x : Fin N, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
          have := haltR (hρ x) M
          linarith [ENNReal.toReal_nonneg (a := tr (ρ x M Set.univ))]
      _ = (N : ℝ) * 1 := by simp
  exact h1.trans (le_of_mul_le_mul_left h2 hN0)

/-- The query cells of depth `< M`: `N ∑ W ≤ ∑_x T_x`. -/
theorem query_total {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ)
    {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x)) (hc : ∑ x, A.cost (ρ x) ≠ ⊤)
    (M : ℕ) : (N : ℝ) * ∑ m ∈ Finset.range M, qSum A Λ m ≤ (∑ x, A.cost (ρ x)).toReal := by
  have h1 : ∑ m ∈ Finset.range M, qSum A Λ m ≤
      ∑ m ∈ Finset.range M, (tr (Λ m (A.kind m ⁻¹' {Kind.query}))).toReal :=
    Finset.sum_le_sum fun m _ => sumR_cP_le A (hΛ.pom m) (kmeas A m {Kind.query})
  have hcx : ∀ x, A.cost (ρ x) ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top hc (Finset.single_le_sum (f := fun j => A.cost (ρ j))
      (fun j _ => zero_le) (Finset.mem_univ x))
  calc (N : ℝ) * ∑ m ∈ Finset.range M, qSum A Λ m
      ≤ (N : ℝ) * ∑ m ∈ Finset.range M, (tr (Λ m (A.kind m ⁻¹' {Kind.query}))).toReal :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)
    _ = ∑ m ∈ Finset.range M, ∑ x : Fin N, (tr (ρ x m (A.kind m ⁻¹' {Kind.query}))).toReal := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => trR_joint hΛ hρ m _ (kmeas A m _)
    _ = ∑ x : Fin N, ∑ m ∈ Finset.range M, (tr (ρ x m (A.kind m ⁻¹' {Kind.query}))).toReal :=
        Finset.sum_comm
    _ ≤ ∑ x : Fin N, (A.cost (ρ x)).toReal :=
        Finset.sum_le_sum fun x _ => toReal_sum_le _ _ (hcx x) (ENNReal.sum_le_tsum (Finset.range M))
    _ = (∑ x, A.cost (ρ x)).toReal := (ENNReal.toReal_sum fun x _ => hcx x).symm

omit [TopologicalSpace.SeparableSpace K] [∀ m, Nonempty (Ω m)] in
theorem dSum_le {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ) (M : ℕ) :
    dSum A Λ M ≤ (Real.pi / 8 + 1 / 4) * (tr (Λ M Set.univ)).toReal := by
  have h1 := sumR_cP_le A (hΛ.pom M) (S := Set.univ) MeasurableSet.univ
  simp only [Set.inter_univ] at h1
  unfold dSum
  calc ∑ w : Fin M → Bool, VL Λ M (cP A M w)
      ≤ ∑ w : Fin M → Bool, (Real.pi / 8 + 1 / 4) * (tr (Λ M (cP A M w))).toReal :=
        Finset.sum_le_sum fun w _ => VL_le_W (hΛ.pom M) (measurableSet_cP A M w)
    _ = (Real.pi / 8 + 1 / 4) * ∑ w : Fin M → Bool, (tr (Λ M (cP A M w))).toReal :=
        (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem NdSum_le {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hΛ : A.IsJoint Λ)
    {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x)) (M : ℕ) :
    (N : ℝ) * dSum A Λ M ≤ (Real.pi / 8 + 1 / 4) * ∑ x : Fin N, (tr (ρ x M Set.univ)).toReal := by
  rw [← trR_joint hΛ hρ M Set.univ MeasurableSet.univ]
  have h2 := mul_le_mul_of_nonneg_left (dSum_le hΛ M) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  linarith

/-- For each `M`: `N κ γ ≤ κ γ + κ γ ε_M + ∑_x T_x`. -/
theorem main_ineq {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω} (hN : 4 ≤ N) (hΛ : A.IsJoint Λ)
    {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x)) (hz : A.ZeroError ρ)
    (hc : ∑ x, A.cost (ρ x) ≠ ⊤) (M : ℕ) :
    (N : ℝ) * (kap N * (Real.pi / 8 + 1 / 4)) ≤
      kap N * (Real.pi / 8 + 1 / 4) +
        kap N * ((Real.pi / 8 + 1 / 4) * ∑ x : Fin N, (tr (ρ x M Set.univ)).toReal) +
        (∑ x, A.cost (ρ x)).toReal := by
  have hk := kap_pos hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h0 : Phi A Λ 0 ≤ Phi A Λ M := monotone_nat_of_le_succ (Phi_mono hN hΛ) (Nat.zero_le M)
  rw [Phi_zero hΛ] at h0
  have hH : (N : ℝ) * ∑ m ∈ Finset.range M, hSum A Λ m ≤ Real.pi / 8 + 1 / 4 := by
    rw [Finset.mul_sum]
    calc ∑ m ∈ Finset.range M, (N : ℝ) * hSum A Λ m
        ≤ ∑ m ∈ Finset.range M, (Real.pi / 8 + 1 / 4) *
            ∑ w : Fin m → Bool, ∑ y : Fin N, (tr (Λ m (cX A m w (Sum.inr y)))).toReal :=
          Finset.sum_le_sum fun m _ => hSum_le hΛ hρ hz m
      _ = (Real.pi / 8 + 1 / 4) * ∑ m ∈ Finset.range M,
            ∑ w : Fin m → Bool, ∑ y : Fin N, (tr (Λ m (cX A m w (Sum.inr y)))).toReal :=
          (Finset.mul_sum ..).symm
      _ ≤ (Real.pi / 8 + 1 / 4) * 1 :=
          mul_le_mul_of_nonneg_left (halt_total hN hΛ hρ M) (by positivity)
      _ = Real.pi / 8 + 1 / 4 := mul_one _
  have hD := NdSum_le hΛ hρ M
  have hQ := query_total hΛ hρ hc M
  have e1 := mul_le_mul_of_nonneg_left hH hk.le
  have e2 := mul_le_mul_of_nonneg_left hD hk.le
  have e0 := mul_le_mul_of_nonneg_left h0 hN0
  simp only [Phi] at e0
  linarith

/-- Letting `M → ∞`: `N κ γ ≤ κ γ + ∑_x T_x`. -/
theorem main_limit {A : Alg N K Ω} (hN : 4 ≤ N) {ρ : Fin N → HistFam N K Ω}
    (hρ : ∀ x, A.IsHistory x (ρ x)) (hz : A.ZeroError ρ) (hc : ∑ x, A.cost (ρ x) ≠ ⊤) :
    (N : ℝ) * (kap N * (Real.pi / 8 + 1 / 4)) ≤
      kap N * (Real.pi / 8 + 1 / 4) + (∑ x, A.cost (ρ x)).toReal := by
  obtain ⟨Λ, hΛ⟩ := Alg.exists_joint A
  have hε := eps_tendsto hρ hz
  have hlim : Tendsto (fun M => kap N * (Real.pi / 8 + 1 / 4) +
      kap N * ((Real.pi / 8 + 1 / 4) * ∑ x : Fin N, (tr (ρ x M Set.univ)).toReal) +
        (∑ x, A.cost (ρ x)).toReal) atTop
      (𝓝 (kap N * (Real.pi / 8 + 1 / 4) + kap N * ((Real.pi / 8 + 1 / 4) * 0) +
        (∑ x, A.cost (ρ x)).toReal)) :=
    (tendsto_const_nhds.add ((hε.const_mul _).const_mul _)).add tendsto_const_nhds
  rw [mul_zero, mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim fun M => main_ineq hN hΛ hρ hz hc M

end End

theorem final_ineq {n k R : ℝ} (hn : 0 < n) (hk : 0 ≤ k) (h : n * k ≤ k + R) :
    k * (1 - 2 / n) ≤ R / n := by
  rw [le_div_iff₀ hn, mul_assoc, sub_mul, one_mul, div_mul_cancel₀ (2 : ℝ) hn.ne']
  linarith

end Bound

/-! ### The targets -/

/-- Theorem thm:S-meas for arbitrary nonempty measurable outcome spaces (`TheoremSMeasGen`). -/
theorem theoremSMeasGen : TheoremSMeasGen := by
  intro N hN K _ _ _ _ Ω _ _ A ρ hρ hz
  by_cases htop : ∑ x, A.cost (ρ x) = ⊤
  · rw [htop, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top N)]
    exact le_top
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNe : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.div_ne_top htop hNe), ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  have hk : 0 ≤ Bound.kap N * (Real.pi / 8 + 1 / 4) := by
    have := Bound.kap_pos hN
    positivity
  exact Bound.final_ineq hN0 hk (Bound.main_limit hN hρ hz htop)

/-- The explicit form `(π/8 + 1/4)√N - 4/√N` (`TheoremSMeasGen'`), from `kappa_end` with `t = √N`. -/
theorem theoremSMeasGen' : TheoremSMeasGen' := by
  intro N hN K _ _ _ _ Ω _ _ A ρ hρ hz
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (theoremSMeasGen N hN K Ω A ρ hρ hz)
  have h := TheoremS.kappa_end (Real.sqrt N) (Bound.two_le_sqrt hN)
  rw [Real.sq_sqrt (Nat.cast_nonneg N)] at h
  exact h.trans_eq (by ring)

/-- Theorem thm:S-meas (`TheoremSMeas`); the standard Borel hypothesis is not used. -/
theorem theoremSMeas : TheoremSMeas := by
  intro N hN K _ _ _ _ Ω _ _ _ A ρ hρ hz
  exact theoremSMeasGen N hN K Ω A ρ hρ hz

/-- Theorem thm:S-meas, explicit form (`TheoremSMeas'`). -/
theorem theoremSMeas' : TheoremSMeas' := by
  intro N hN K _ _ _ _ Ω _ _ _ A ρ hρ hz
  exact theoremSMeasGen' N hN K Ω A ρ hρ hz

end

end TheoremS.Meas
