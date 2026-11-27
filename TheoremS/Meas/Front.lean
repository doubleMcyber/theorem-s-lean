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
Lemma lem:m-front (frontier) of the paper's section on measurable outcome spaces: truncation of histories
`h|_m`, the set `A_M` of histories that halted before depth `M`, and claims (i) to (iii) for a history family
`ρ` of an `Alg`.
-/
import TheoremS.Meas.Hist

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

/-! ### Truncation of histories -/

/-- The truncation `h|_m ∈ X_m` of a history `h ∈ X_M` to its first `m` coordinates, `m ≤ M`
(Definition def:s-meas, item 2). With `Hist Ω (M+1) = Hist Ω M × Ω M`, `h|_{M+1} = h` and
`(h, ω)|_m = h|_m` for `m ≤ M`. -/
def Hist.trunc {Ω : ℕ → Type} : {M : ℕ} → Hist Ω M → (m : ℕ) → m ≤ M → Hist Ω m
  | 0, h, m, hm => cast (congrArg (Hist Ω) (Nat.le_zero.mp hm).symm) h
  | M + 1, h, m, hm =>
    if hmM : m = M + 1 then cast (congrArg (Hist Ω) hmM.symm) h
    else Hist.trunc (Prod.fst (α := Hist Ω M) (β := Ω M) h) m (by omega)

/-- `h|_M = h` for `h` of depth `M`. -/
theorem Hist.trunc_self {Ω : ℕ → Type} {M : ℕ} (h : Hist Ω M) : h.trunc M le_rfl = h := by
  cases M <;> simp [Hist.trunc]

/-- `(h, ω)|_m = h|_m` for `m ≤ M`. -/
theorem Hist.trunc_cons {Ω : ℕ → Type} {M : ℕ} (h : Hist Ω M) (ω : Ω M) (m : ℕ) (hm : m ≤ M) :
    (Hist.cons h ω).trunc m (hm.trans M.le_succ) = h.trunc m hm := by
  have hne : m ≠ M + 1 := by omega
  simp [Hist.trunc, Hist.cons, hne]

/-- `h|_m = (h.1)|_m` for `h` of depth `M + 1` and `m ≤ M`. -/
private theorem front_trunc_fst {Ω : ℕ → Type} {M : ℕ} (h : Hist Ω (M + 1)) (m : ℕ) (hm : m ≤ M) :
    h.trunc m (hm.trans M.le_succ) = (Prod.fst (α := Hist Ω M) (β := Ω M) h).trunc m hm :=
  Hist.trunc_cons (Prod.fst (α := Hist Ω M) (β := Ω M) h) (Prod.snd (α := Hist Ω M) (β := Ω M) h) m hm

/-- `h|_M = h.1` for `h` of depth `M + 1`. -/
private theorem front_trunc_succ_self {Ω : ℕ → Type} {M : ℕ} (h : Hist Ω (M + 1)) (hm : M ≤ M + 1) :
    h.trunc M hm = Prod.fst (α := Hist Ω M) (β := Ω M) h := by
  have h1 := front_trunc_fst h M le_rfl
  rw [Hist.trunc_self] at h1
  exact h1

/-- Truncation `h ↦ h|_m` is measurable for the product σ-algebras (used in the proof of lem:m-front(ii):
"`A_M` is measurable since `h ↦ h|_m` and `k_m` are"). -/
theorem Hist.measurable_trunc {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)] {M : ℕ} (m : ℕ)
    (hm : m ≤ M) : Measurable (fun h : Hist Ω M => h.trunc m hm) := by
  induction M generalizing m with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    have h1 : (fun h : Hist Ω 0 => h.trunc 0 hm) = id := funext fun h => Hist.trunc_self h
    rw [h1]
    exact measurable_id
  | succ M ih =>
    by_cases hmM : m = M + 1
    · subst hmM
      have h1 : (fun h : Hist Ω (M + 1) => h.trunc (M + 1) hm) = id :=
        funext fun h => Hist.trunc_self h
      rw [h1]
      exact measurable_id
    · have hle : m ≤ M := by omega
      have h1 : (fun h : Hist Ω (M + 1) => h.trunc m hm) =
          fun h => (Prod.fst (α := Hist Ω M) (β := Ω M) h).trunc m hle :=
        funext fun h => front_trunc_fst h m hle
      rw [h1]
      exact (ih m hle).comp measurable_fst

namespace Alg

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

/-- The set `A_M = {h ∈ X_M : k_m(h|_m) ∈ [N] for some m < M}` of histories that halted before depth `M`
(Lemma lem:m-front(ii)). -/
def haltedBefore (A : Alg N K Ω) (M : ℕ) : Set (Hist Ω M) :=
  {h | ∃ m, ∃ hm : m < M, ∃ y : Fin N, A.kind m (h.trunc m hm.le) = Kind.halt y}

/-- `A_M` is measurable (proof of lem:m-front(ii)). -/
theorem measurableSet_haltedBefore (A : Alg N K Ω) (M : ℕ) : MeasurableSet (A.haltedBefore M) := by
  have h1 : A.haltedBefore M = ⋃ (m : Fin M) (y : Fin N),
      (fun h : Hist Ω M => A.kind m (h.trunc m m.isLt.le)) ⁻¹' {Kind.halt y} := by
    ext h
    simp only [haltedBefore, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, hm, y, hy⟩
      exact ⟨⟨m, hm⟩, y, hy⟩
    · rintro ⟨m, y, hy⟩
      exact ⟨m, m.isLt, y, hy⟩
  rw [h1]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun y =>
    ((A.kind_meas m).comp (Hist.measurable_trunc (Ω := Ω) m m.isLt.le))
      MeasurableSpace.measurableSet_top

/-! #### Helpers -/

/-- The cylinder `E × Ω_M` over `E ⊆ X_M`, as a set of histories of depth `M + 1`. -/
private def prodU {M : ℕ} (E : Set (Hist Ω M)) : Set (Hist Ω (M + 1)) :=
  (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω M × Ω M))

private theorem front_measurableSet_prodU {M : ℕ} {E : Set (Hist Ω M)} (hE : MeasurableSet E) :
    MeasurableSet (prodU E) :=
  hE.prod MeasurableSet.univ

omit [∀ m, MeasurableSpace (Ω m)] in
private theorem front_sect_prodU {M : ℕ} (E : Set (Hist Ω M)) (h : Hist Ω M) :
    Hist.sect (prodU E) h = Prod.mk h ⁻¹' (E ×ˢ (Set.univ : Set (Ω M))) :=
  rfl

omit [∀ m, MeasurableSpace (Ω m)] in
private theorem front_prodU_univ {M : ℕ} : prodU (Set.univ : Set (Hist Ω M)) = Set.univ :=
  Set.univ_prod_univ

private theorem front_kind_cases (k : Kind N) :
    k = Kind.op ∨ k = Kind.query ∨ ∃ y, k = Kind.halt y := by
  cases k with
  | op => exact Or.inl rfl
  | query => exact Or.inr (Or.inl rfl)
  | halt y => exact Or.inr (Or.inr ⟨y, rfl⟩)

private theorem front_stepKraus_op (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M)
    (hk : A.kind M h = Kind.op) : A.stepKraus x M h = A.kraus M h := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem front_stepKraus_query (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M)
    (hk : A.kind M h = Kind.query) :
    A.stepKraus x M h = fun F k => A.kraus M h F k ∘L oracleL x := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem front_stepKraus_halt (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M) {y : Fin N}
    (hk : A.kind M h = Kind.halt y) : A.stepKraus x M h = fun _ _ => 0 := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem front_oracleL_adjoint (x : Fin N) :
    ContinuousLinearMap.adjoint (oracleL (K := K) x) =
      (oracle x).symm.toLinearIsometry.toContinuousLinearMap := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  show ⟪(oracle x).symm u, v⟫_ℂ = ⟪u, (oracle x) v⟫_ℂ
  rw [← (oracle x).inner_map_map ((oracle x).symm u) v, LinearIsometryEquiv.apply_symm_apply]

private theorem front_tr_zero : tr (0 : Op N K) = 0 := by
  simp [tr]

private theorem front_meas_kind (A : Alg N K Ω) (M : ℕ) (T : Set (Kind N)) :
    MeasurableSet (A.kind M ⁻¹' T) :=
  A.kind_meas M MeasurableSpace.measurableSet_top

/-- The set `A_M ∪ k_M⁻¹([N])` of depth-`M` histories that halted before or at depth `M`. -/
private def frontE (A : Alg N K Ω) (M : ℕ) : Set (Hist Ω M) :=
  A.haltedBefore M ∪ ⋃ y : Fin N, A.kind M ⁻¹' {Kind.halt y}

private theorem front_haltedBefore_succ_subset (A : Alg N K Ω) (M : ℕ) :
    A.haltedBefore (M + 1) ⊆ prodU (frontE A M) := by
  intro h hh
  obtain ⟨m, hm, y, hk⟩ := hh
  show Prod.fst (α := Hist Ω M) (β := Ω M) h ∈
      A.haltedBefore M ∪ ⋃ y : Fin N, A.kind M ⁻¹' {Kind.halt y} ∧
    Prod.snd (α := Hist Ω M) (β := Ω M) h ∈ (Set.univ : Set (Ω M))
  refine ⟨?_, Set.mem_univ _⟩
  by_cases hmM : m = M
  · subst hmM
    rw [front_trunc_succ_self] at hk
    exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨y, hk⟩)
  · have hlt : m < M := by omega
    rw [front_trunc_fst h m hlt.le] at hk
    exact Set.mem_union_left _ ⟨m, hlt, y, hk⟩

variable [TopologicalSpace.SeparableSpace K] {A : Alg N K Ω} {x : Fin N} {ρ : HistFam N K Ω}

set_option maxHeartbeats 400000 in
/-- The core of lem:m-front: for a density `τ` of `ρ^{(M)}` (so `τ = tr ρ^{(M)}`),
`tr ρ^{(M+1)}(E × Ω_M) = τ(E ∩ k_M⁻¹({o, q}))`, since `tr Ξ_{M,h}(Ω_M)(σ(h))` is `1` on operation and
query kinds and `0` on halt kinds. -/
private theorem front_core (hρ : A.IsHistory x ρ) (M : ℕ) :
    ∃ τ : Measure (Hist Ω M), (∀ E, MeasurableSet E → τ E = tr (ρ M E)) ∧
      ∀ E, MeasurableSet E →
        tr (ρ (M + 1) (prodU E)) = τ (E ∩ A.kind M ⁻¹' {Kind.op, Kind.query}) := by
  obtain ⟨τ, σ, hd, heq⟩ := hρ.step M
  have := hd.finite
  refine ⟨τ, fun E hE => hd.apply_eq_tr hE, fun E hE => ?_⟩
  have hK := A.isKrausKernel_stepKraus x M
  have hfin : ∀ h, tr (σ h) < ∞ := fun h => by rw [hd.trace_one h]; exact ENNReal.one_lt_top
  have hfinB : ∀ h, trB (hbasis N K) (σ h) < ∞ := fun h => by rw [← tr_eq_trB]; exact hfin h
  have hZex : ∀ h, ∃ Z : Op N K, Z.IsPositive ∧
      ∀ a c, ⟪a, Z c⟫_ℂ = krausMat (A.stepKraus x M h Set.univ) (σ h) a c := fun h =>
    exists_krausOp (b := hbasis N K) (hK.bounded h Set.univ MeasurableSet.univ) (hd.pos h)
      (hfinB h)
  choose Z hZpos hZ using hZex
  have hS := front_meas_kind A M ({Kind.op, Kind.query} : Set (Kind N))
  have hZtr : ∀ h, tr (Z h) =
      (A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N))).indicator 1 h := by
    intro h
    rcases front_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
    · have hmem : h ∈ A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N)) := by simp [hk]
      have hZ' : ∀ a c, ⟪a, Z h c⟫_ℂ = krausMatG (A.kraus M h Set.univ) (σ h) a c := by
        intro a c
        rw [hZ, front_stepKraus_op A x M h hk, krausMat_eq_krausMatG]
      rw [Set.indicator_of_mem hmem, Pi.one_apply, tr_eq_trB,
        trB_eq_of_krausMatG (b := hbasis N K) (b' := hbasis N K) (A.normalised M h) (hd.pos h)
          (hfinB h) hZ', ← tr_eq_trB, hd.trace_one h]
    · have hmem : h ∈ A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N)) := by simp [hk]
      have hZ' : ∀ a c, ⟪a, Z h c⟫_ℂ = krausMatG (A.kraus M h Set.univ)
          (oracleL x ∘L σ h ∘L ContinuousLinearMap.adjoint (oracleL x)) a c := by
        intro a c
        rw [hZ, front_stepKraus_query A x M h hk]
        simp only [krausMat_eq_krausMatG, krausMatG_comp]
      have hconj : trB (hbasis N K)
          (oracleL x ∘L σ h ∘L ContinuousLinearMap.adjoint (oracleL x)) = tr (σ h) := by
        rw [front_oracleL_adjoint, tr_eq_trB]
        unfold oracleL
        rw [trB_conj (b := hbasis N K) (oracle x) (hd.pos h)]
      rw [Set.indicator_of_mem hmem, Pi.one_apply, tr_eq_trB,
        trB_eq_of_krausMatG (b := hbasis N K) (b' := hbasis N K) (A.normalised M h)
          ((hd.pos h).conj_adjoint (oracleL x)) (by rw [hconj]; exact hfin h) hZ',
        hconj, hd.trace_one h]
    · have hmem : h ∉ A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N)) := by simp [hk]
      have hZ0 : Z h = 0 := by
        ext1 c
        refine ext_inner_left ℂ fun a => ?_
        rw [hZ, front_stepKraus_halt A x M h hk]
        simp [krausMat]
      rw [Set.indicator_of_notMem hmem, hZ0, front_tr_zero]
  have hmeasZ : ∀ a b : H N K, Measurable (fun h => ⟪a, Z h b⟫_ℂ) := by
    intro a b
    have hm := hK.measurable_sect_field (G := Set.univ) MeasurableSet.univ hd.pos hfin hd.meas a b
    simp only [Set.preimage_univ] at hm
    simp only [hZ]
    exact hm
  have hlint : ∫⁻ h, tr (Z h) ∂(τ.restrict E) < ∞ := by
    calc ∫⁻ h, tr (Z h) ∂(τ.restrict E) ≤ ∫⁻ _, 1 ∂(τ.restrict E) := by
          refine lintegral_mono fun h => ?_
          rw [hZtr]
          by_cases hh : h ∈ A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N))
          · simp [Set.indicator_of_mem hh]
          · simp [Set.indicator_of_notMem hh]
      _ < ∞ := by
          rw [lintegral_const, one_mul]
          exact measure_lt_top _ _
  obtain ⟨Y, -, hYtr, hYm⟩ := exists_weakInt (τ := τ.restrict E) hZpos hmeasZ hlint
  have hYE : Y = ρ (M + 1) (prodU E) := by
    ext1 b
    refine ext_inner_left ℂ fun a => ?_
    rw [hYm, heq (prodU E) (front_measurableSet_prodU hE) a b]
    simp only [hZ, A.stepMat_eq, front_sect_prodU]
    exact (hK.integral_sect_prod_univ hd hE a b).symm
  rw [← hYE, hYtr]
  simp only [hZtr]
  rw [lintegral_indicator_one hS, Measure.restrict_apply hS, Set.inter_comm]

/-- `tr ρ^{(M)}(X_M) = ∑_y tr ρ^{(M)}(k_M⁻¹(y)) + tr ρ^{(M)}(k_M⁻¹({o, q}))`. -/
private theorem front_tr_univ_split (hρ : A.IsHistory x ρ) (M : ℕ) :
    tr (ρ M Set.univ) = (∑ y : Fin N, tr (ρ M (A.kind M ⁻¹' {Kind.halt y}))) +
      tr (ρ M (A.kind M ⁻¹' {Kind.op, Kind.query})) := by
  obtain ⟨τ, hτ, -⟩ := front_core hρ M
  have hT : ∀ y : Fin N, MeasurableSet (A.kind M ⁻¹' {Kind.halt y}) := fun y =>
    front_meas_kind A M _
  have hS := front_meas_kind A M ({Kind.op, Kind.query} : Set (Kind N))
  have hTd : Pairwise (Function.onFun Disjoint fun y : Fin N => A.kind M ⁻¹' {Kind.halt y}) :=
    fun y y' hne => Disjoint.preimage _ (Set.disjoint_singleton.2 fun h => hne (Kind.halt.inj h))
  have hU : (⋃ y : Fin N, A.kind M ⁻¹' {Kind.halt y}) ∪
      A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N)) = Set.univ := by
    refine Set.eq_univ_of_forall fun h => ?_
    rcases front_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
    · exact Set.mem_union_right _ (by simp [hk])
    · exact Set.mem_union_right _ (by simp [hk])
    · exact Set.mem_union_left _ (Set.mem_iUnion.2 ⟨y, by simp [hk]⟩)
  have hD : Disjoint (⋃ y : Fin N, A.kind M ⁻¹' {Kind.halt y})
      (A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N))) := by
    rw [Set.disjoint_left]
    intro h h1 h2
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 h1
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff] at hy h2
    rw [hy] at h2
    rcases h2 with h2 | h2 <;> cases h2
  rw [← hτ _ MeasurableSet.univ, ← hτ _ hS, ← hU, measure_union hD hS, measure_iUnion hTd hT,
    tsum_fintype]
  congr 1
  exact Finset.sum_congr rfl fun y _ => hτ _ (hT y)

/-- Lemma lem:m-front(i), first claim: `p^{(M+1)}_x(X_{M+1}) = p^{(M)}_x(k_M⁻¹({o, q}))`. -/
theorem tr_succ_univ (hρ : A.IsHistory x ρ) (M : ℕ) :
    tr (ρ (M + 1) Set.univ) = tr (ρ M (A.kind M ⁻¹' {Kind.op, Kind.query})) := by
  obtain ⟨τ, hτ, hfront⟩ := front_core hρ M
  have h1 : ρ (M + 1) Set.univ = ρ (M + 1) (prodU (Set.univ : Set (Hist Ω M))) := by
    rw [front_prodU_univ]
  rw [h1, hfront _ MeasurableSet.univ, Set.univ_inter,
    hτ _ (front_meas_kind A M ({Kind.op, Kind.query} : Set (Kind N)))]

/-- Lemma lem:m-front(i), second claim:
`∑_{m<M} p^{(m)}_x(k_m⁻¹([N])) + p^{(M)}_x(X_M) = 1`, with `k_m⁻¹([N])` split over the outputs `y`. -/
theorem sum_halt_add_tr_univ (hρ : A.IsHistory x ρ) (M : ℕ) :
    (∑ m ∈ Finset.range M, ∑ y : Fin N, tr (ρ m (A.kind m ⁻¹' {Kind.halt y}))) +
      tr (ρ M Set.univ) = 1 := by
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    rw [hρ.init, A.rho0_tr]
  | succ M ih =>
    rw [Finset.sum_range_succ, tr_succ_univ hρ M, add_assoc, ← front_tr_univ_split hρ M]
    exact ih

/-- Lemma lem:m-front(ii): `ρ^{(M)}_x(A_M) = 0`. -/
theorem rho_haltedBefore (hρ : A.IsHistory x ρ) (M : ℕ) : ρ M (A.haltedBefore M) = 0 := by
  induction M with
  | zero =>
    have h0 : A.haltedBefore 0 = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun h hh => ?_
      obtain ⟨m, hm, _⟩ := hh
      exact Nat.not_lt_zero _ hm
    rw [h0]
    exact (hρ.pom 0).empty
  | succ M ih =>
    obtain ⟨τ, hτ, hfront⟩ := front_core hρ M
    have hT : ∀ y : Fin N, MeasurableSet (A.kind M ⁻¹' {Kind.halt y}) := fun y =>
      front_meas_kind A M _
    have hB0 := measurableSet_haltedBefore A M
    have hE : MeasurableSet (frontE A M) := hB0.union (MeasurableSet.iUnion hT)
    have hES : frontE A M ∩ A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N)) ⊆
        A.haltedBefore M := by
      rintro h ⟨hE1, hS1⟩
      rcases hE1 with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨y, hy⟩ := Set.mem_iUnion.1 h1
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff] at hy hS1
        rw [hy] at hS1
        rcases hS1 with h2 | h2 <;> cases h2
    have htr0 : tr (ρ (M + 1) (prodU (frontE A M))) = 0 := by
      rw [hfront _ hE]
      refine le_antisymm ?_ zero_le
      calc τ (frontE A M ∩ A.kind M ⁻¹' ({Kind.op, Kind.query} : Set (Kind N)))
          ≤ τ (A.haltedBefore M) := measure_mono hES
        _ = 0 := by rw [hτ _ hB0, ih, front_tr_zero]
    have hpom := hρ.pom (M + 1)
    have hB := measurableSet_haltedBefore A (M + 1)
    have hPE := front_measurableSet_prodU hE
    have h1 : trB (hbasis N K) (ρ (M + 1) (A.haltedBefore (M + 1))) ≤
        trB (hbasis N K) (ρ (M + 1) (prodU (frontE A M))) :=
      trB_mono (hpom.pos _ hB) (hpom.mono hB hPE (front_haltedBefore_succ_subset A M))
    rw [← tr_eq_trB (ρ (M + 1) (prodU (frontE A M))), htr0] at h1
    exact eq_zero_of_trB_eq_zero (hpom.pos _ hB) (le_antisymm h1 zero_le)

/-- Lemma lem:m-front(iii), first claim: `∑_M ∑_{y ∈ [N]} p^{(M)}_x(k_M⁻¹(y)) ≤ 1`. -/
theorem tsum_halt_le_one (hρ : A.IsHistory x ρ) :
    ∑' M : ℕ, ∑ y : Fin N, tr (ρ M (A.kind M ⁻¹' {Kind.halt y})) ≤ 1 :=
  ENNReal.tsum_le_of_sum_range_le fun n => le_self_add.trans_eq (sum_halt_add_tr_univ hρ n)

/-- Lemma lem:m-front(iii), second claim: if `s_x = 1` (zero error at `x`), then
`p^{(M)}_x(k_M⁻¹(y)) = 0` for all `M` and all `y ≠ x`. -/
theorem halt_ne_eq_zero (hρ : A.IsHistory x ρ) (hs : A.success ρ x = 1) (M : ℕ) (y : Fin N)
    (hy : y ≠ x) : tr (ρ M (A.kind M ⁻¹' {Kind.halt y})) = 0 := by
  have hle := tsum_halt_le_one hρ
  have hsplit : ∀ M : ℕ, ∑ y : Fin N, tr (ρ M (A.kind M ⁻¹' {Kind.halt y})) =
      tr (ρ M (A.kind M ⁻¹' {Kind.halt x})) +
        ∑ y ∈ Finset.univ.erase x, tr (ρ M (A.kind M ⁻¹' {Kind.halt y})) :=
    fun M => (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  simp only [hsplit] at hle
  rw [ENNReal.tsum_add] at hle
  have hsx : ∑' M : ℕ, tr (ρ M (A.kind M ⁻¹' {Kind.halt x})) = 1 := hs
  rw [hsx] at hle
  have hr : ∑' M : ℕ, ∑ y ∈ Finset.univ.erase x, tr (ρ M (A.kind M ⁻¹' {Kind.halt y})) = 0 := by
    have h2 : (1 : ℝ≥0∞) +
        ∑' M : ℕ, ∑ y ∈ Finset.univ.erase x, tr (ρ M (A.kind M ⁻¹' {Kind.halt y})) ≤ 1 + 0 := by
      rwa [add_zero]
    exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 h2)
  have hM := ENNReal.tsum_eq_zero.1 hr M
  exact Finset.sum_eq_zero_iff.1 hM y (Finset.mem_erase.2 ⟨hy, Finset.mem_univ y⟩)

end Alg

end

end TheoremS.Meas
