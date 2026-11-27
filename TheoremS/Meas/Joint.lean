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
The paragraph "The reference register" (with (M2)) and Lemma lem:m-joint (joint measures) of the paper's
section on measurable outcome spaces.

Representation: the register `R = ℂ^N` is put into the workspace, `K' = RK N K = PiLp 2 (fun _ : Fin N => K)`,
so `H' = R ⊗ H` is `H N (RK N K)` and every `H N K` result of `TheoremS/Meas/Trace.lean` to
`TheoremS/Meas/Hist.lean` applies to it with `K := RK N K`. A vector `ψ : H N (RK N K)` is `(i, r) ↦ ψ i r ∈ K`
(`i ∈ Idx N` the label of `ℂ^N ⊗ ℂ^2`, `r ∈ Fin N` the register label); `|r⟩ ⊗ φ` is `slot r φ`.
-/
import TheoremS.Meas.Hist

namespace TheoremS.Meas

set_option autoImplicit false

open scoped ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

/-- The workspace `K' = ℂ^N ⊗ K` of `H' = R ⊗ H` (paragraph "The reference register"), as the ℓ² sum of
`N` copies of `K`; `H' = H N (RK N K)`. -/
abbrev RK (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Fin N => K)

/-! ### Helpers: one-term Kraus families -/

section Single

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

/-- The Kraus family `(V, 0, 0, ...)`. -/
private def single1 (V : E →L[ℂ] E') : ℕ → E →L[ℂ] E' := fun k => if k = 0 then V else 0

private theorem krausMatG_single1 (V : E →L[ℂ] E') (Y : E →L[ℂ] E) (a c : E') :
    krausMatG (single1 V) Y a c =
      ⟪ContinuousLinearMap.adjoint V a, Y (ContinuousLinearMap.adjoint V c)⟫_ℂ := by
  unfold krausMatG
  rw [tsum_eq_single 0]
  · simp [single1]
  · intro k hk
    simp [single1, hk]

private theorem single1_bound (V : E →L[ℂ] E') (hV : ∀ ψ, ‖V ψ‖ ≤ ‖ψ‖) (ψ : E) :
    ∑' k, ENNReal.ofReal (‖single1 V k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [tsum_eq_single 0]
  · simp only [single1, eq_self_iff_true, if_true]
    exact ENNReal.ofReal_le_ofReal (by gcongr; exact hV ψ)
  · intro k hk
    simp [single1, hk]

private theorem single1_hN (V : E →L[ℂ] E') (hV : ∀ ψ, ContinuousLinearMap.adjoint V (V ψ) = ψ) (ψ : E) :
    HasSum (fun k => ContinuousLinearMap.adjoint (single1 V k) (single1 V k ψ)) ψ := by
  convert hasSum_single (f := fun k => ContinuousLinearMap.adjoint (single1 V k) (single1 V k ψ)) 0
    (fun k hk => by simp [single1, hk]) using 1
  simp [single1, hV]

end Single

section Register

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- `slot x : H → H'`, `φ ↦ |x⟩ ⊗ φ`: `(slot x φ) i` is the vector of `RK N K` with entry `φ i` at `x`
and `0` elsewhere (paragraph "The reference register"; `slot x† Y slot x'` is the block `Y_{xx'}`). -/
def slot (x : Fin N) : H N K →L[ℂ] H N (RK N K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Idx N => RK N K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : Idx N =>
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => K)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi (fun r : Fin N =>
          if r = x then
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Idx N => K) i ∘L
              (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Idx N => K)).toContinuousLinearMap
          else 0))

/-- The defining formula of `slot`: `(|x⟩ ⊗ φ) i r = [r = x] φ i`. -/
theorem slot_apply (x : Fin N) (φ : H N K) (i : Idx N) (r : Fin N) :
    slot x φ i r = if r = x then φ i else 0 := by
  by_cases h : r = x
  · subst h; simp [slot]
  · simp [slot, h]

/-- `|x⟩ ⊗ ·` is an isometry. -/
theorem slot_isometry (x : Fin N) (φ : H N K) : ‖slot x φ‖ = ‖φ‖ := by
  have h : ‖slot x φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 _ (slot x φ), PiLp.norm_sq_eq_of_L2 _ φ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.norm_sq_eq_of_L2 _ (slot x φ i)]
    simp only [slot_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro r _ hr; simp [hr]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

variable [CompleteSpace K]

/-! Helpers: register blocks. -/

private theorem adj_slot_eq (x : Fin N) (ψ : H N (RK N K)) :
    ContinuousLinearMap.adjoint (slot x) ψ = WithLp.toLp 2 (fun i => ψ i x) := by
  refine ext_inner_right ℂ fun φ => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, slot_apply, PiLp.toLp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single x]
  · simp
  · intro r _ hr; simp [hr]
  · intro hx; exact absurd (Finset.mem_univ x) hx

private theorem adj_slot_apply' (x : Fin N) (ψ : H N (RK N K)) (i : Idx N) :
    ContinuousLinearMap.adjoint (slot x) ψ i = ψ i x := by
  rw [adj_slot_eq, PiLp.toLp_apply]

private theorem adj_slot_slot_apply (x x' : Fin N) (φ : H N K) :
    ContinuousLinearMap.adjoint (slot x) (slot x' φ) = if x = x' then φ else 0 := by
  ext i
  rw [adj_slot_apply', slot_apply]
  by_cases h : x = x'
  · subst h; simp
  · simp [h]

private theorem eq_of_adj_slot {ψ ψ' : H N (RK N K)}
    (h : ∀ x, ContinuousLinearMap.adjoint (slot x) ψ = ContinuousLinearMap.adjoint (slot x) ψ') :
    ψ = ψ' := by
  ext i r
  rw [← adj_slot_apply' r ψ i, ← adj_slot_apply' r ψ' i, h r]

/-- Block-diagonal operators `∑_r |r⟩⟨r| ⊗ T_r`. -/
private def opSum (T : Fin N → Op N K) : Op N (RK N K) :=
  ∑ r : Fin N, slot r ∘L T r ∘L ContinuousLinearMap.adjoint (slot r)

private theorem adj_slot_opSum (T : Fin N → Op N K) (x : Fin N) (ψ : H N (RK N K)) :
    ContinuousLinearMap.adjoint (slot x) (opSum T ψ) = T x (ContinuousLinearMap.adjoint (slot x) ψ) := by
  rw [opSum, sum_apply, map_sum]
  simp only [ContinuousLinearMap.comp_apply, adj_slot_slot_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro r _ hr; simp [Ne.symm hr]
  · intro hx; exact absurd (Finset.mem_univ x) hx

private theorem opSum_slot (T : Fin N → Op N K) (x : Fin N) (φ : H N K) :
    opSum T (slot x φ) = slot x (T x φ) := by
  refine eq_of_adj_slot fun y => ?_
  rw [adj_slot_opSum, adj_slot_slot_apply, adj_slot_slot_apply]
  split_ifs with h
  · subst h; rfl
  · simp

private theorem opSum_comp (S T : Fin N → Op N K) :
    opSum S ∘L opSum T = opSum (fun r => S r ∘L T r) := by
  ext1 ψ
  refine eq_of_adj_slot fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, adj_slot_opSum]

private theorem opSum_id :
    opSum (fun _ : Fin N => ContinuousLinearMap.id ℂ (H N K)) = ContinuousLinearMap.id ℂ (H N (RK N K)) := by
  ext1 ψ
  refine eq_of_adj_slot fun x => ?_
  rw [adj_slot_opSum]
  rfl

private theorem adjoint_opSum (T : Fin N → Op N K) :
    ContinuousLinearMap.adjoint (opSum T) = opSum (fun r => ContinuousLinearMap.adjoint (T r)) := by
  simp only [opSum, map_sum, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

private theorem oracleL_adjoint' (x : Fin N) :
    ContinuousLinearMap.adjoint (oracleL (K := K) x) =
      (oracle x).symm.toLinearIsometry.toContinuousLinearMap := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  show ⟪(oracle x).symm u, v⟫_ℂ = ⟪u, (oracle x) v⟫_ℂ
  rw [← (oracle x).inner_map_map ((oracle x).symm u) v, LinearIsometryEquiv.apply_symm_apply]

private theorem oracle_apply' (x : Fin N) (v : H N K) (i : Idx N) : oracleL x v i = v (flip x i) := by
  rfl

/-- `slot x† = ⟨x| ⊗ I`: `(slot x† ψ) i = ψ i x`. -/
theorem adjoint_slot_apply (x : Fin N) (ψ : H N (RK N K)) (i : Idx N) :
    ContinuousLinearMap.adjoint (slot x) ψ i = ψ i x := by
  exact adj_slot_apply' x ψ i

/-- `(⟨x| ⊗ I)(|x'⟩ ⊗ I) = [x = x'] I`. -/
theorem adjoint_slot_comp_slot (x x' : Fin N) :
    ContinuousLinearMap.adjoint (slot (K := K) x) ∘L slot x' =
      if x = x' then ContinuousLinearMap.id ℂ (H N K) else 0 := by
  ext1 φ
  rw [ContinuousLinearMap.comp_apply, adj_slot_slot_apply]
  split_ifs <;> simp

/-- `∑_x |x⟩⟨x| ⊗ I = I` on `H'`. -/
theorem sum_slot_comp_adjoint :
    ∑ x : Fin N, slot (K := K) x ∘L ContinuousLinearMap.adjoint (slot x) =
      ContinuousLinearMap.id ℂ (H N (RK N K)) := by
  ext1 ψ
  refine eq_of_adj_slot fun x => ?_
  rw [sum_apply, map_sum]
  simp only [ContinuousLinearMap.comp_apply, adj_slot_slot_apply, ContinuousLinearMap.id_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro r _ hr; simp [Ne.symm hr]
  · intro hx; exact absurd (Finset.mem_univ x) hx

/-- `β_x(Y) = N Y_{xx}`, `Y_{xx} = (⟨x| ⊗ I) Y (|x⟩ ⊗ I)` (paragraph "The reference register"). -/
def beta (x : Fin N) (Y : Op N (RK N K)) : Op N K :=
  (N : ℂ) • (ContinuousLinearMap.adjoint (slot x) ∘L Y ∘L slot x)

/-- `id_R ⊗ B = ∑_r |r⟩⟨r| ⊗ B`: applies `B` to the column `(i ↦ ψ i r)` for each register label `r`. -/
def liftOp (B : Op N K) : Op N (RK N K) :=
  ∑ r : Fin N, slot r ∘L B ∘L ContinuousLinearMap.adjoint (slot r)

private theorem liftOp_eq (B : Op N K) : liftOp B = opSum (fun _ => B) := rfl

private theorem liftOp_slot' (B : Op N K) (x : Fin N) (φ : H N K) :
    liftOp B (slot x φ) = slot x (B φ) := by
  rw [liftOp_eq, opSum_slot]

private theorem adj_slot_liftOp (B : Op N K) (x : Fin N) (ψ : H N (RK N K)) :
    ContinuousLinearMap.adjoint (slot x) (liftOp B ψ) = B (ContinuousLinearMap.adjoint (slot x) ψ) := by
  rw [liftOp_eq, adj_slot_opSum]

private theorem adjoint_liftOp' (B : Op N K) :
    ContinuousLinearMap.adjoint (liftOp B) = liftOp (ContinuousLinearMap.adjoint B) := by
  rw [liftOp_eq, liftOp_eq, adjoint_opSum]

/-- The defining formula of `liftOp`: `((id_R ⊗ B) ψ) i r = B (slot r† ψ) i`, `slot r† ψ = (i ↦ ψ i r)`. -/
theorem liftOp_apply (B : Op N K) (ψ : H N (RK N K)) (i : Idx N) (r : Fin N) :
    liftOp B ψ i r = B (ContinuousLinearMap.adjoint (slot r) ψ) i := by
  rw [← adj_slot_apply' r (liftOp B ψ) i, adj_slot_liftOp]

/-- `(id_R ⊗ B)(|x⟩ ⊗ I) = (|x⟩ ⊗ I) B`. -/
theorem liftOp_comp_slot (B : Op N K) (x : Fin N) : liftOp B ∘L slot x = slot x ∘L B := by
  ext1 φ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, liftOp_slot']

/-- The controlled oracle `U = ∑_x |x⟩⟨x| ⊗ O_x` on `H'` (paragraph "The reference register"); it does
not depend on the marked item. -/
def ctrlU : Op N (RK N K) :=
  ∑ r : Fin N, slot (K := K) r ∘L oracleL r ∘L ContinuousLinearMap.adjoint (slot r)

private theorem ctrlU_eq : ctrlU (N := N) (K := K) = opSum (oracleL (K := K)) := rfl

private theorem adj_slot_ctrlU (x : Fin N) (ψ : H N (RK N K)) :
    ContinuousLinearMap.adjoint (slot x) (ctrlU ψ) = oracleL x (ContinuousLinearMap.adjoint (slot x) ψ) := by
  rw [ctrlU_eq, adj_slot_opSum]

private theorem adjoint_ctrlU_slot (x : Fin N) (φ : H N K) :
    ContinuousLinearMap.adjoint (ctrlU (N := N) (K := K)) (slot x φ) =
      slot x (ContinuousLinearMap.adjoint (oracleL x) φ) := by
  rw [ctrlU_eq, adjoint_opSum, opSum_slot]

/-- The defining formula of `ctrlU`: `(U ψ) i r = ψ (flip r i) r`. -/
theorem ctrlU_apply (ψ : H N (RK N K)) (i : Idx N) (r : Fin N) :
    ctrlU ψ i r = ψ (flip r i) r := by
  rw [← adj_slot_apply' r (ctrlU ψ) i, adj_slot_ctrlU, oracle_apply', adj_slot_apply']

/-- `U (|x⟩ ⊗ I) = (|x⟩ ⊗ I) O_x`. -/
theorem ctrlU_comp_slot (x : Fin N) :
    ctrlU (N := N) (K := K) ∘L slot x = slot (K := K) x ∘L oracleL x := by
  ext1 φ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ctrlU_eq, opSum_slot]

/-- `U` is unitary. -/
theorem ctrlU_unitary :
    ContinuousLinearMap.adjoint (ctrlU (N := N) (K := K)) ∘L ctrlU (N := N) (K := K) =
        ContinuousLinearMap.id ℂ (H N (RK N K)) ∧
      ctrlU (N := N) (K := K) ∘L ContinuousLinearMap.adjoint (ctrlU (N := N) (K := K)) =
        ContinuousLinearMap.id ℂ (H N (RK N K)) := by
  have h1 : ∀ r : Fin N, ContinuousLinearMap.adjoint (oracleL (K := K) r) ∘L oracleL r =
      ContinuousLinearMap.id ℂ (H N K) := fun r => by
    rw [oracleL_adjoint']
    ext1 v
    show (oracle r).symm (oracle r v) = v
    exact (oracle r).symm_apply_apply v
  have h2 : ∀ r : Fin N, oracleL (K := K) r ∘L ContinuousLinearMap.adjoint (oracleL r) =
      ContinuousLinearMap.id ℂ (H N K) := fun r => by
    rw [oracleL_adjoint']
    ext1 v
    show (oracle r) ((oracle r).symm v) = v
    exact (oracle r).apply_symm_apply v
  rw [ctrlU_eq, adjoint_opSum, opSum_comp, opSum_comp]
  simp only [h1, h2]
  exact ⟨opSum_id, opSum_id⟩

/-- `|u⟩ ⊗ · : H → H'`, `u = N^{-1/2} ∑_x |x⟩`. -/
def uEmb : H N K →L[ℂ] H N (RK N K) :=
  ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x : Fin N, slot x

/-- `C(Y) = tr((|u⟩⟨u| ⊗ I) Y) = tr((⟨u| ⊗ I) Y (|u⟩ ⊗ I))` (paragraph "The reference register"). -/
def Cf (Y : Op N (RK N K)) : ℝ≥0∞ :=
  tr (ContinuousLinearMap.adjoint uEmb ∘L Y ∘L uEmb)

/-- (M2), first identity, in matrix elements: `β_x ∘ (id_R ⊗ Γ) = Γ ∘ β_x` for `Γ(Y) = ∑_k B_k Y B_k†`,
`⟪a, Γ(β_x Y) b⟫ = N ⟪|x⟩ ⊗ a, (id_R ⊗ Γ)(Y) (|x⟩ ⊗ b)⟫`, where `id_R ⊗ Γ` has the Kraus operators
`id_R ⊗ B_k`. The identity holds term by term in `k`, so no hypothesis on `B` or `Y` is needed. -/
theorem beta_liftKraus (B : ℕ → Op N K) (x : Fin N) (Y : Op N (RK N K)) (a b : H N K) :
    krausMat B (beta x Y) a b = (N : ℂ) * krausMat (fun k => liftOp (B k)) Y (slot x a) (slot x b) := by
  unfold krausMat
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [adjoint_liftOp', liftOp_slot', liftOp_slot']
  simp only [beta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]

/-- (M2), second identity: `β_x(U Y U*) = O_x β_x(Y) O_x*`. -/
theorem beta_ctrlU (x : Fin N) (Y : Op N (RK N K)) :
    beta x (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU) =
      oracleL x ∘L beta x Y ∘L ContinuousLinearMap.adjoint (oracleL x) := by
  ext1 v
  simp only [beta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, adj_slot_ctrlU,
    adjoint_ctrlU_slot, map_smul]

/-! Helpers: the embedding `|u⟩ ⊗ ·` and the block trace. -/

private theorem uEmb_adjoint :
    ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) =
      ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • ∑ x : Fin N, ContinuousLinearMap.adjoint (slot (K := K) x) := by
  rw [uEmb, map_smulₛₗ, map_sum]
  congr 1
  simp [Complex.conj_ofReal]

private theorem adj_slot_uEmb (x : Fin N) (φ : H N K) :
    ContinuousLinearMap.adjoint (slot x) (uEmb φ) = ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • φ := by
  rw [uEmb, ContinuousLinearMap.smul_apply, sum_apply, map_smul, map_sum]
  simp only [adj_slot_slot_apply]
  simp

private theorem adj_uEmb_slot (x : Fin N) (φ : H N K) :
    ContinuousLinearMap.adjoint uEmb (slot x φ) = ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • φ := by
  rw [uEmb_adjoint, ContinuousLinearMap.smul_apply, sum_apply]
  simp only [adj_slot_slot_apply]
  simp

private theorem c_mul_c {N : ℕ} (hN : N ≠ 0) :
    (N : ℂ) * (((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) * ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ))) = 1 := by
  have hs : (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    simp
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [div_mul_div_comm, one_mul, hs, mul_one_div_cancel hN']

private theorem uEmb_isom :
    ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) ∘L uEmb = ContinuousLinearMap.id ℂ (H N K) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    ext1 φ
    ext i
    exact i.1.elim0
  · ext1 φ
    have h1 : ∀ x : Fin N, ContinuousLinearMap.adjoint (slot x) (uEmb φ) =
        ((1 : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) • φ := fun x => adj_slot_uEmb x φ
    rw [ContinuousLinearMap.comp_apply, uEmb_adjoint, ContinuousLinearMap.smul_apply, sum_apply]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ContinuousLinearMap.id_apply]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    simp only [smul_smul]
    rw [mul_left_comm, c_mul_c hN.ne', one_smul]

private theorem norm_uEmb_apply (φ : H N K) : ‖uEmb φ‖ = ‖φ‖ := by
  have h : ⟪uEmb φ, uEmb φ⟫_ℂ = ⟪φ, φ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, uEmb_isom,
      ContinuousLinearMap.id_apply]
  have h2 : ‖uEmb φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

private theorem norm_adj_uEmb_le (ψ : H N (RK N K)) :
    ‖ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) ψ‖ ≤ ‖ψ‖ := by
  have h1 : ‖(uEmb (N := N) (K := K))‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => by rw [norm_uEmb_apply, one_mul]
  have h2 : ‖ContinuousLinearMap.adjoint (uEmb (N := N) (K := K))‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact h1
  calc ‖ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) ψ‖
      ≤ ‖ContinuousLinearMap.adjoint (uEmb (N := N) (K := K))‖ * ‖ψ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ‖ := by gcongr
    _ = ‖ψ‖ := one_mul _

/-- The product basis `|x⟩ ⊗ e` of `H'`. -/
private def slotFam (p : Fin N × basisSet N K) : H N (RK N K) := slot p.1 (p.2 : H N K)

private theorem slotFam_orth : Orthonormal ℂ (slotFam (N := N) (K := K)) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨x, e⟩ ⟨x', e'⟩
  have he := orthonormal_iff_ite.mp (bd_orth (N := N) (K := K)) e e'
  simp only [slotFam]
  rw [← ContinuousLinearMap.adjoint_inner_right, adj_slot_slot_apply]
  by_cases hx : x = x'
  · subst hx
    rw [if_pos rfl, he]
    simp
  · simp [hx]

private theorem slotFam_complete :
    (Submodule.span ℂ (Set.range (slotFam (N := N) (K := K))))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro ψ hψ
  rw [Submodule.mem_orthogonal] at hψ
  refine eq_of_adj_slot fun x => ?_
  rw [map_zero]
  refine bd_vec_ext (hbasis N K) fun e => ?_
  rw [hb_coe, inner_zero_right, ContinuousLinearMap.adjoint_inner_right]
  exact hψ _ (Submodule.subset_span ⟨(x, e), rfl⟩)

private def slotBasis : HilbertBasis (Fin N × basisSet N K) ℂ (H N (RK N K)) :=
  HilbertBasis.mkOfOrthogonalEqBot slotFam_orth slotFam_complete

private theorem slotBasis_apply (x : Fin N) (e : basisSet N K) :
    slotBasis (N := N) (K := K) (x, e) = slot x (e : H N K) := by
  rw [slotBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

private theorem tr_eq_sum_blocks {Y : Op N (RK N K)} (hY : Y.IsPositive) :
    tr Y = ∑ x : Fin N, tr (ContinuousLinearMap.adjoint (slot x) ∘L Y ∘L slot x) := by
  rw [tr_eq_trB, trB_indep (hbasis N (RK N K)) slotBasis hY]
  unfold trB
  rw [ENNReal.tsum_prod', tsum_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tr_eq_trB]
  unfold trB
  refine tsum_congr fun e => ?_
  simp only [slotBasis_apply]
  rw [hb_coe]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

private theorem tr_nat_smul (n : ℕ) (Z : Op N K) : tr ((n : ℂ) • Z) = n * tr Z := by
  rw [tr_eq_trB, tr_eq_trB]
  have h := trB_smul (b := hbasis N K) (Y := Z) (n : NNReal)
  simpa using h

private theorem tr_zero_N {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    (Z : Op 0 K') : tr Z = 0 := by
  have hs : ∀ v : H 0 K', v = 0 := fun v => by ext i; exact i.1.elim0
  unfold tr
  refine ENNReal.tsum_eq_zero.mpr fun e => ?_
  rw [hs (e : H 0 K')]
  simp

/-- `W(Y) = tr Y = ∑_x tr Y_{xx} = (1/N) ∑_x tr β_x(Y)` for positive `Y` (proof of lem:m-joint(i)). -/
theorem tr_eq_sum_beta {Y : Op N (RK N K)} (hY : Y.IsPositive) :
    (N : ℝ≥0∞) * tr Y = ∑ x : Fin N, tr (beta x Y) := by
  rw [tr_eq_sum_blocks hY, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [beta, tr_nat_smul]

/-- `C(Y) ≤ W(Y)` for `Y ∈ 𝒯(H')₊`. -/
theorem Cf_le_tr {Y : Op N (RK N K)} (hY : PosTC Y) : Cf Y ≤ tr Y := by
  unfold Cf
  rw [tr_eq_trB, tr_eq_trB]
  refine trB_le_of_krausMatG (A := single1 (ContinuousLinearMap.adjoint (uEmb (N := N) (K := K))))
    (single1_bound _ norm_adj_uEmb_le) hY.1 (by rw [← tr_eq_trB]; exact hY.2) fun a c => ?_
  rw [krausMatG_single1, ContinuousLinearMap.adjoint_adjoint]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- `W(U Y U*) = W(Y)`. -/
theorem tr_ctrlU {Y : Op N (RK N K)} (hY : PosTC Y) :
    tr (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU) = tr Y := by
  rw [tr_eq_trB, tr_eq_trB]
  refine trB_eq_of_krausMatG (A := single1 (ctrlU (N := N) (K := K))) (single1_hN _ fun ψ => ?_) hY.1
    (by rw [← tr_eq_trB]; exact hY.2) fun a c => ?_
  · rw [← ContinuousLinearMap.comp_apply, ctrlU_unitary.1, ContinuousLinearMap.id_apply]
  · rw [krausMatG_single1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]

/-- `C(Y + Z) = C(Y) + C(Z)` for positive `Y`, `Z` (the sums of (M3)). -/
theorem Cf_add {Y Z : Op N (RK N K)} (hY : Y.IsPositive) (hZ : Z.IsPositive) : Cf (Y + Z) = Cf Y + Cf Z := by
  unfold Cf
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, tr_eq_trB, tr_eq_trB, tr_eq_trB]
  exact trB_add (hY.adjoint_conj _) (hZ.adjoint_conj _)

/-- `(⟨x| ⊗ I) U = O_x (⟨x| ⊗ I)`. -/
theorem adjoint_slot_comp_ctrlU (x : Fin N) :
    ContinuousLinearMap.adjoint (slot (K := K) x) ∘L ctrlU = oracleL x ∘L ContinuousLinearMap.adjoint (slot x) := by
  ext1 ψ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, adj_slot_ctrlU]

/-- `(id_R ⊗ B)† = id_R ⊗ B†`. -/
theorem adjoint_liftOp (B : Op N K) :
    ContinuousLinearMap.adjoint (liftOp B) = liftOp (ContinuousLinearMap.adjoint B) := by
  exact adjoint_liftOp' B

/-- `(id_R ⊗ B)(|u⟩ ⊗ ·) = (|u⟩ ⊗ ·) B`. -/
theorem liftOp_comp_uEmb (B : Op N K) : liftOp B ∘L uEmb = uEmb ∘L B := by
  ext1 φ
  simp only [uEmb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, sum_apply, map_smul,
    map_sum, liftOp_slot']

/-- `|u⟩ ⊗ ·` is an isometry: `(⟨u| ⊗ I)(|u⟩ ⊗ I) = I` (also for `N = 0`, where `H` is the zero space). -/
theorem adjoint_uEmb_comp_uEmb :
    ContinuousLinearMap.adjoint (uEmb (N := N) (K := K)) ∘L uEmb = ContinuousLinearMap.id ℂ (H N K) := by
  exact uEmb_isom

/-- `tr(|u⟩⟨u| ⊗ ρ) = tr ρ` for positive `ρ` (`W(Λ_0) = 1`). -/
theorem tr_uEmb_conj {ρ : Op N K} (hρ : ρ.IsPositive) :
    tr (uEmb ∘L ρ ∘L ContinuousLinearMap.adjoint uEmb) = tr ρ := by
  have hpos := hρ.conj_adjoint (uEmb (N := N) (K := K))
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [tr_zero_N, tr_zero_N]
  · have hbeta : ∀ x : Fin N, beta x (uEmb ∘L ρ ∘L ContinuousLinearMap.adjoint uEmb) = ρ := fun x => by
      ext1 v
      simp only [beta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, adj_uEmb_slot,
        adj_slot_uEmb, map_smul, smul_smul]
      rw [c_mul_c hN.ne', one_smul]
    have hmain := tr_eq_sum_beta hpos
    simp only [hbeta, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hmain
    exact (ENNReal.mul_right_inj (Nat.cast_ne_zero.mpr hN.ne') (ENNReal.natCast_ne_top N)).mp hmain

/-! Helpers: polarisation of the register blocks, lifted Kraus families, `β_x`. -/

/-- `(|r⟩ + s |r'⟩) / 2 ⊗ ·`. -/
private def pw (r r' : Fin N) (s : ℂ) : H N K →L[ℂ] H N (RK N K) :=
  (1 / 2 : ℂ) • (slot r + s • slot r')

/-- The compression `pw† Y pw`. -/
private def pz (r r' : Fin N) (s : ℂ) (Y : Op N (RK N K)) : Op N K :=
  ContinuousLinearMap.adjoint (pw r r' s) ∘L Y ∘L pw r r' s

/-- The polarisation combination over `s ∈ {1, -1, i, -i}`. -/
private def pc (f : ℂ → ℂ) : ℂ :=
  f 1 - f (-1) - Complex.I * f Complex.I + Complex.I * f (-Complex.I)

private theorem norm_slot_le (r : Fin N) : ‖slot (K := K) r‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => by rw [slot_isometry, one_mul]

private theorem norm_pw_le (r r' : Fin N) {s : ℂ} (hs : ‖s‖ = 1) : ‖pw (K := K) r r' s‖ ≤ 1 := by
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
  have e : pw (K := K) r r' s φ = (1 / 2 : ℂ) • (slot r φ + s • slot r' φ) := by
    simp only [pw, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  rw [e, norm_smul, one_mul]
  calc ‖(1 / 2 : ℂ)‖ * ‖slot r φ + s • slot r' φ‖
      ≤ ‖(1 / 2 : ℂ)‖ * (‖slot r φ‖ + ‖s • slot r' φ‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖φ‖ := by rw [norm_smul, hs, one_mul, slot_isometry, slot_isometry, h2]; ring

private theorem norm_adj_pw_le (r r' : Fin N) {s : ℂ} (hs : ‖s‖ = 1) (ψ : H N (RK N K)) :
    ‖ContinuousLinearMap.adjoint (pw (K := K) r r' s) ψ‖ ≤ ‖ψ‖ := by
  have h2 : ‖ContinuousLinearMap.adjoint (pw (K := K) r r' s)‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact norm_pw_le r r' hs
  calc ‖ContinuousLinearMap.adjoint (pw (K := K) r r' s) ψ‖
      ≤ ‖ContinuousLinearMap.adjoint (pw (K := K) r r' s)‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖ψ‖ := one_mul _

private theorem posTC_pz (r r' : Fin N) {s : ℂ} (hs : ‖s‖ = 1) {Y : Op N (RK N K)} (hY : PosTC Y) :
    PosTC (pz r r' s Y) := by
  refine ⟨hY.1.adjoint_conj (pw r r' s), lt_of_le_of_lt ?_ hY.2⟩
  rw [tr_eq_trB, tr_eq_trB]
  refine trB_le_of_krausMatG (A := single1 (ContinuousLinearMap.adjoint (pw (K := K) r r' s)))
    (single1_bound _ (norm_adj_pw_le r r' hs)) hY.1 (by rw [← tr_eq_trB]; exact hY.2) fun a c => ?_
  rw [krausMatG_single1, ContinuousLinearMap.adjoint_adjoint]
  simp only [pz, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

private theorem polar_slot (Y : Op N (RK N K)) (r r' : Fin N) (u v : H N K) :
    ⟪slot r u, Y (slot r' v)⟫_ℂ = pc (fun s => ⟪u, pz r r' s Y v⟫_ℂ) := by
  simp only [pc, pz, pw, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, map_add, map_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I, map_neg, map_one, map_div₀,
    map_ofNat, map_inv₀]
  linear_combination (1 / 2 : ℂ) * (⟪slot r u, Y (slot r' v)⟫_ℂ - ⟪slot r' u, Y (slot r v)⟫_ℂ) *
    Complex.I_sq

private theorem unit_norms :
    ‖(1 : ℂ)‖ = 1 ∧ ‖(-1 : ℂ)‖ = 1 ∧ ‖Complex.I‖ = 1 ∧ ‖-Complex.I‖ = 1 :=
  ⟨norm_one, by rw [norm_neg, norm_one], Complex.norm_I, by rw [norm_neg, Complex.norm_I]⟩

private theorem hasSum_pc {f : ℂ → ℕ → ℂ} {g : ℂ → ℂ} (h : ∀ s : ℂ, ‖s‖ = 1 → HasSum (f s) (g s)) :
    HasSum (fun k => pc (fun s => f s k)) (pc g) := by
  unfold pc
  exact (((h 1 unit_norms.1).sub (h (-1) unit_norms.2.1)).sub
    ((h _ unit_norms.2.2.1).mul_left Complex.I)).add ((h _ unit_norms.2.2.2).mul_left Complex.I)

private theorem measurable_pc {β : Type*} [MeasurableSpace β] {f : ℂ → β → ℂ}
    (h : ∀ s : ℂ, ‖s‖ = 1 → Measurable (f s)) : Measurable (fun t => pc (fun s => f s t)) := by
  unfold pc
  exact (((h 1 unit_norms.1).sub (h (-1) unit_norms.2.1)).sub
    ((h _ unit_norms.2.2.1).const_mul Complex.I)).add ((h _ unit_norms.2.2.2).const_mul Complex.I)

private theorem liftOp_adj_apply (B : Op N K) (a : H N (RK N K)) :
    ContinuousLinearMap.adjoint (liftOp B) a =
      ∑ r : Fin N, slot r (ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint (slot r) a)) := by
  rw [adjoint_liftOp']
  simp only [liftOp, sum_apply, ContinuousLinearMap.comp_apply]

private theorem liftOp_term (B : Op N K) (Y : Op N (RK N K)) (a b : H N (RK N K)) :
    ⟪ContinuousLinearMap.adjoint (liftOp B) a, Y (ContinuousLinearMap.adjoint (liftOp B) b)⟫_ℂ =
      ∑ r : Fin N, ∑ r' : Fin N, pc (fun s =>
        ⟪ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint (slot r) a),
          pz r r' s Y (ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint (slot r') b))⟫_ℂ) := by
  rw [liftOp_adj_apply, liftOp_adj_apply, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  exact polar_slot Y r r' _ _

/-- The off-diagonal blocks of `id_R ⊗ Γ` by polarisation: only `PosTC` arguments of `Γ` occur. -/
private theorem krausMat_liftOp {T : ℕ → Op N K}
    (hT : ∀ ψ : H N K, ∑' k, ENNReal.ofReal (‖T k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    {Y : Op N (RK N K)} (hY : PosTC Y) (a b : H N (RK N K)) :
    krausMat (fun k => liftOp (T k)) Y a b = ∑ r : Fin N, ∑ r' : Fin N,
      pc (fun s => krausMat T (pz r r' s Y) (ContinuousLinearMap.adjoint (slot r) a)
        (ContinuousLinearMap.adjoint (slot r') b)) := by
  have hs : ∀ r r' : Fin N, ∀ s : ℂ, ‖s‖ = 1 → HasSum
      (fun k => ⟪ContinuousLinearMap.adjoint (T k) (ContinuousLinearMap.adjoint (slot r) a),
        pz r r' s Y (ContinuousLinearMap.adjoint (T k) (ContinuousLinearMap.adjoint (slot r') b))⟫_ℂ)
      (krausMat T (pz r r' s Y) (ContinuousLinearMap.adjoint (slot r) a)
        (ContinuousLinearMap.adjoint (slot r') b)) := by
    intro r r' s hs
    rw [krausMat_eq_krausMatG]
    exact krausMatG_hasSum (b := hbasis N K) hT (posTC_pz r r' hs hY).1
      (by rw [← tr_eq_trB]; exact (posTC_pz r r' hs hY).2) _ _
  have hsum := hasSum_sum fun r (_ : r ∈ Finset.univ) =>
    hasSum_sum fun r' (_ : r' ∈ Finset.univ) => hasSum_pc (hs r r')
  exact (tsum_congr fun k => liftOp_term (T k) Y a b).trans hsum.tsum_eq

private theorem norm_sq_blocks (ψ : H N (RK N K)) :
    ‖ψ‖ ^ 2 = ∑ r : Fin N, ‖ContinuousLinearMap.adjoint (slot r) ψ‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 _ ψ]
  simp only [adj_slot_eq, PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply]
  exact Finset.sum_comm

private theorem liftOp_bound {T : ℕ → Op N K}
    (hT : ∀ ψ : H N K, ∑' k, ENNReal.ofReal (‖T k ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2))
    (ψ : H N (RK N K)) :
    ∑' k, ENNReal.ofReal (‖liftOp (T k) ψ‖ ^ 2) ≤ ENNReal.ofReal (‖ψ‖ ^ 2) := by
  have e : ∀ φ : H N (RK N K), ENNReal.ofReal (‖φ‖ ^ 2) =
      ∑ r : Fin N, ENNReal.ofReal (‖ContinuousLinearMap.adjoint (slot r) φ‖ ^ 2) := fun φ => by
    rw [norm_sq_blocks, ENNReal.ofReal_sum_of_nonneg fun r _ => sq_nonneg _]
  calc ∑' k, ENNReal.ofReal (‖liftOp (T k) ψ‖ ^ 2)
      = ∑' k, ∑ r : Fin N, ENNReal.ofReal (‖T k (ContinuousLinearMap.adjoint (slot r) ψ)‖ ^ 2) :=
        tsum_congr fun k => by rw [e]; simp only [adj_slot_liftOp]
    _ = ∑ r : Fin N, ∑' k, ENNReal.ofReal (‖T k (ContinuousLinearMap.adjoint (slot r) ψ)‖ ^ 2) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ r : Fin N, ENNReal.ofReal (‖ContinuousLinearMap.adjoint (slot r) ψ‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hT _
    _ = ENNReal.ofReal (‖ψ‖ ^ 2) := (e ψ).symm

private theorem opSum_apply' (T : Fin N → Op N K) (ψ : H N (RK N K)) :
    opSum T ψ = ∑ r : Fin N, slot r (T r (ContinuousLinearMap.adjoint (slot r) ψ)) := by
  simp only [opSum, sum_apply, ContinuousLinearMap.comp_apply]

private theorem liftOp_hN {B : ℕ → Op N K}
    (hB : ∀ ψ, HasSum (fun k => ContinuousLinearMap.adjoint (B k) (B k ψ)) ψ) (ψ : H N (RK N K)) :
    HasSum (fun k => ContinuousLinearMap.adjoint (liftOp (B k)) (liftOp (B k) ψ)) ψ := by
  have e : ∀ k, ContinuousLinearMap.adjoint (liftOp (B k)) (liftOp (B k) ψ) =
      ∑ r : Fin N, slot r (ContinuousLinearMap.adjoint (B k) (B k (ContinuousLinearMap.adjoint (slot r) ψ))) := by
    intro k
    rw [adjoint_liftOp', liftOp_eq (ContinuousLinearMap.adjoint (B k)), opSum_apply']
    simp only [adj_slot_liftOp]
  have hψ : ψ = ∑ r : Fin N, slot r (ContinuousLinearMap.adjoint (slot r) ψ) := by
    have h := congrArg (fun T => T ψ) (opSum_id (N := N) (K := K))
    simp only [opSum_apply', ContinuousLinearMap.id_apply] at h
    exact h.symm
  have hs : HasSum (fun k => ∑ r : Fin N, slot (K := K) r
      (ContinuousLinearMap.adjoint (B k) (B k (ContinuousLinearMap.adjoint (slot (K := K) r) ψ))))
      (∑ r : Fin N, slot (K := K) r (ContinuousLinearMap.adjoint (slot (K := K) r) ψ)) :=
    hasSum_sum fun r _ => (slot (K := K) r).hasSum (hB (ContinuousLinearMap.adjoint (slot (K := K) r) ψ))
  convert hs using 1
  exact funext e

private theorem lift_uEmb_apply (B : Op N K) (φ : H N K) : liftOp B (uEmb φ) = uEmb (B φ) := by
  rw [← ContinuousLinearMap.comp_apply (liftOp B) uEmb, liftOp_comp_uEmb, ContinuousLinearMap.comp_apply]

/-- A lifted normalised Kraus family preserves `W` and `C`. -/
private theorem lift_kraus_eq {B : ℕ → Op N K}
    (hB : ∀ ψ, HasSum (fun k => ContinuousLinearMap.adjoint (B k) (B k ψ)) ψ)
    {Y Z : Op N (RK N K)} (hY : PosTC Y)
    (hZ : ∀ a c, ⟪a, Z c⟫_ℂ = krausMatG (fun k => liftOp (B k)) Y a c) :
    tr Z = tr Y ∧ Cf Z = Cf Y := by
  have hYf : trB (hbasis N (RK N K)) Y < ∞ := by rw [← tr_eq_trB]; exact hY.2
  refine ⟨?_, ?_⟩
  · rw [tr_eq_trB, tr_eq_trB]
    exact trB_eq_of_krausMatG (liftOp_hN hB) hY.1 hYf hZ
  · have hC : Cf Y < ∞ := (Cf_le_tr hY).trans_lt hY.2
    unfold Cf at hC ⊢
    rw [tr_eq_trB, tr_eq_trB]
    refine trB_eq_of_krausMatG hB (hY.1.adjoint_conj uEmb) (by rw [← tr_eq_trB]; exact hC)
      fun a c => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [hZ]
    unfold krausMatG
    refine tsum_congr fun k => ?_
    simp only [adjoint_liftOp', lift_uEmb_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]

private theorem norm_ctrlU_apply (ψ : H N (RK N K)) : ‖ctrlU (N := N) (K := K) ψ‖ = ‖ψ‖ := by
  have h : ⟪ctrlU ψ, ctrlU ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, ctrlU_unitary.1,
      ContinuousLinearMap.id_apply]
  have h2 : ‖ctrlU (N := N) (K := K) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

private theorem posTC_ctrlU {Y : Op N (RK N K)} (hY : PosTC Y) :
    PosTC (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU) :=
  ⟨hY.1.conj_adjoint ctrlU, by rw [tr_ctrlU hY]; exact hY.2⟩

private theorem kz (Y : Op N (RK N K)) (a b : H N (RK N K)) :
    krausMat (fun _ => (0 : Op N (RK N K))) Y a b = 0 := by
  simp [krausMat]

private theorem inner_beta (x : Fin N) (Y : Op N (RK N K)) (a b : H N K) :
    ⟪a, beta x Y b⟫_ℂ = (N : ℂ) * ⟪slot x a, Y (slot x b)⟫_ℂ := by
  simp only [beta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]

open scoped ComplexOrder in
private theorem beta_pos (x : Fin N) {Y : Op N (RK N K)} (hY : Y.IsPositive) : (beta x Y).IsPositive := by
  have h0 : (0 : ℂ) ≤ (N : ℂ) := by
    rw [← Complex.ofReal_natCast]; exact Complex.zero_le_real.2 (Nat.cast_nonneg N)
  exact (hY.adjoint_conj (slot x)).smul_of_nonneg h0

private theorem beta_tr_le (x : Fin N) {Y : Op N (RK N K)} (hY : Y.IsPositive) :
    tr (beta x Y) ≤ (N : ℝ≥0∞) * tr Y := by
  rw [tr_eq_sum_beta hY]
  exact Finset.single_le_sum (f := fun y => tr (beta y Y)) (fun _ _ => by simp) (Finset.mem_univ x)

private theorem beta_uEmb_conj (x : Fin N) (ρ : Op N K) :
    beta x (uEmb ∘L ρ ∘L ContinuousLinearMap.adjoint uEmb) = ρ := by
  have hN : N ≠ 0 := (Fin.pos x).ne'
  ext1 v
  simp only [beta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, adj_uEmb_slot,
    adj_slot_uEmb, map_smul, smul_smul]
  rw [c_mul_c hN, one_smul]

private theorem beta_pom {α : Type} [MeasurableSpace α] {Λ' : Set α → Op N (RK N K)} (hP : IsPOM Λ')
    (x : Fin N) : IsPOM (fun E => beta x (Λ' E)) where
  pos E hE := beta_pos x (hP.pos E hE)
  trace_lt_top E hE := (beta_tr_le x (hP.pos E hE)).trans_lt
    (ENNReal.mul_lt_top (ENNReal.natCast_ne_top N).lt_top (hP.trace_lt_top E hE))
  additive E hEm hEd a b := by
    simp only [inner_beta]
    exact (hP.additive E hEm hEd _ _).mul_left _

/-- Mathlib infers separability of the register workspace (checked here). -/
example [TopologicalSpace.SeparableSpace K] : TopologicalSpace.SeparableSpace (RK N K) := inferInstance

end Register

/-! Helpers: the trace of a weak integral. -/

section Weak

variable {N : ℕ} {α : Type} [MeasurableSpace α]

private theorem weak_tr {K₁ : Type} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
    [TopologicalSpace.SeparableSpace K₁] {ν : Measure α} {Yf : α → Op N K₁} {Y : Op N K₁}
    (hpos : ∀ h, (Yf h).IsPositive) (hmeas : ∀ a b : H N K₁, Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hint : ∫⁻ h, tr (Yf h) ∂ν < ∞) (hY : ∀ a b : H N K₁, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂ν) :
    tr Y = ∫⁻ h, tr (Yf h) ∂ν := by
  obtain ⟨Y', -, hYtr, hYm⟩ := exists_weakInt hpos hmeas hint
  have hYY : Y' = Y := by
    ext1 b
    refine ext_inner_left ℂ fun a => ?_
    rw [hYm, hY]
  rw [← hYY, hYtr]

private theorem weak_conj {K₁ K₂ : Type} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    [TopologicalSpace.SeparableSpace K₂] {ν : Measure α} {Yf : α → Op N K₁} {Y : Op N K₁}
    (V : H N K₂ →L[ℂ] H N K₁)
    (hpos : ∀ h, (Yf h).IsPositive) (hmeas : ∀ a b : H N K₁, Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hint : ∫⁻ h, tr (ContinuousLinearMap.adjoint V ∘L Yf h ∘L V) ∂ν < ∞)
    (hY : ∀ a b : H N K₁, ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂ν) :
    tr (ContinuousLinearMap.adjoint V ∘L Y ∘L V) =
      ∫⁻ h, tr (ContinuousLinearMap.adjoint V ∘L Yf h ∘L V) ∂ν := by
  refine weak_tr (fun h => (hpos h).adjoint_conj V) (fun a b => ?_) hint (fun a b => ?_)
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    exact hmeas _ _
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    exact hY _ _

end Weak

namespace Alg

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Ω : ℕ → Type} [∀ m, MeasurableSpace (Ω m)]

/-- Kraus operators of the joint step kernel `Ψ_{M,h}(F)` on `H'`: `id_R ⊗ A_k` after an operation kind,
`(id_R ⊗ A_k) U` after a query kind (`Ψ(Y) = (id_R ⊗ I)(U Y U*)`), none (all `0`) after a halt kind. -/
def jointKraus (A : Alg N K Ω) (M : ℕ) (h : Hist Ω M) (F : Set (Ω M)) : ℕ → Op N (RK N K) :=
  match A.kind M h with
  | .op => fun k => liftOp (A.kraus M h F k)
  | .query => fun k => liftOp (A.kraus M h F k) ∘L ctrlU
  | .halt _ => fun _ => 0

/-! Helpers: kind cases and the polarised form of the lifted Kraus matrix elements. -/

private theorem jk_kind_cases (k : Kind N) : k = Kind.op ∨ k = Kind.query ∨ ∃ y, k = Kind.halt y := by
  cases k with
  | op => exact Or.inl rfl
  | query => exact Or.inr (Or.inl rfl)
  | halt y => exact Or.inr (Or.inr ⟨y, rfl⟩)

private theorem jk_op (A : Alg N K Ω) (M : ℕ) (h : Hist Ω M) (hk : A.kind M h = Kind.op) :
    A.jointKraus M h = fun F k => liftOp (A.kraus M h F k) := by
  funext F
  unfold jointKraus
  simp only [hk]

private theorem jk_query (A : Alg N K Ω) (M : ℕ) (h : Hist Ω M) (hk : A.kind M h = Kind.query) :
    A.jointKraus M h = fun F k => liftOp (A.kraus M h F k) ∘L ctrlU := by
  funext F
  unfold jointKraus
  simp only [hk]

private theorem jk_halt (A : Alg N K Ω) (M : ℕ) (h : Hist Ω M) {y : Fin N}
    (hk : A.kind M h = Kind.halt y) : A.jointKraus M h = fun _ _ => 0 := by
  funext F
  unfold jointKraus
  simp only [hk]

private theorem jk_sop (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M)
    (hk : A.kind M h = Kind.op) : A.stepKraus x M h = A.kraus M h := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem jk_squery (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M)
    (hk : A.kind M h = Kind.query) :
    A.stepKraus x M h = fun F k => A.kraus M h F k ∘L oracleL x := by
  funext F
  unfold stepKraus
  simp only [hk]

private theorem jk_shalt (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M) {y : Fin N}
    (hk : A.kind M h = Kind.halt y) : A.stepKraus x M h = fun _ _ => 0 := by
  funext F
  unfold stepKraus
  simp only [hk]

/-- The polarised sum of `krausMat_liftOp`. -/
private def jkS (A : Alg N K Ω) (M : ℕ) (F : Set (Ω M)) (Y : Op N (RK N K)) (a b : H N (RK N K))
    (h : Hist Ω M) : ℂ :=
  ∑ r : Fin N, ∑ r' : Fin N, pc (fun s => krausMat (A.kraus M h F) (pz r r' s Y)
    (ContinuousLinearMap.adjoint (slot r) a) (ContinuousLinearMap.adjoint (slot r') b))

private theorem jk_lift (A : Alg N K Ω) (M : ℕ) (h : Hist Ω M) {F : Set (Ω M)} (hF : MeasurableSet F)
    {Y : Op N (RK N K)} (hY : PosTC Y) (a b : H N (RK N K)) :
    krausMat (fun k => liftOp (A.kraus M h F k)) Y a b = jkS A M F Y a b h :=
  krausMat_liftOp (A.bounded M h F hF) hY a b

private theorem jk_lift_q (A : Alg N K Ω) (M : ℕ) (h : Hist Ω M) {F : Set (Ω M)} (hF : MeasurableSet F)
    {Y : Op N (RK N K)} (hY : PosTC Y) (a b : H N (RK N K)) :
    krausMat (fun k => liftOp (A.kraus M h F k) ∘L ctrlU) Y a b =
      jkS A M F (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU) a b h :=
  (krausMatG_comp (fun k => liftOp (A.kraus M h F k)) ctrlU Y a b).trans
    (krausMat_liftOp (A.bounded M h F hF) (posTC_ctrlU hY) a b)

private theorem jkS_hasSum (A : Alg N K Ω) (M : ℕ) (h : Hist Ω M) {Fs : ℕ → Set (Ω M)}
    (hFm : ∀ n, MeasurableSet (Fs n)) (hFd : Pairwise (fun i j => Disjoint (Fs i) (Fs j)))
    {Y : Op N (RK N K)} (hY : PosTC Y) (a b : H N (RK N K)) :
    HasSum (fun n => jkS A M (Fs n) Y a b h) (jkS A M (⋃ n, Fs n) Y a b h) := by
  unfold jkS
  exact hasSum_sum fun r _ => hasSum_sum fun r' _ =>
    hasSum_pc fun s hs => A.additive M h Fs hFm hFd _ (posTC_pz r r' hs hY) _ _

private theorem measurable_jkS (A : Alg N K Ω) (M : ℕ) {F : Set (Ω M)} (hF : MeasurableSet F)
    {Y : Op N (RK N K)} (hY : PosTC Y) (a b : H N (RK N K)) :
    Measurable (fun h => jkS A M F Y a b h) := by
  unfold jkS
  exact Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun r' _ =>
    measurable_pc fun s hs => A.measurable M F hF _ (posTC_pz r r' hs hY) _ _

/-- The joint step kernel `Ψ_M` is a measurable CP kernel from `Hist Ω M` to `Ω M` on `H'`
(paragraph "The reference register"). Additivity and measurability need polarisation of the off-diagonal
register blocks `Y_{rr'}`, since the fields of `Alg` cover only `PosTC Y`. -/
theorem isKrausKernel_jointKraus (A : Alg N K Ω) (M : ℕ) : IsKrausKernel (A.jointKraus M) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro h F hF ψ
    rcases jk_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
    · rw [jk_op A M h hk]
      exact liftOp_bound (A.bounded M h F hF) ψ
    · rw [jk_query A M h hk]
      simp only [ContinuousLinearMap.comp_apply]
      have hb := liftOp_bound (A.bounded M h F hF) (ctrlU ψ)
      rwa [norm_ctrlU_apply] at hb
    · rw [jk_halt A M h hk]
      simp
  · intro h Fs hFm hFd Y hY a b
    rcases jk_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
    · rw [jk_op A M h hk]
      have e : ∀ n, krausMat (fun k => liftOp (A.kraus M h (Fs n) k)) Y a b = jkS A M (Fs n) Y a b h :=
        fun n => jk_lift A M h (hFm n) hY a b
      simp only [e, jk_lift A M h (MeasurableSet.iUnion hFm) hY a b]
      exact jkS_hasSum A M h hFm hFd hY a b
    · rw [jk_query A M h hk]
      have e : ∀ n, krausMat (fun k => liftOp (A.kraus M h (Fs n) k) ∘L ctrlU) Y a b =
          jkS A M (Fs n) (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU) a b h :=
        fun n => jk_lift_q A M h (hFm n) hY a b
      simp only [e, jk_lift_q A M h (MeasurableSet.iUnion hFm) hY a b]
      exact jkS_hasSum A M h hFm hFd (posTC_ctrlU hY) a b
    · rw [jk_halt A M h hk]
      simp only [kz]
      exact hasSum_zero
  · intro F hF Y hY a b
    have hop : MeasurableSet (A.kind M ⁻¹' {Kind.op}) :=
      A.kind_meas M MeasurableSpace.measurableSet_top
    have hq : MeasurableSet (A.kind M ⁻¹' {Kind.query}) :=
      A.kind_meas M MeasurableSpace.measurableSet_top
    have hfun : (fun h => krausMat (A.jointKraus M h F) Y a b) = fun h =>
        if h ∈ A.kind M ⁻¹' {Kind.op} then jkS A M F Y a b h
        else if h ∈ A.kind M ⁻¹' {Kind.query} then
          jkS A M F (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU) a b h
        else 0 := by
      funext h
      rcases jk_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
      · rw [jk_op A M h hk]
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hk, ↓reduceIte]
        exact jk_lift A M h hF hY a b
      · rw [jk_query A M h hk]
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hk, reduceCtorEq, ↓reduceIte]
        exact jk_lift_q A M h hF hY a b
      · rw [jk_halt A M h hk]
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hk, reduceCtorEq, ↓reduceIte]
        exact kz Y a b
    rw [hfun]
    exact Measurable.ite hop (measurable_jkS A M hF hY a b)
      (Measurable.ite hq (measurable_jkS A M hF (posTC_ctrlU hY) a b) measurable_const)

/-- (M2) for the step kernels, the form used in the proof of lem:m-joint(i):
`β_x ∘ Ψ_{M,h}(F) = Ξ^x_{M,h}(F) ∘ β_x`, in matrix elements. -/
theorem stepKraus_beta (A : Alg N K Ω) (x : Fin N) (M : ℕ) (h : Hist Ω M) (F : Set (Ω M))
    (Y : Op N (RK N K)) (a b : H N K) :
    krausMat (A.stepKraus x M h F) (beta x Y) a b =
      (N : ℂ) * krausMat (A.jointKraus M h F) Y (slot x a) (slot x b) := by
  rcases jk_kind_cases (A.kind M h) with hk | hk | ⟨y, hk⟩
  · rw [jk_sop A x M h hk, jk_op A M h hk]
    exact beta_liftKraus (A.kraus M h F) x Y a b
  · rw [jk_squery A x M h hk, jk_query A M h hk]
    have h1 := krausMatG_comp (A.kraus M h F) (oracleL x) (beta x Y) a b
    have h2 := krausMatG_comp (fun k => liftOp (A.kraus M h F k)) ctrlU Y (slot x a) (slot x b)
    rw [← beta_ctrlU] at h1
    have h3 := beta_liftKraus (A.kraus M h F) x (ctrlU ∘L Y ∘L ContinuousLinearMap.adjoint ctrlU) a b
    show krausMatG (fun k => A.kraus M h F k ∘L oracleL x) (beta x Y) a b =
      (N : ℂ) * krausMatG (fun k => liftOp (A.kraus M h F k) ∘L ctrlU) Y (slot x a) (slot x b)
    rw [h1, h2]
    exact h3
  · rw [jk_shalt A x M h hk, jk_halt A M h hk]
    simp [krausMat]

/-- `Λ` is the family of joint measures `Λ_M` of `A` on `H'` (paragraph "The reference register"), in the
form of `IsHistory`: `Λ_0({∅}) = |u⟩⟨u| ⊗ ρ₀`, every `Λ_M` is a positive operator measure, and
`Λ_{M+1}(G) = ∫ Ψ_{M,h}(G_h)(σ(h)) τ(dh)` (weakly) for a density `(σ, τ)` of `Λ_M`
(`Λ_{M+1} = Ψ_M ∘ Λ_M`, Lemma lem:m-comp(ii)). -/
structure IsJoint (A : Alg N K Ω) (Λ : HistFam N (RK N K) Ω) : Prop where
  init : Λ 0 Set.univ = uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb
  pom : ∀ M, IsPOM (Λ M)
  step : ∀ M, ∃ (τ : Measure (Hist Ω M)) (σ : Hist Ω M → Op N (RK N K)), IsDensity (Λ M) τ σ ∧
    ∀ G : Set (Hist Ω (M + 1)), MeasurableSet G → ∀ a b : H N (RK N K),
      ⟪a, Λ (M + 1) G b⟫_ℂ = ∫ h, krausMat (A.jointKraus M h (Hist.sect G h)) (σ h) a b ∂τ

/-! Helpers: the depth-0 joint measure, copied from `TheoremS/Meas/Hist.lean` on `H'`. -/

omit [∀ m, MeasurableSpace (Ω m)] in
private theorem jhist0_sub : Subsingleton (Hist Ω 0) :=
  ⟨fun u v => Subsingleton.elim (α := Unit) u v⟩

open Classical in
private def jhist0 (A : Alg N K Ω) : Set (Hist Ω 0) → Op N (RK N K) :=
  fun E => if E.Nonempty then uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb else 0

private theorem jtr_zero : tr (0 : Op N (RK N K)) = 0 := by
  simp [tr]

private theorem jrho_pos (A : Alg N K Ω) :
    (uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb : Op N (RK N K)).IsPositive :=
  A.rho0_pos.conj_adjoint uEmb

private theorem jrho_tr (A : Alg N K Ω) :
    tr (uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb : Op N (RK N K)) = 1 := by
  rw [tr_uEmb_conj A.rho0_pos, A.rho0_tr]

private theorem jhist0_pom (A : Alg N K Ω) : IsPOM (jhist0 A) where
  pos E _ := by
    unfold jhist0
    split_ifs
    · exact jrho_pos A
    · exact ContinuousLinearMap.isPositive_zero
  trace_lt_top E _ := by
    unfold jhist0
    split_ifs
    · rw [jrho_tr A]; exact ENNReal.one_lt_top
    · rw [jtr_zero]; exact ENNReal.zero_lt_top
  additive E _ hdisj a b := by
    have := jhist0_sub (Ω := Ω)
    by_cases hex : ∃ n, (E n).Nonempty
    · obtain ⟨n, hn⟩ := hex
      have hU : (⋃ m, E m).Nonempty := hn.mono (Set.subset_iUnion E n)
      have hzero : ∀ m, m ≠ n → ⟪a, jhist0 A (E m) b⟫_ℂ = 0 := by
        intro m hm
        have hm' : ¬ (E m).Nonempty := by
          rintro ⟨u, hu⟩
          obtain ⟨v, hv⟩ := hn
          have huv : u = v := Subsingleton.elim u v
          subst huv
          exact Set.disjoint_left.1 (hdisj hm) hu hv
        simp [jhist0, hm']
      have h := hasSum_single (f := fun m => ⟪a, jhist0 A (E m) b⟫_ℂ) n hzero
      convert h using 1
      simp only [jhist0, hU, hn, ↓reduceIte]
    · simp only [not_exists, Set.not_nonempty_iff_eq_empty] at hex
      have hU : ¬ (⋃ m, E m).Nonempty := by
        rintro ⟨u, hu⟩
        obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hu
        exact Set.not_nonempty_iff_eq_empty.2 (hex m) ⟨u, hm⟩
      have hE : ∀ m, ¬ (E m).Nonempty := fun m => Set.not_nonempty_iff_eq_empty.2 (hex m)
      have hf : (fun m => ⟪a, jhist0 A (E m) b⟫_ℂ) = fun _ => 0 := by
        funext m
        simp [jhist0, hE m]
      rw [hf]
      simp only [jhist0, hU, ↓reduceIte, ContinuousLinearMap.zero_apply, inner_zero_right]
      exact hasSum_zero

variable [TopologicalSpace.SeparableSpace K]

/-! Helpers: the recursion of `TheoremS/Meas/Hist.lean` for the kernel `A.jointKraus`. -/

private abbrev JPomAt (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (Ω : ℕ → Type) [∀ m, MeasurableSpace (Ω m)] (M : ℕ) :=
  {Λ : Set (Hist Ω M) → Op N (RK N K) // IsPOM Λ}

private def jstTau (A : Alg N K Ω) {M : ℕ} (Λ : JPomAt N K Ω M) : Measure (Hist Ω M) :=
  Classical.choose (exists_density Λ.2 (uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb)
    (jrho_pos A) (jrho_tr A))

private def jstSig (A : Alg N K Ω) {M : ℕ} (Λ : JPomAt N K Ω M) : Hist Ω M → Op N (RK N K) :=
  Classical.choose (Classical.choose_spec (exists_density Λ.2
    (uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb) (jrho_pos A) (jrho_tr A)))

private theorem jstDens (A : Alg N K Ω) {M : ℕ} (Λ : JPomAt N K Ω M) :
    IsDensity Λ.1 (jstTau A Λ) (jstSig A Λ) :=
  (Classical.choose_spec (Classical.choose_spec (exists_density Λ.2
    (uEmb ∘L A.rho0 ∘L ContinuousLinearMap.adjoint uEmb) (jrho_pos A) (jrho_tr A)))).1

private def jstNextFun (A : Alg N K Ω) {M : ℕ} (Λ : JPomAt N K Ω M) :
    Set (Hist Ω M × Ω M) → Op N (RK N K) :=
  Classical.choose ((A.isKrausKernel_jointKraus M).exists_comp (jstDens A Λ))

private theorem jstNextFun_spec (A : Alg N K Ω) {M : ℕ} (Λ : JPomAt N K Ω M) :
    IsPOM (jstNextFun A Λ) ∧ ∀ G : Set (Hist Ω M × Ω M), MeasurableSet G → ∀ a b : H N (RK N K),
      ⟪a, jstNextFun A Λ G b⟫_ℂ =
        ∫ h, krausMat (A.jointKraus M h (Prod.mk h ⁻¹' G)) (jstSig A Λ h) a b ∂(jstTau A Λ) :=
  Classical.choose_spec ((A.isKrausKernel_jointKraus M).exists_comp (jstDens A Λ))

private def jstNext (A : Alg N K Ω) {M : ℕ} (Λ : JPomAt N K Ω M) : JPomAt N K Ω (M + 1) :=
  ⟨jstNextFun A Λ, (jstNextFun_spec A Λ).1⟩

private def jhistSeq (A : Alg N K Ω) : (M : ℕ) → JPomAt N K Ω M
  | 0 => ⟨jhist0 A, jhist0_pom A⟩
  | M + 1 => jstNext A (jhistSeq A M)

/-- The joint measures exist (Lemmas lem:m-dens and lem:m-comp(ii) on `H'`, by induction on the depth). -/
theorem exists_joint (A : Alg N K Ω) : ∃ Λ : HistFam N (RK N K) Ω, A.IsJoint Λ := by
  refine ⟨fun M => (jhistSeq A M).1, ?_, fun M => (jhistSeq A M).2, fun M => ?_⟩
  · show jhist0 A Set.univ = _
    have hne : (Set.univ : Set (Hist Ω 0)).Nonempty := ⟨(() : Unit), Set.mem_univ _⟩
    simp only [jhist0, hne, ↓reduceIte]
  · exact ⟨jstTau A (jhistSeq A M), jstSig A (jhistSeq A M), jstDens A (jhistSeq A M),
      fun G hG a b => (jstNextFun_spec A (jhistSeq A M)).2 G hG a b⟩

/-! Helpers: trace and `Cf` of weak integrals over `E`, and of the joint step on `univ`. -/

private theorem jt_weak {α : Type} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {Yf : α → Op N (RK N K)} {Y : Op N (RK N K)} (hpos : ∀ h, (Yf h).IsPositive)
    (hle : ∀ h, tr (Yf h) ≤ 1) (hmeas : ∀ a b : H N (RK N K), Measurable (fun h => ⟪a, Yf h b⟫_ℂ))
    (hY : ∀ a b : H N (RK N K), ⟪a, Y b⟫_ℂ = ∫ h, ⟪a, Yf h b⟫_ℂ ∂ν) :
    tr Y = ∫⁻ h, tr (Yf h) ∂ν ∧ Cf Y = ∫⁻ h, Cf (Yf h) ∂ν := by
  have hint : ∫⁻ h, tr (Yf h) ∂ν < ∞ :=
    calc ∫⁻ h, tr (Yf h) ∂ν ≤ ∫⁻ _, 1 ∂ν := lintegral_mono fun h => hle h
      _ = ν Set.univ := lintegral_one
      _ < ∞ := measure_lt_top ν _
  have hintC : ∫⁻ h, Cf (Yf h) ∂ν < ∞ :=
    calc ∫⁻ h, Cf (Yf h) ∂ν ≤ ∫⁻ h, tr (Yf h) ∂ν :=
          lintegral_mono fun h => Cf_le_tr ⟨hpos h, (hle h).trans_lt ENNReal.one_lt_top⟩
      _ < ∞ := hint
  exact ⟨weak_tr hpos hmeas hint hY, weak_conj uEmb hpos hmeas hintC hY⟩

private theorem jt_core (A : Alg N K Ω) {M : ℕ} {τ : Measure (Hist Ω M)}
    {σ : Hist Ω M → Op N (RK N K)} {Λ' : Set (Hist Ω M) → Op N (RK N K)} (hd : IsDensity Λ' τ σ)
    {E : Set (Hist Ω M)} {Y : Op N (RK N K)}
    (hY : ∀ a b : H N (RK N K),
      ⟪a, Y b⟫_ℂ = ∫ h in E, krausMat (A.jointKraus M h Set.univ) (σ h) a b ∂τ) :
    ∃ Z : Hist Ω M → Op N (RK N K), (∀ h, (Z h).IsPositive) ∧
      (∀ h (a c : H N (RK N K)), ⟪a, Z h c⟫_ℂ = krausMatG (A.jointKraus M h Set.univ) (σ h) a c) ∧
      tr Y = ∫⁻ h in E, tr (Z h) ∂τ ∧ Cf Y = ∫⁻ h in E, Cf (Z h) ∂τ := by
  haveI := hd.finite
  have hK := A.isKrausKernel_jointKraus M
  have hσB : ∀ h, trB (hbasis N (RK N K)) (σ h) < ∞ := fun h => by
    rw [← tr_eq_trB, hd.trace_one h]; exact ENNReal.one_lt_top
  choose Z hZpos hZ using fun h => exists_krausOp (b := hbasis N (RK N K))
    (hK.bounded h Set.univ MeasurableSet.univ) (hd.pos h) (hσB h)
  have hZle : ∀ h, tr (Z h) ≤ 1 := fun h => by
    rw [tr_eq_trB, ← hd.trace_one h, tr_eq_trB]
    exact trB_le_of_krausMatG (hK.bounded h Set.univ MeasurableSet.univ) (hd.pos h) (hσB h) (hZ h)
  have hσfin : ∀ h, tr (σ h) < ∞ := fun h => by rw [hd.trace_one h]; exact ENNReal.one_lt_top
  have hmeas : ∀ a b : H N (RK N K), Measurable (fun h => ⟪a, Z h b⟫_ℂ) := by
    intro a b
    have hm := hK.measurable_sect_field MeasurableSet.univ hd.pos hσfin hd.meas a b
    simp only [Set.preimage_univ] at hm
    have e : (fun h => ⟪a, Z h b⟫_ℂ) = fun h => krausMat (A.jointKraus M h Set.univ) (σ h) a b :=
      funext fun h => hZ h a b
    rw [e]
    exact hm
  obtain ⟨h1, h2⟩ := jt_weak (ν := τ.restrict E) hZpos hZle hmeas fun a b =>
    (hY a b).trans (integral_congr_ae (Filter.Eventually.of_forall fun h => (hZ h a b).symm))
  exact ⟨Z, hZpos, hZ, h1, h2⟩

variable {A : Alg N K Ω} {Λ : HistFam N (RK N K) Ω}

/-- Lemma lem:m-joint(i), first claim, in the form proved: `M ↦ β_x ∘ Λ_M` is a history family of `A`
for `x` (no induction: for each `M`, `IsPOM (β_x ∘ Λ_M)`, a density of it from `exists_density` on `H`,
and Lemma lem:m-comp(iii) (`integral_sect_eq`) with `(ν, ξ) = (τ, β_x ∘ σ)`, using (M2) `stepKraus_beta`). -/
theorem isHistory_beta (hΛ : A.IsJoint Λ) (x : Fin N) :
    A.IsHistory x (fun M E => beta x (Λ M E)) := by
  refine ⟨?_, fun M => beta_pom (hΛ.pom M) x, fun M => ?_⟩
  · show beta x (Λ 0 Set.univ) = A.rho0
    rw [hΛ.init, beta_uEmb_conj]
  · obtain ⟨τ, σ, hd, heq⟩ := hΛ.step M
    haveI := hd.finite
    obtain ⟨τ', σ', hd', -⟩ :=
      exists_density (beta_pom (hΛ.pom M) x) A.rho0 A.rho0_pos A.rho0_tr
    refine ⟨τ', σ', hd', fun G hG a b => ?_⟩
    have hbd : ∀ h, tr (beta x (σ h)) ≤ (N : ℝ≥0∞) := fun h => by
      have hb := beta_tr_le x (hd.pos h)
      rwa [hd.trace_one h, mul_one] at hb
    have hpos : ∀ h, (beta x (σ h)).IsPositive := fun h => beta_pos x (hd.pos h)
    have hfin : ∀ h, tr (beta x (σ h)) < ∞ := fun h =>
      (hbd h).trans_lt (ENNReal.natCast_ne_top N).lt_top
    have hmeas : ∀ a' b' : H N K, Measurable (fun h => ⟪a', beta x (σ h) b'⟫_ℂ) := fun a' b' => by
      simp only [inner_beta]
      exact (hd.meas _ _).const_mul _
    have hint : ∫⁻ h, tr (beta x (σ h)) ∂τ < ∞ :=
      calc ∫⁻ h, tr (beta x (σ h)) ∂τ ≤ ∫⁻ _, (N : ℝ≥0∞) ∂τ := lintegral_mono fun h => hbd h
        _ = N * τ Set.univ := lintegral_const _
        _ < ∞ := ENNReal.mul_lt_top (ENNReal.natCast_ne_top N).lt_top (measure_lt_top τ _)
    have hrepr : ∀ E, MeasurableSet E → ∀ a' b' : H N K,
        ⟪a', beta x (Λ M E) b'⟫_ℂ = ∫ h in E, ⟪a', beta x (σ h) b'⟫_ℂ ∂τ := fun E hE a' b' => by
      simp only [inner_beta]
      rw [hd.repr E hE, integral_const_mul]
    have key := (A.isKrausKernel_stepKraus x M).integral_sect_eq hd' τ hpos hfin hmeas hint hrepr
      hG a b
    show ⟪a, beta x (Λ (M + 1) G) b⟫_ℂ = ∫ h, A.stepMat x M h (Hist.sect G h) (σ' h) a b ∂τ'
    simp only [A.stepMat_eq]
    rw [inner_beta, heq G hG, ← integral_const_mul]
    refine Eq.trans ?_ key
    exact integral_congr_ae (Filter.Eventually.of_forall fun h =>
      (stepKraus_beta A x M h _ (σ h) a b).symm)

/-- Lemma lem:m-joint(i), first claim: `β_x(Λ_M(E)) = ρ^{(M)}_x(E)` (from `isHistory_beta` and
`historyUnique`, whose binder `[∀ m, Nonempty (Ω m)]` is carried here). -/
theorem beta_joint [∀ m, Nonempty (Ω m)] (hΛ : A.IsJoint Λ) {x : Fin N} {ρ : HistFam N K Ω}
    (hρ : A.IsHistory x ρ) (M : ℕ)
    (E : Set (Hist Ω M)) (hE : MeasurableSet E) : beta x (Λ M E) = ρ M E := by
  exact historyUnique N K Ω A x (fun M E => beta x (Λ M E)) ρ (isHistory_beta hΛ x) hρ M E hE

/-- Lemma lem:m-joint(i), second claim: `W(Λ_M(E)) = (1/N) ∑_x p^{(M)}_x(E)`, written
`N W(Λ_M(E)) = ∑_x p^{(M)}_x(E)`. -/
theorem tr_joint [∀ m, Nonempty (Ω m)] (hΛ : A.IsJoint Λ) {ρ : Fin N → HistFam N K Ω} (hρ : ∀ x, A.IsHistory x (ρ x))
    (M : ℕ) (E : Set (Hist Ω M)) (hE : MeasurableSet E) :
    (N : ℝ≥0∞) * tr (Λ M E) = ∑ x : Fin N, tr (ρ x M E) := by
  rw [tr_eq_sum_beta ((hΛ.pom M).pos E hE)]
  exact Finset.sum_congr rfl fun x _ => by rw [beta_joint hΛ (hρ x) M E hE]

/-- Lemma lem:m-joint(ii), operation kind: for `E ⊆ k_M⁻¹(o)`, `W` and `C` take the same values at
`Λ_{M+1}(E × Ω_{M+1})` as at `Λ_M(E)`. -/
theorem joint_op (hΛ : A.IsJoint Λ) {M : ℕ} {E : Set (Hist Ω M)} (hE : MeasurableSet E)
    (hEk : E ⊆ A.kind M ⁻¹' {Kind.op}) :
    tr (Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1)))) = tr (Λ M E) ∧
      Cf (Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1)))) = Cf (Λ M E) := by
  obtain ⟨τ, σ, hd, heq⟩ := hΛ.step M
  haveI := hd.finite
  have hK := A.isKrausKernel_jointKraus M
  obtain ⟨Z, -, hZ, hZtr, hZC⟩ := jt_core A hd (E := E)
    (Y := Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1)))) fun a b =>
      (heq (E ×ˢ (Set.univ : Set (Ω M))) (hE.prod MeasurableSet.univ) a b).trans
        (hK.integral_sect_prod_univ hd hE a b)
  have hσ : ∀ h, PosTC (σ h) := fun h =>
    ⟨hd.pos h, by rw [hd.trace_one h]; exact ENNReal.one_lt_top⟩
  obtain ⟨hΛtr, hΛC⟩ := jt_weak (ν := τ.restrict E) hd.pos (fun h => (hd.trace_one h).le) hd.meas
    (hd.repr E hE)
  have hpt : ∀ h ∈ E, tr (Z h) = tr (σ h) ∧ Cf (Z h) = Cf (σ h) := by
    intro h hh
    have hk : A.kind M h = Kind.op := hEk hh
    refine lift_kraus_eq (A.normalised M h) (hσ h) fun a c => ?_
    rw [hZ h a c, jk_op A M h hk]
  refine ⟨?_, ?_⟩
  · rw [hZtr, hΛtr]
    exact setLIntegral_congr_fun hE fun h hh => (hpt h hh).1
  · rw [hZC, hΛC]
    exact setLIntegral_congr_fun hE fun h hh => (hpt h hh).2

/-- Lemma lem:m-joint(ii), query kind: for `E ⊆ k_M⁻¹(q)`, `W` and `C` take the same values at
`Λ_{M+1}(E × Ω_{M+1})` as at `U Λ_M(E) U*`. -/
theorem joint_query (hΛ : A.IsJoint Λ) {M : ℕ} {E : Set (Hist Ω M)} (hE : MeasurableSet E)
    (hEk : E ⊆ A.kind M ⁻¹' {Kind.query}) :
    tr (Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1)))) = tr (Λ M E) ∧
      Cf (Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1)))) =
        Cf (ctrlU ∘L Λ M E ∘L ContinuousLinearMap.adjoint ctrlU) := by
  obtain ⟨τ, σ, hd, heq⟩ := hΛ.step M
  haveI := hd.finite
  have hK := A.isKrausKernel_jointKraus M
  obtain ⟨Z, -, hZ, hZtr, hZC⟩ := jt_core A hd (E := E)
    (Y := Λ (M + 1) (E ×ˢ (Set.univ : Set (Ω M)) : Set (Hist Ω (M + 1)))) fun a b =>
      (heq (E ×ˢ (Set.univ : Set (Ω M))) (hE.prod MeasurableSet.univ) a b).trans
        (hK.integral_sect_prod_univ hd hE a b)
  have hσ : ∀ h, PosTC (σ h) := fun h =>
    ⟨hd.pos h, by rw [hd.trace_one h]; exact ENNReal.one_lt_top⟩
  have hUσ : ∀ h, PosTC (ctrlU ∘L σ h ∘L ContinuousLinearMap.adjoint ctrlU) := fun h =>
    posTC_ctrlU (hσ h)
  obtain ⟨hΛtr, -⟩ := jt_weak (ν := τ.restrict E) hd.pos (fun h => (hd.trace_one h).le) hd.meas
    (hd.repr E hE)
  obtain ⟨-, hΛC⟩ := jt_weak (ν := τ.restrict E)
    (Yf := fun h => ctrlU ∘L σ h ∘L ContinuousLinearMap.adjoint ctrlU)
    (Y := ctrlU ∘L Λ M E ∘L ContinuousLinearMap.adjoint ctrlU) (fun h => (hUσ h).1)
    (fun h => (tr_ctrlU (hσ h)).le.trans (hd.trace_one h).le)
    (fun a b => by
      simp only [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_left (ctrlU (N := N) (K := K))]
      exact hd.meas _ _)
    (fun a b => by
      simp only [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_left (ctrlU (N := N) (K := K))]
      exact hd.repr E hE _ _)
  have hpt : ∀ h ∈ E, tr (Z h) = tr (ctrlU ∘L σ h ∘L ContinuousLinearMap.adjoint ctrlU) ∧
      Cf (Z h) = Cf (ctrlU ∘L σ h ∘L ContinuousLinearMap.adjoint ctrlU) := by
    intro h hh
    have hk : A.kind M h = Kind.query := hEk hh
    refine lift_kraus_eq (A.normalised M h) (hUσ h) fun a c => ?_
    rw [hZ h a c, jk_query A M h hk]
    exact krausMatG_comp (fun k => liftOp (A.kraus M h Set.univ k)) ctrlU (σ h) a c
  refine ⟨?_, ?_⟩
  · rw [hZtr, hΛtr]
    exact setLIntegral_congr_fun hE fun h hh => (hpt h hh).1.trans (tr_ctrlU (hσ h))
  · rw [hZC, hΛC]
    exact setLIntegral_congr_fun hE fun h hh => (hpt h hh).2

end Alg

end

end TheoremS.Meas
