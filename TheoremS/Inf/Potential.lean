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
Countable subadditivity of the potential `Vf` (the countable case of the paper's subadditivity lemma).
Pure real analysis; uses only `Vf_add`, `Vf_le`, `Vf_nonneg`, `Vf_finset_sum` from
`TheoremS/Potential.lean`.
-/
import TheoremS.Potential

namespace TheoremS.Inf

set_option autoImplicit false

open TheoremS
open Filter Topology

/-- Countable subadditivity of `Vf`: for nonnegative `C ≤ W` with sums `c` and `w`, the family
`Vf (C i) (W i)` is summable and `Vf c w ≤ ∑' i, Vf (C i) (W i)`. -/
theorem Vf_hasSum {ι : Type*} (C W : ι → ℝ) (h0 : ∀ i, 0 ≤ C i) (h1 : ∀ i, C i ≤ W i)
    {c w : ℝ} (hc : HasSum C c) (hw : HasSum W w) :
    Summable (fun i => Vf (C i) (W i)) ∧ Vf c w ≤ ∑' i, Vf (C i) (W i) := by
  have hs : Summable (fun i => Vf (C i) (W i)) :=
    Summable.of_nonneg_of_le (fun i => Vf_nonneg _ _ (h0 i) (h1 i))
      (fun i => Vf_le _ _ (h0 i) (h1 i)) (hc.summable.mul_left (Real.pi / 8 + 1 / 4))
  refine ⟨hs, ?_⟩
  have key : ∀ F : Finset ι, Vf c w ≤
      ∑' i, Vf (C i) (W i) + (Real.pi / 8 + 1 / 4) * (c - ∑ i ∈ F, C i) := by
    intro F
    have hF0 : ∑ i ∈ F, C i ≤ c := sum_le_hasSum F (fun i _ => h0 i) hc
    have hdiff : HasSum (fun i => W i - C i) (w - c) := hw.sub hc
    have hF1 : ∑ i ∈ F, (W i - C i) ≤ w - c :=
      sum_le_hasSum F (fun i _ => sub_nonneg.2 (h1 i)) hdiff
    rw [Finset.sum_sub_distrib] at hF1
    have hr0 : 0 ≤ c - ∑ i ∈ F, C i := sub_nonneg.2 hF0
    have hr1 : c - ∑ i ∈ F, C i ≤ w - ∑ i ∈ F, W i := by linarith
    have hS0 : 0 ≤ ∑ i ∈ F, C i := Finset.sum_nonneg (fun i _ => h0 i)
    have hS1 : ∑ i ∈ F, C i ≤ ∑ i ∈ F, W i := Finset.sum_le_sum (fun i _ => h1 i)
    have hA : Vf c w ≤ Vf (∑ i ∈ F, C i) (∑ i ∈ F, W i) +
        Vf (c - ∑ i ∈ F, C i) (w - ∑ i ∈ F, W i) := by
      calc Vf c w = Vf (∑ i ∈ F, C i + (c - ∑ i ∈ F, C i)) (∑ i ∈ F, W i + (w - ∑ i ∈ F, W i)) := by
            congr 1 <;> ring
        _ ≤ _ := Vf_add _ _ _ _ hS0 hS1 hr0 hr1
    have hB := Vf_finset_sum F C W (fun i _ => h0 i) (fun i _ => h1 i)
    have hC := Vf_le _ _ hr0 hr1
    have hD : ∑ i ∈ F, Vf (C i) (W i) ≤ ∑' i, Vf (C i) (W i) :=
      Summable.sum_le_tsum F (fun i _ => Vf_nonneg _ _ (h0 i) (h1 i)) hs
    linarith
  have hc' : Tendsto (fun s : Finset ι => ∑ i ∈ s, C i) atTop (𝓝 c) := hc
  have hlim : Tendsto
      (fun s : Finset ι => ∑' i, Vf (C i) (W i) + (Real.pi / 8 + 1 / 4) * (c - ∑ i ∈ s, C i))
      atTop (𝓝 (∑' i, Vf (C i) (W i) + (Real.pi / 8 + 1 / 4) * (c - c))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub hc'))
  rw [sub_self, mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim key

end TheoremS.Inf
