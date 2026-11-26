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
The statement of Theorem S for finite-dimensional adaptive query algorithms.

This file imports only Mathlib and proves nothing about algorithms: it defines the model and the claim.
The proof is in `TheoremS/Bound.lean`.

The model is the paper's definition of an adaptive query algorithm (Section "The single-item theorem in
the standard query model") with a finite workspace and finitely many outcomes per node:

* State space `H = ℂ^N ⊗ ℂ^2 ⊗ ℂ^K` (address, marker bit, workspace), written as
  `EuclideanSpace ℂ (Fin N × Bool × K)` for a finite type `K` of workspace labels.
* The bit oracle for the marked item `x` is the unitary `O_x |y, b, w⟩ = |y, b xor [y = x], w⟩`.
* A rooted tree of classical control, given by the kind of the node reached after each finite history of
  outcomes (a `List ℕ`, newest outcome first). A node is a query node (one child, outcome `0`), an operation
  node (a finite outcome set `J` and Kraus operators `A j` with `∑_{j ∈ J} A_j† A_j = I`; child `j` for
  each `j ∈ J`), or a halt node (a leaf with an output in `Fin N`). The tree and the operators do not depend
  on the marked item. Paths may be infinite.
* Branch vectors: `ψ_x [] = ψ₀`, `ψ_x (j :: h) = O_x ψ_x h` below a query node (for `j = 0`),
  `= A_j ψ_x h` below an operation node (for `j ∈ J`), and `0` for every history that is not in the tree.
* `p_x h = ‖ψ_x h‖²`; cost `T_x = ∑_{query nodes h} p_x h ∈ [0, ∞]` (expected number of queries, each
  query counted with the probability that it is made); success `s_x = ∑_{halt nodes h with output x} p_x h`;
  zero error means `s_x = 1` for every `x`.

Claim (`TheoremSFin`): for `N ≥ 4` the average cost `(1/N) ∑_x T_x` is at least
`(2 / arcsin (2/√N)) · (π/8 + 1/4) · (1 - 2/N)`, and (`TheoremSFin'`) at least `(π/8 + 1/4)√N - 4/√N`.
The real bound of `TheoremSFin'` is negative for `N ∈ {4, 5, 6}`, where `ENNReal.ofReal` clips it to 0 and
the claim is vacuous (as the paper's second bound is). The worst case `max_x T_x` satisfies the same bounds
because `(∑ x, T_x) / N ≤ max_x T_x`; that corollary is not stated here.

Scope: infinite-dimensional workspaces and countably infinite outcome sets, which the paper allows, are
outside this statement; the paper reduces them to this case by a paper proof. One independent statement
review (by an AI agent that had not seen the proof) judged this file faithful to the paper's definition
restricted to finite workspaces and finitely many outcomes.
-/
import Mathlib

namespace TheoremS

set_option autoImplicit false

open scoped ENNReal

/-- Basis labels of `ℂ^N ⊗ ℂ^2 ⊗ ℂ^K`: address, marker bit, workspace label. -/
abbrev Idx (N : ℕ) (K : Type) := Fin N × Bool × K

/-- The state space `H = ℂ^N ⊗ ℂ^2 ⊗ ℂ^K`; finite dimensional because `K` is finite. -/
abbrev H (N : ℕ) (K : Type) [Fintype K] := EuclideanSpace ℂ (Idx N K)

/-- The basis map of the bit oracle for the marked item `x`: `(y, b, w) ↦ (y, b xor [y = x], w)`. -/
def flip {N : ℕ} {K : Type} (x : Fin N) (i : Idx N K) : Idx N K :=
  (i.1, xor i.2.1 (decide (i.1 = x)), i.2.2)

/-- `flip x` as a permutation of the basis labels (it is an involution). -/
def flipEquiv {N : ℕ} {K : Type} (x : Fin N) : Idx N K ≃ Idx N K where
  toFun := flip x
  invFun := flip x
  left_inv := fun i => by rcases i with ⟨y, b, w⟩; by_cases h : y = x <;> simp [flip, h]
  right_inv := fun i => by rcases i with ⟨y, b, w⟩; by_cases h : y = x <;> simp [flip, h]

/-- The bit oracle `O_x`, the unitary on `H` that permutes the basis by `flip x`. -/
noncomputable def oracle {N : ℕ} {K : Type} [Fintype K] (x : Fin N) : H N K ≃ₗᵢ[ℂ] H N K :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (flipEquiv x)

/-- The kind of a node of the classical control tree. -/
inductive Node (N : ℕ) (K : Type) [Fintype K] where
  /-- A query node: apply the oracle. Its only child is outcome `0`. -/
  | query : Node N K
  /-- An operation node: an instrument with finitely many outcomes `j ∈ J` and Kraus operators `A j`
  (the values `A j` for `j ∉ J` are never used). -/
  | op (J : Finset ℕ) (A : ℕ → H N K →ₗ[ℂ] H N K) : Node N K
  /-- A halt node (a leaf) with an output. -/
  | halt (out : Fin N) : Node N K

/-- `true` exactly at query nodes. -/
def Node.isQuery {N : ℕ} {K : Type} [Fintype K] : Node N K → Bool
  | .query => true
  | _ => false

/-- The output of a halt node, `none` at other nodes. -/
def Node.output {N : ℕ} {K : Type} [Fintype K] : Node N K → Option (Fin N)
  | .halt y => some y
  | _ => none

/-- An adaptive query algorithm on `ℂ^N ⊗ ℂ^2 ⊗ ℂ^K`. `node h` is the kind of the node reached by the
history `h` (newest outcome first). Neither `psi0` nor the tree depends on the marked item. -/
structure Alg (N : ℕ) (K : Type) [Fintype K] where
  /-- The initial state. -/
  psi0 : H N K
  norm_psi0 : ‖psi0‖ = 1
  /-- The node reached by each history. -/
  node : List ℕ → Node N K
  /-- Every operation node carries a complete family of Kraus operators: `∑_{j ∈ J} A_j† A_j = I`.
  This is also required at histories outside the tree, which loses nothing (set those nodes to `.query`). -/
  complete : ∀ h J A, node h = .op J A → ∑ j ∈ J, LinearMap.adjoint (A j) ∘ₗ A j = LinearMap.id

namespace Alg

variable {N : ℕ} {K : Type} [Fintype K]

/-- The unnormalised branch vector `ψ_x h` of history `h` when the marked item is `x`. -/
noncomputable def branch (A : Alg N K) (x : Fin N) : List ℕ → H N K
  | [] => A.psi0
  | j :: h =>
    match A.node h with
    | .query => if j = 0 then oracle x (A.branch x h) else 0
    | .op J B => if j ∈ J then B j (A.branch x h) else 0
    | .halt _ => 0

/-- `p_x h = ‖ψ_x h‖²`, the probability that the run with marked item `x` passes through `h`. -/
noncomputable def prob (A : Alg N K) (x : Fin N) (h : List ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖A.branch x h‖ ^ 2)

/-- The cost `T_x`: the expected number of queries, `∑` of `p_x h` over the query nodes `h`. -/
noncomputable def cost (A : Alg N K) (x : Fin N) : ℝ≥0∞ :=
  ∑' h : List ℕ, if (A.node h).isQuery then A.prob x h else 0

/-- The success probability `s_x`: `∑` of `p_x h` over the halt nodes `h` with output `x`. -/
noncomputable def success (A : Alg N K) (x : Fin N) : ℝ≥0∞ :=
  ∑' h : List ℕ, if (A.node h).output = some x then A.prob x h else 0

/-- Zero error: the algorithm outputs the marked item with probability one, for every marked item. -/
def ZeroError (A : Alg N K) : Prop :=
  ∀ x, A.success x = 1

end Alg

/-- Theorem S, finite-dimensional form: for `N ≥ 4`, every zero-error adaptive query algorithm with a
finite workspace and finitely many outcomes per node has average cost at least
`(2 / arcsin (2/√N)) (π/8 + 1/4) (1 - 2/N)`. -/
def TheoremSFin : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [Fintype K] (A : Alg N K), A.ZeroError →
    ENNReal.ofReal (2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / (N : ℝ)))
      ≤ (∑ x, A.cost x) / (N : ℝ≥0∞)

/-- The same with the explicit form `(π/8 + 1/4)√N - 4/√N` of the paper's Theorem S. -/
def TheoremSFin' : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [Fintype K] (A : Alg N K), A.ZeroError →
    ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * Real.sqrt N - 4 / Real.sqrt N)
      ≤ (∑ x, A.cost x) / (N : ℝ≥0∞)

end TheoremS
