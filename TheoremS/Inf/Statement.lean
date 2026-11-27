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
The statement of Theorem S for the countable model: a separable workspace of any dimension and countably
many outcomes per node.

This file imports only Mathlib and proves nothing about algorithms: it defines the model and the claims.
The proof is in `TheoremS/Inf/Bound.lean`. It is the counterpart of `TheoremS/Statement.lean` (finite
workspace, finitely many outcomes), which it extends in two ways: the workspace is any separable complex
Hilbert space, and an operation node may have countably many outcomes. This is the paper's definition of
an adaptive query algorithm (Section "The single-item theorem in the standard query model").

* Workspace: a separable complex Hilbert space `K` (finite or infinite dimensional).
* State space `H = ℂ^N ⊗ ℂ^2 ⊗ K` (address, marker bit, workspace). Since `ℂ^N ⊗ ℂ^2` is finite
  dimensional, `H` is the ℓ² direct sum of `2N` copies of `K`, one for each basis label `(y, b)`; it is
  written `PiLp 2 (fun _ : Fin N × Bool => K)`. A vector `ψ : H` is the function `(y, b) ↦ ψ (y, b) ∈ K`,
  i.e. `ψ = ∑_{y,b} |y, b⟩ ⊗ ψ (y, b)`.
* The bit oracle for the marked item `x`: `O_x |y, b⟩ ⊗ w = |y, b xor [y = x]⟩ ⊗ w`, i.e.
  `(O_x ψ) (y, b) = ψ (y, b xor [y = x])`, the unitary that permutes the `2N` summands by `flip x`.
* A rooted tree of classical control, given by the kind of the node reached after each finite history of
  outcomes (a `List ℕ`, newest outcome first). A node is a query node (one child, outcome `0`), an
  operation node (a set `J ⊆ ℕ` of outcomes, finite or countably infinite, and bounded operators `A j` on
  `H` with `∑_{j ∈ J} A_j† A_j = I` in the strong operator topology, the sum taken unordered; child `j` for
  each `j ∈ J`), or a halt node (a leaf with an output in `Fin N`). The tree and the operators do not
  depend on the marked item. Paths may be infinite. Every countable outcome set can be labelled by a
  subset of `ℕ`, so `J : Set ℕ` loses nothing.
* Branch vectors: `ψ_x [] = ψ₀`, `ψ_x (j :: h) = O_x ψ_x h` below a query node (for `j = 0`),
  `= A_j ψ_x h` below an operation node (for `j ∈ J`), and `0` for every history that is not in the tree.
* `p_x h = ‖ψ_x h‖²`; cost `T_x = ∑_{query nodes h} p_x h ∈ [0, ∞]`; success
  `s_x = ∑_{halt nodes h with output x} p_x h`; zero error means `s_x = 1` for every `x`.
  These are the definitions of `TheoremS/Statement.lean`, word for word.

Claims (`TheoremSInf`, `TheoremSInf'`): the two bounds of `TheoremSFin`, `TheoremSFin'` for this model.
As there, the bound of `TheoremSInf'` is negative for `N ∈ {4, 5, 6}`, where `ENNReal.ofReal` clips it to 0.

`K : Type` (universe 0) loses nothing: every separable complex Hilbert space is unitarily isomorphic to `ℂ^n`
or to `ℓ²(ℕ)`, both in `Type`, and cost and success are invariant under a unitary change of workspace.
The proof does not use separability.

Scope: instruments with an arbitrary measurable outcome space, which the paper also treats, are outside
this statement. One independent statement review (by an AI agent that had not seen the proof) judged
this file faithful to the paper's definition.
-/
import Mathlib

namespace TheoremS.Inf

set_option autoImplicit false

open scoped ENNReal

/-- Basis labels of `ℂ^N ⊗ ℂ^2`: address and marker bit. -/
abbrev Idx (N : ℕ) := Fin N × Bool

/-- The state space `H = ℂ^N ⊗ ℂ^2 ⊗ K`, as the ℓ² sum of `2N` copies of the workspace `K`. -/
abbrev H (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Idx N => K)

/-- The basis map of the bit oracle for the marked item `x`: `(y, b) ↦ (y, b xor [y = x])`. -/
def flip {N : ℕ} (x : Fin N) (i : Idx N) : Idx N :=
  (i.1, xor i.2 (decide (i.1 = x)))

/-- `flip x` as a permutation of the basis labels (it is an involution). -/
def flipEquiv {N : ℕ} (x : Fin N) : Idx N ≃ Idx N where
  toFun := flip x
  invFun := flip x
  left_inv := fun i => by rcases i with ⟨y, b⟩; by_cases h : y = x <;> simp [flip, h]
  right_inv := fun i => by rcases i with ⟨y, b⟩; by_cases h : y = x <;> simp [flip, h]

/-- The bit oracle `O_x`, the unitary on `H` that permutes the `2N` summands by `flip x`:
`(O_x ψ) i = ψ ((flip x).symm i) = ψ (flip x i)`. -/
noncomputable def oracle {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x : Fin N) : H N K ≃ₗᵢ[ℂ] H N K :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (flipEquiv x)

section Model

variable (N : ℕ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The kind of a node of the classical control tree. -/
inductive Node where
  /-- A query node: apply the oracle. Its only child is outcome `0`. -/
  | query : Node
  /-- An operation node: an instrument with outcomes `j ∈ J` (a finite or countably infinite set of
  labels) and bounded Kraus operators `A j` (the values `A j` for `j ∉ J` are never used). -/
  | op (J : Set ℕ) (A : ℕ → H N K →L[ℂ] H N K) : Node
  /-- A halt node (a leaf) with an output. -/
  | halt (out : Fin N) : Node

/-- An adaptive query algorithm on `ℂ^N ⊗ ℂ^2 ⊗ K`. `node h` is the kind of the node reached by the
history `h` (newest outcome first). Neither `psi0` nor the tree depends on the marked item. -/
structure Alg where
  /-- The initial state. -/
  psi0 : H N K
  norm_psi0 : ‖psi0‖ = 1
  /-- The node reached by each history. -/
  node : List ℕ → Node N K
  /-- Every operation node carries a complete family of Kraus operators:
  `∑_{j ∈ J} A_j† A_j = I` in the strong operator topology, i.e. for every vector `ψ` the unordered sum
  `∑_{j ∈ J} A_j† A_j ψ` converges to `ψ`. For positive operators the unordered strong limit, the ordered
  strong limit in any enumeration of `J`, and `∑_j ‖A_j ψ‖² = ‖ψ‖²` for every `ψ` are equivalent, so taking
  the sum unordered is not a restriction. This is also required at histories outside the tree, which
  loses nothing (set those nodes to `.query`). -/
  complete : ∀ h J A, node h = .op J A →
    ∀ ψ : H N K, HasSum (fun j : J => ContinuousLinearMap.adjoint (A j) (A j ψ)) ψ

end Model

namespace Node

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `true` exactly at query nodes. -/
def isQuery : Node N K → Bool
  | .query => true
  | _ => false

/-- The output of a halt node, `none` at other nodes. -/
def output : Node N K → Option (Fin N)
  | .halt y => some y
  | _ => none

end Node

namespace Alg

variable {N : ℕ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open Classical in
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

/-- Theorem S for the countable model: for `N ≥ 4`, every zero-error adaptive query algorithm with a
separable workspace and countably many outcomes per node has average cost at least
`(2 / arcsin (2/√N)) (π/8 + 1/4) (1 - 2/N)`. -/
def TheoremSInf : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (A : Alg N K), A.ZeroError →
    ENNReal.ofReal (2 / Real.arcsin (2 / Real.sqrt N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / (N : ℝ)))
      ≤ (∑ x, A.cost x) / (N : ℝ≥0∞)

/-- The same with the explicit form `(π/8 + 1/4)√N - 4/√N` of the paper's Theorem S. -/
def TheoremSInf' : Prop :=
  ∀ (N : ℕ), 4 ≤ N → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (A : Alg N K), A.ZeroError →
    ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * Real.sqrt N - 4 / Real.sqrt N)
      ≤ (∑ x, A.cost x) / (N : ℝ≥0∞)

end TheoremS.Inf
