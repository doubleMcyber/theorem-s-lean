# Build check

This file records one build of this repository from a fresh clone. It was written after that build and is the only file added since the commit that was built.

## The build

- Commit built: `9750267dcb04ce80d03eaf9001b4d0eba2d6ee53` (the parent of the commit that adds this file).
- Where: a Slurm compute node (`barley-04`), job 2027805, 8 CPUs, 26 November 2026, 15:17:17 to 15:20:54 PST.
- Toolchain: elan installed fresh in the job folder, then `leanprover/lean4:v4.35.0` (Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux). Empty Lake and Mathlib caches at the start.
- Steps, each with exit code 0:
  1. `git clone` of a bundle of the commit above; `git rev-parse HEAD` matched it.
  2. `grep -rnE "sorry|admit|native_decide|^axiom|unsafe" TheoremS/` found nothing.
  3. `lake exe cache get`: 9,031 Mathlib files downloaded and unpacked (2 min 7 s).
  4. `lake build`: 9,053 jobs, the five `TheoremS` modules compiled from source (69 s wall, peak memory 7.2 GB). Warnings only: two deprecated lemma names (`if_neg`, `if_pos`), two uses of the deprecated `push_neg`, and two `unnecessarySeqFocus` linter notes, all in `TheoremS/Potential.lean`.
  5. `lake env lean checks/Axioms.lean`.

## Output of the check file

```
def TheoremS.TheoremSFin : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : Fintype K] (A : Alg N K),
      A.ZeroError →
        ENNReal.ofReal (2 / Real.arcsin (2 / √↑N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / ↑N)) ≤ (∑ x, A.cost x) / ↑N
def TheoremS.TheoremSFin' : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : Fintype K] (A : Alg N K),
      A.ZeroError → ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * √↑N - 4 / √↑N) ≤ (∑ x, A.cost x) / ↑N
'TheoremS.theoremSFin' depends on axioms: [propext, Classical.choice, Quot.sound]
'TheoremS.theoremSFin'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## The statement file and the reviewed statement

The files here were copied from the paper's working repository, where the statement file was reviewed by an AI agent that had not seen the proof (verdict: faithful to the paper's model restricted to a finite workspace and finitely many outcomes, no required changes). For publication the module names and namespace were changed (`QC22.FinS` to `TheoremS`), the comments and docstrings were rewritten without references to the working repository, and a licence header was added. No definition changed. With comments and docstrings removed, the whole difference between the reviewed file and `TheoremS/Statement.lean` is:

```
--- StageB/QC22FinStatement.lean (code only)
+++ TheoremS/Statement.lean (code only)
@@ -2 +2 @@
-namespace QC22.FinS
+namespace TheoremS
@@ -57 +57 @@
-end QC22.FinS
+end TheoremS
```

Both files have 57 lines of code. SHA-256 of the reviewed file: `3009b286f1f5b83a559385f4c8143d3e2ff06e5364341dc8cb2e62357c8c3885`; of `TheoremS/Statement.lean`: `7472feca9fb5896576f438b29e4ac88fa7973a0ff4dcb03a9684f340b08c5302`. The other four files differ from the working copies in the same way: namespace, import lines, comments and the header.
