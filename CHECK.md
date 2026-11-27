# Build checks

This file records builds of this repository from a fresh clone. Each section was written after its build, and the commit that adds or updates this file changes nothing else.

## Build 3: measurable outcome spaces

- Commit built: `b4d04536712a23cfb199273c019ed167ae79e0dc` (adds `TheoremS/Meas/`, the model with measurable outcome spaces and its proof).
- Where: a Slurm compute node (`rye-02`), job 2030656, 4 CPUs requested and 6 allocated (Slurm's share for the 24 GB memory request), 27 November 2026, 10:57:59 to 11:06:25 PST.
- Toolchain: elan installed fresh in the job folder, then `leanprover/lean4:v4.35.0` (Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux). Empty Lake and Mathlib caches at the start.
- Steps, each with exit code 0:
  1. `git clone` of a bundle of the commit above; `git rev-parse HEAD` matched it.
  2. `grep -rnE "sorry|admit|native_decide|^axiom|unsafe" TheoremS/` found nothing (this covers `TheoremS/Meas/`).
  3. `lake exe cache get`: 9,031 Mathlib files downloaded and unpacked.
  4. `lake build`: 9,067 jobs, completed successfully (301 s wall, peak memory 8.8 GB). The job log keeps only the last 40 lines of build output; the warnings in them are four `Try this` suggestions in `TheoremS/Meas/Joint.lean`, one deprecated lemma name and four `haveILetI` style-linter notes.
  5. `lake env lean checks/Axioms.lean`.

Output of the check file for the model with measurable outcome spaces (the output for the finite and countable models is the same as in Builds 1 and 2):

```
def TheoremS.Meas.TheoremSMeasGen : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : NormedAddCommGroup K] [inst_1 : InnerProductSpace ℂ K] [inst_2 : CompleteSpace K]
      [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [inst_4 : (m : ℕ) → MeasurableSpace (Ω m)]
      [∀ (m : ℕ), Nonempty (Ω m)] (A : Meas.Alg N K Ω) (ρ : Fin N → Meas.HistFam N K Ω),
      (∀ (x : Fin N), A.IsHistory x (ρ x)) →
        A.ZeroError ρ →
          ENNReal.ofReal (2 / Real.arcsin (2 / √↑N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / ↑N)) ≤ (∑ x, A.cost (ρ x)) / ↑N
def TheoremS.Meas.TheoremSMeasGen' : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : NormedAddCommGroup K] [inst_1 : InnerProductSpace ℂ K] [inst_2 : CompleteSpace K]
      [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [inst_4 : (m : ℕ) → MeasurableSpace (Ω m)]
      [∀ (m : ℕ), Nonempty (Ω m)] (A : Meas.Alg N K Ω) (ρ : Fin N → Meas.HistFam N K Ω),
      (∀ (x : Fin N), A.IsHistory x (ρ x)) →
        A.ZeroError ρ → ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * √↑N - 4 / √↑N) ≤ (∑ x, A.cost (ρ x)) / ↑N
def TheoremS.Meas.TheoremSMeas : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : NormedAddCommGroup K] [inst_1 : InnerProductSpace ℂ K] [inst_2 : CompleteSpace K]
      [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [inst_4 : (m : ℕ) → MeasurableSpace (Ω m)]
      [∀ (m : ℕ), StandardBorelSpace (Ω m)] [∀ (m : ℕ), Nonempty (Ω m)] (A : Meas.Alg N K Ω)
      (ρ : Fin N → Meas.HistFam N K Ω),
      (∀ (x : Fin N), A.IsHistory x (ρ x)) →
        A.ZeroError ρ →
          ENNReal.ofReal (2 / Real.arcsin (2 / √↑N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / ↑N)) ≤ (∑ x, A.cost (ρ x)) / ↑N
def TheoremS.Meas.TheoremSMeas' : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : NormedAddCommGroup K] [inst_1 : InnerProductSpace ℂ K] [inst_2 : CompleteSpace K]
      [TopologicalSpace.SeparableSpace K] (Ω : ℕ → Type) [inst_4 : (m : ℕ) → MeasurableSpace (Ω m)]
      [∀ (m : ℕ), StandardBorelSpace (Ω m)] [∀ (m : ℕ), Nonempty (Ω m)] (A : Meas.Alg N K Ω)
      (ρ : Fin N → Meas.HistFam N K Ω),
      (∀ (x : Fin N), A.IsHistory x (ρ x)) →
        A.ZeroError ρ → ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * √↑N - 4 / √↑N) ≤ (∑ x, A.cost (ρ x)) / ↑N
'TheoremS.Meas.theoremSMeasGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TheoremS.Meas.theoremSMeasGen'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TheoremS.Meas.theoremSMeas' depends on axioms: [propext, Classical.choice, Quot.sound]
'TheoremS.Meas.theoremSMeas'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TheoremS.Meas.historyExists' depends on axioms: [propext, Classical.choice, Quot.sound]
'TheoremS.Meas.historyUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The statement file `TheoremS/Meas/Statement.lean` was copied from the paper's working repository, where it was reviewed by an AI agent that had not seen the proof (verdict: faithful to the paper's model, no required changes). As in Builds 1 and 2, the module names and namespace were changed (`QC22.MeasS` to `TheoremS.Meas`), the comments and docstrings were rewritten without references to the working repository, and a licence header was added. No definition changed. With comments and docstrings removed, the whole difference between the reviewed file and `TheoremS/Meas/Statement.lean` is:

```
--- StageD/QC22MeasStatement.lean (code only)
+++ TheoremS/Meas/Statement.lean (code only)
@@ -2 +2 @@
-namespace QC22.MeasS
+namespace TheoremS.Meas
@@ -190 +190 @@
-end QC22.MeasS
+end TheoremS.Meas
```

Both files have 190 lines of code. SHA-256 of the reviewed file: `83b3a363a30c3dc9e909a6ef5ef4c9f9d6d58c8a4179f50f636d119ee12f676e`; of `TheoremS/Meas/Statement.lean`: `57525b4822f36bfadc5edd97a20886f7cece0e2b8b914bc18fedc70ed28c8bef`. The eight proof files under `TheoremS/Meas/` differ from the working copies in the same way (namespace, import lines, the leading comment and the header), plus `QC22.FinS.` changed to `TheoremS.` in `Bound.lean` and `QC22.MeasS.flip` changed to `TheoremS.Meas.flip` in `Cell.lean`.

## Build 2: the countable model

- Commit built: `57d12fae77a2e966b5e4027af7ea392e40af4b77` (adds `TheoremS/Inf/`, the countable model and its proof).
- Where: a Slurm compute node (`barley-03`), job 2027944, 8 CPUs, 26 November 2026, 16:29:04 to 16:35:55 PST.
- Toolchain: elan installed fresh in the job folder, then `leanprover/lean4:v4.35.0` (Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux). Empty Lake and Mathlib caches at the start.
- Steps, each with exit code 0:
  1. `git clone` of a bundle of the commit above; `git rev-parse HEAD` matched it.
  2. `grep -rnE "sorry|admit|native_decide|^axiom|unsafe" TheoremS/` found nothing (this covers `TheoremS/Inf/`).
  3. `lake exe cache get`: 9,031 Mathlib files downloaded and unpacked.
  4. `lake build`: 9,058 jobs, the ten `TheoremS` modules compiled from source (173 s wall, peak memory 7.5 GB). The job log keeps only the last 40 lines of build output; the warnings in them are the ones of Build 1, all in `TheoremS/Potential.lean`.
  5. `lake env lean checks/Axioms.lean`.

Output of the check file for the countable model (the output for `TheoremSFin`, `TheoremSFin'` is the same as in Build 1):

```
def TheoremS.Inf.TheoremSInf : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : NormedAddCommGroup K] [inst_1 : InnerProductSpace ℂ K] [inst_2 : CompleteSpace K]
      [TopologicalSpace.SeparableSpace K] (A : Inf.Alg N K),
      A.ZeroError →
        ENNReal.ofReal (2 / Real.arcsin (2 / √↑N) * (Real.pi / 8 + 1 / 4) * (1 - 2 / ↑N)) ≤ (∑ x, A.cost x) / ↑N
def TheoremS.Inf.TheoremSInf' : Prop :=
∀ (N : ℕ),
  4 ≤ N →
    ∀ (K : Type) [inst : NormedAddCommGroup K] [inst_1 : InnerProductSpace ℂ K] [inst_2 : CompleteSpace K]
      [TopologicalSpace.SeparableSpace K] (A : Inf.Alg N K),
      A.ZeroError → ENNReal.ofReal ((Real.pi / 8 + 1 / 4) * √↑N - 4 / √↑N) ≤ (∑ x, A.cost x) / ↑N
'TheoremS.Inf.theoremSInf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TheoremS.Inf.theoremSInf'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The statement file `TheoremS/Inf/Statement.lean` was copied from the paper's working repository, where it was reviewed by an AI agent that had not seen the proof (verdict: faithful to the paper's model). As in Build 1, the module names and namespace were changed (`QC22.InfS` to `TheoremS.Inf`), the comments were rewritten and a licence header was added. No definition changed. With the leading comment block removed, the whole difference between the reviewed file and `TheoremS/Inf/Statement.lean` is:

```
-namespace QC22.InfS
+namespace TheoremS.Inf
-end QC22.InfS
+end TheoremS.Inf
```

SHA-256 of the reviewed file: `d4e4e19d6b319dbd4696c4e5ba46849e0ab1fa67a7fbc099d1b8cbfe867897f8`; of `TheoremS/Inf/Statement.lean`: `aab40c674c7de5a055549d37a0761820492910940758173cbe7a0aeac39e3d8a`. The four proof files under `TheoremS/Inf/` differ from the working copies in the same way (namespace, import lines, the leading comment and the header), plus `open QC22.FinS` changed to `open TheoremS` and two comments that named a working file.

## Build 1: the finite model

- Commit built: `9750267dcb04ce80d03eaf9001b4d0eba2d6ee53` (the parent of `581ccba`, the commit that first added this file).
- Where: a Slurm compute node (`barley-04`), job 2027805, 8 CPUs, 26 November 2026, 15:17:17 to 15:20:54 PST.
- Toolchain: elan installed fresh in the job folder, then `leanprover/lean4:v4.35.0` (Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux). Empty Lake and Mathlib caches at the start.
- Steps, each with exit code 0:
  1. `git clone` of a bundle of the commit above; `git rev-parse HEAD` matched it.
  2. `grep -rnE "sorry|admit|native_decide|^axiom|unsafe" TheoremS/` found nothing.
  3. `lake exe cache get`: 9,031 Mathlib files downloaded and unpacked (2 min 7 s).
  4. `lake build`: 9,053 jobs, the five `TheoremS` modules compiled from source (69 s wall, peak memory 7.2 GB). Warnings only: two deprecated lemma names (`if_neg`, `if_pos`), two uses of the deprecated `push_neg`, and two `unnecessarySeqFocus` linter notes, all in `TheoremS/Potential.lean`.
  5. `lake env lean checks/Axioms.lean`.

### Output of the check file

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

### The statement file and the reviewed statement

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
