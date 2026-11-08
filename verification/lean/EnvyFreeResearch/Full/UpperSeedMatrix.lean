import EnvyFreeResearch.Full.UpperAssignment
import EnvyFreeResearch.Full.UpperThresholdProduct

/-!
# Actual seed matrices on the independent threshold tape

Each job supplies a literal threshold-selected witness family to one column.
The row difference of that job is the separated seed score. Deleting its
column removes the job from every deleted-column optimization, so the forced
score difference on a coordinate fiber is a fixed offset plus that score.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperSeedMatrix

open UpperSeeds UpperSeedProbability UpperAssignment UpperThresholdProduct

structure SeedSystem (Agent : Type*) (M L : ℕ) where
  left : Fin (M + 1) → Agent
  right : Fin (M + 1) → Agent
  column : Fin (M + 1) → Agent
  weight : Fin (M + 1) → Fin L → Agent → ℝ

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent] {M L : ℕ}

def difference (S : SeedSystem Agent M L) (job : Fin (M + 1)) (a : Fin L) : ℝ :=
  S.weight job a (S.left job) - S.weight job a (S.right job)

def rowSeed (S : SeedSystem Agent M L) (job : Fin (M + 1))
    (row : Agent) (threshold : Fin (L + 1)) : ℝ :=
  ∑ a, if kept (difference S job) threshold a then S.weight job a row else 0

def contribution (S : SeedSystem Agent M L) (draw : Fin (M + 1) → Fin (L + 1))
    (row column : Agent) (job : Fin (M + 1)) : ℝ :=
  if S.column job = column then rowSeed S job row (draw job) else 0

def matrix (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) (row column : Agent) : ℝ :=
  old row column + ∑ job, contribution S draw row column job

omit [Fintype Agent] [DecidableEq Agent] in
theorem rowSeed_difference (S : SeedSystem Agent M L) (job : Fin (M + 1))
    (threshold : Fin (L + 1)) :
    rowSeed S job (S.left job) threshold - rowSeed S job (S.right job) threshold =
      value (difference S job) threshold := by
  simp only [rowSeed, ← Finset.sum_sub_distrib, value]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp [difference]

theorem insertNth_other (job other : Fin (M + 1)) (hother : other ≠ job)
    (t u : Fin (L + 1)) (rest : Fin M → Fin (L + 1)) :
    Fin.insertNth (α := fun _ => Fin (L + 1)) job t rest other =
      Fin.insertNth (α := fun _ => Fin (L + 1)) job u rest other := by
  rcases Fin.eq_self_or_eq_succAbove job other with h | ⟨j, rfl⟩
  · exact False.elim (hother h)
  · simp

omit [Fintype Agent] in
theorem contribution_other (S : SeedSystem Agent M L) (job other : Fin (M + 1))
    (hother : other ≠ job) (t u : Fin (L + 1)) (rest : Fin M → Fin (L + 1))
    (row column : Agent) :
    contribution S (Fin.insertNth job t rest) row column other =
      contribution S (Fin.insertNth job u rest) row column other := by
  simp only [contribution, insertNth_other job other hother t u rest]

/-- Changing a seed threshold changes entries in its own column only. -/
theorem matrix_outside_column (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (t u : Fin (L + 1)) (rest : Fin M → Fin (L + 1))
    (row column : Agent) (hcolumn : column ≠ S.column job) :
    matrix S old (Fin.insertNth job t rest) row column =
      matrix S old (Fin.insertNth job u rest) row column := by
  unfold matrix
  congr 1
  apply Finset.sum_congr rfl
  intro other _
  by_cases hother : other = job
  · subst other
    simp [contribution, Ne.symm hcolumn]
  · exact contribution_other S job other hother t u rest row column

def otherRow (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (rest : Fin M → Fin (L + 1)) (row : Agent) : ℝ :=
  old row (S.column job) + ∑ other ∈ Finset.univ.erase job,
    contribution S (Fin.insertNth job 0 rest) row (S.column job) other

theorem matrix_at_column (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (t : Fin (L + 1)) (rest : Fin M → Fin (L + 1)) (row : Agent) :
    matrix S old (Fin.insertNth job t rest) row (S.column job) =
      otherRow S old job rest row + rowSeed S job row t := by
  have hsum : (∑ other ∈ Finset.univ.erase job,
      contribution S (Fin.insertNth job t rest) row (S.column job) other) =
      ∑ other ∈ Finset.univ.erase job,
        contribution S (Fin.insertNth job 0 rest) row (S.column job) other := by
    apply Finset.sum_congr rfl
    intro other hother
    exact contribution_other S job other (Finset.mem_erase.mp hother).1 t 0 rest row _
  have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (Fin (M + 1)))
    (contribution S (Fin.insertNth job t rest) row (S.column job)) (Finset.mem_univ job)
  rw [hsum] at hdecomp
  have hat : contribution S (Fin.insertNth job t rest) row (S.column job) job =
      rowSeed S job row t := by simp [contribution]
  rw [hat] at hdecomp
  dsimp only [matrix, otherRow]
  rw [← hdecomp]
  ring

def forcedDifference (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (draw : Fin (M + 1) → Fin (L + 1)) : ℝ :=
  forcedValue (matrix S old draw) (S.left job) (S.column job) -
    forcedValue (matrix S old draw) (S.right job) (S.column job)

def fiberOffset (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (rest : Fin M → Fin (L + 1)) : ℝ :=
  otherRow S old job rest (S.left job) - otherRow S old job rest (S.right job) +
    deletedValue (matrix S old (Fin.insertNth job 0 rest)) (S.left job) (S.column job) -
      deletedValue (matrix S old (Fin.insertNth job 0 rest)) (S.right job) (S.column job)

/-- The fixed offset is derived from the concrete matrix and actual
deleted-column maximizers. It is not an independent affine-score assumption. -/
theorem forcedDifference_fiber (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (rest : Fin M → Fin (L + 1)) (t : Fin (L + 1)) :
    forcedDifference S old job (Fin.insertNth job t rest) =
      fiberOffset S old job rest + value (difference S job) t := by
  have hdeleted (row : Agent) := deletedValue_column_independent
    (matrix S old (Fin.insertNth job t rest)) (matrix S old (Fin.insertNth job 0 rest))
    row (S.column job) (matrix_outside_column S old job t 0 rest)
  simp only [forcedDifference, forcedValue, matrix_at_column, hdeleted, fiberOffset]
  have hseed := rowSeed_difference S job t
  linarith

/-- The actual seed matrix has the full product-law truncated expectation
bound at every separated job, including arbitrary effects of all other jobs
on the optimizing assignment. -/
theorem matrix_charge_expectation (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (A lam a : ℝ) (hA : 0 < A) (hlam : 0 ≤ lam)
    (ha : 0 < a) (haone : a ≤ 1) (hgap : ∀ r, A / 3 ≤ |difference S job r|) :
    (∫ draw, max (charge A lam (forcedDifference S old job draw) - a) 0
      ∂tapeLaw (M + 1) L) ≤
      (12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ) :=
  product_truncated_charge_expectation job (difference S job) A lam a
    (forcedDifference S old job) (fiberOffset S old job) (forcedDifference_fiber S old job)
    hA hlam ha haone hgap

end EnvyFreeResearch.Full.UpperSeedMatrix
