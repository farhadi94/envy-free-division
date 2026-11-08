import EnvyFreeResearch.Full.UpperRepresentatives

/-!
# Actual optimal assignments and deleted-column scores

Every optimization below enumerates a fixed finite list and uses the first
maximizer. In particular the deleted-column value is proved independent of
all entries of the deleted column. No optimal-assignment event is used as a
conditioning hypothesis.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperAssignment

open UpperRepresentatives ProtocolMeasurable

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def score (V : Agent → Agent → ℝ) (assignment : Equiv.Perm Agent) : ℝ :=
  ∑ i, V i (assignment i)

def assignments : List (Equiv.Perm Agent) := Finset.univ.toList

theorem mem_assignments (assignment : Equiv.Perm Agent) :
    assignment ∈ assignments := by simp [assignments]

theorem assignments_nonempty : (assignments : List (Equiv.Perm Agent)) ≠ [] := by
  intro h
  have := mem_assignments (Equiv.refl Agent)
  simp [h] at this

/-- Finite exhaustive optimization, using the first maximizer on ties. -/
def maximize (V : Agent → Agent → ℝ) : Equiv.Perm Agent :=
  ((assignments : List (Equiv.Perm Agent)).argmax (score V)).getD (Equiv.refl Agent)

theorem maximize_spec (V : Agent → Agent → ℝ) (assignment : Equiv.Perm Agent) :
    score V assignment ≤ score V (maximize V) := by
  obtain ⟨best, hbest⟩ := argmax_exists (score V) assignments assignments_nonempty
  have h := List.le_of_mem_argmax (f := score V) (mem_assignments assignment)
    (show best ∈ assignments.argmax (score V) by simp [hbest])
  simpa [maximize, hbest] using h

def forcedAssignments (i j : Agent) : List (Equiv.Perm Agent) :=
  assignments.filter (fun assignment => assignment i = j)

theorem mem_forcedAssignments (i j : Agent) (assignment : Equiv.Perm Agent) :
    assignment ∈ forcedAssignments i j ↔ assignment i = j := by
  simp [forcedAssignments, mem_assignments]

theorem forcedAssignments_nonempty (i j : Agent) : forcedAssignments i j ≠ [] := by
  intro h
  have hmem := (mem_forcedAssignments i j (Equiv.swap i j)).mpr (by simp)
  simp [h] at hmem

def deletedScore (V : Agent → Agent → ℝ) (i : Agent)
    (assignment : Equiv.Perm Agent) : ℝ := ∑ r ∈ Finset.univ.erase i, V r (assignment r)

def deletedAssignment (V : Agent → Agent → ℝ) (i j : Agent) : Equiv.Perm Agent :=
  ((forcedAssignments i j).argmax (deletedScore V i)).getD (Equiv.swap i j)

def deletedValue (V : Agent → Agent → ℝ) (i j : Agent) : ℝ :=
  deletedScore V i (deletedAssignment V i j)

def forcedValue (V : Agent → Agent → ℝ) (i j : Agent) : ℝ :=
  V i j + deletedValue V i j

theorem deletedAssignment_spec (V : Agent → Agent → ℝ) (i j : Agent) :
    deletedAssignment V i j i = j ∧
      ∀ assignment : Equiv.Perm Agent, assignment i = j →
        deletedScore V i assignment ≤ deletedValue V i j := by
  obtain ⟨best, hbest⟩ := argmax_exists (deletedScore V i) (forcedAssignments i j)
    (forcedAssignments_nonempty i j)
  have hmem : best ∈ (forcedAssignments i j).argmax (deletedScore V i) := by simp [hbest]
  constructor
  · simpa [deletedAssignment, hbest] using
      (mem_forcedAssignments i j best).mp (List.argmax_mem hmem)
  · intro assignment hassignment
    have h := List.le_of_mem_argmax (f := deletedScore V i)
      ((mem_forcedAssignments i j assignment).mpr hassignment) hmem
    simpa [deletedValue, deletedAssignment, hbest] using h

theorem score_decomposition (V : Agent → Agent → ℝ) (i : Agent)
    (assignment : Equiv.Perm Agent) :
    score V assignment = V i (assignment i) + deletedScore V i assignment := by
  simp [score, deletedScore]

theorem forcedValue_eq_score (V : Agent → Agent → ℝ) (i j : Agent) :
    forcedValue V i j = score V (deletedAssignment V i j) := by
  rw [score_decomposition V i, (deletedAssignment_spec V i j).1]
  rfl

theorem forcedValue_le_optimum (V : Agent → Agent → ℝ) (i j : Agent) :
    forcedValue V i j ≤ score V (maximize V) := by
  rw [forcedValue_eq_score]
  exact maximize_spec V _

theorem score_le_forcedValue (V : Agent → Agent → ℝ) (i j : Agent)
    (assignment : Equiv.Perm Agent) (hassignment : assignment i = j) :
    score V assignment ≤ forcedValue V i j := by
  rw [score_decomposition V i assignment, hassignment]
  exact add_le_add le_rfl ((deletedAssignment_spec V i j).2 assignment hassignment)

theorem owner_forcedValue (V : Agent → Agent → ℝ) (owner : Agent) :
    forcedValue V owner (maximize V owner) = score V (maximize V) :=
  le_antisymm (forcedValue_le_optimum V _ _)
    (score_le_forcedValue V _ _ (maximize V) rfl)

/-- Any feasible reassignment of the owner's column bounds its forced-score
gap by the actual loss of that reassignment. This applies in particular to
each transferred column of a cycle competitor. -/
theorem forced_gap_le_loss (V : Agent → Agent → ℝ) (i owner : Agent)
    (competitor : Equiv.Perm Agent) (hcolumn : competitor i = maximize V owner) :
    |forcedValue V i (maximize V owner) - forcedValue V owner (maximize V owner)| ≤
      score V (maximize V) - score V competitor := by
  rw [owner_forcedValue, abs_of_nonpos (sub_nonpos.mpr (forcedValue_le_optimum V _ _))]
  have h := score_le_forcedValue V i (maximize V owner) competitor hcolumn
  linarith

/-- On a permutation forced to use column `j` at row `i`, deleting row `i`
removes every occurrence of column `j`. -/
theorem deletedScore_column_independent (V W : Agent → Agent → ℝ) (i j : Agent)
    (houtside : ∀ r c, c ≠ j → V r c = W r c)
    (assignment : Equiv.Perm Agent) (hassignment : assignment i = j) :
    deletedScore V i assignment = deletedScore W i assignment := by
  apply Finset.sum_congr rfl
  intro r hr
  apply houtside
  intro heq
  have hri := assignment.injective (heq.trans hassignment.symm)
  exact (Finset.mem_erase.mp hr).1 hri

/-- The value obtained by the actual deleted-column optimization is
independent of the entire deleted column, including any seed threshold in it. -/
theorem deletedValue_column_independent (V W : Agent → Agent → ℝ) (i j : Agent)
    (houtside : ∀ r c, c ≠ j → V r c = W r c) :
    deletedValue V i j = deletedValue W i j := by
  apply le_antisymm
  · rw [deletedValue, deletedScore_column_independent V W i j houtside
      (deletedAssignment V i j) (deletedAssignment_spec V i j).1]
    exact (deletedAssignment_spec W i j).2 _ (deletedAssignment_spec V i j).1
  · rw [deletedValue, deletedScore_column_independent W V i j
      (fun r c hc => (houtside r c hc).symm)
      (deletedAssignment W i j) (deletedAssignment_spec W i j).1]
    exact (deletedAssignment_spec V i j).2 _ (deletedAssignment_spec W i j).1

def minimize (V : Agent → Agent → ℝ) : Equiv.Perm Agent :=
  maximize (fun i j => -V i j)

omit [DecidableEq Agent] in
theorem score_neg (V : Agent → Agent → ℝ) (assignment : Equiv.Perm Agent) :
    score (fun i j => -V i j) assignment = -score V assignment := by
  simp [score]

theorem minimize_spec (V : Agent → Agent → ℝ) (assignment : Equiv.Perm Agent) :
    score V (minimize V) ≤ score V assignment := by
  have h := maximize_spec (fun i j => -V i j) assignment
  simpa only [score_neg, neg_le_neg_iff, minimize] using h

section Measurability

instance permutationMeasurableSpace : MeasurableSpace (Equiv.Perm Agent) := ⊤

instance permutationMeasurableSingletonClass : MeasurableSingletonClass (Equiv.Perm Agent) :=
  ⟨fun _ => trivial⟩

variable {X : Type*} [MeasurableSpace X]

omit [DecidableEq Agent] in
theorem score_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (assignment : Equiv.Perm Agent) :
    Measurable (fun x => score (V x) assignment) := by
  exact Finset.measurable_sum _ (fun i _ => hV i (assignment i))

theorem deletedScore_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (i : Agent) (assignment : Equiv.Perm Agent) :
    Measurable (fun x => deletedScore (V x) i assignment) := by
  exact Finset.measurable_sum _ (fun r _ => hV r (assignment r))

theorem maximize_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) :
    Measurable (fun x => maximize (V x)) := by
  have h := argmax_measurable assignments (fun x => score (V x)) (score_measurable V hV)
  exact measurable_option_cases (present := fun _ assignment => assignment)
    (absent := fun _ => Equiv.refl Agent) h measurable_snd measurable_const

theorem deletedAssignment_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (i j : Agent) :
    Measurable (fun x => deletedAssignment (V x) i j) := by
  have h := argmax_measurable (forcedAssignments i j) (fun x => deletedScore (V x) i)
    (deletedScore_measurable V hV i)
  exact measurable_option_cases (present := fun _ assignment => assignment)
    (absent := fun _ => Equiv.swap i j) h measurable_snd measurable_const

theorem deletedValue_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (i j : Agent) :
    Measurable (fun x => deletedValue (V x) i j) :=
  (score_eval_measurable (fun x => deletedScore (V x) i)
    (deletedScore_measurable V hV i)).comp
      (measurable_id.prodMk (deletedAssignment_measurable V hV i j))

theorem forcedValue_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (i j : Agent) :
    Measurable (fun x => forcedValue (V x) i j) :=
  (hV i j).add (deletedValue_measurable V hV i j)

theorem minimize_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) :
    Measurable (fun x => minimize (V x)) :=
  maximize_measurable (fun x i j => -V x i j) (fun i j => (hV i j).neg)

end Measurability

end EnvyFreeResearch.Full.UpperAssignment
