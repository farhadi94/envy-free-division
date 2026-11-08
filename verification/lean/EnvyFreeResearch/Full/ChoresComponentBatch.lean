import EnvyFreeResearch.Full.ChoresComponentDonors
import EnvyFreeResearch.Full.ChoresComponentFrames
import EnvyFreeResearch.Full.ChoresComponentAssignment

/-! The actual finite donor list for one reserved component-cycle group. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentBatch
open Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)

abbrev Task := state.partition.tasks (state.selected hall cycle)

abbrev Result := Recorded (ClippedRecord n) (Task state hall cycle) Root n

def donorRoot (out : Result state hall cycle) (j : Fin n) : Root :=
  if hj : j ∈ Task state hall cycle then out.allocation.assigned ⟨j, hj⟩
  else Classical.choice (inferInstance : Nonempty Root)

def utilities (gap : Root → Fin n → Fin n → ℝ) (out : Result state hall cycle)
    (i j : Fin n) : ℝ :=
  if hj : j ∈ Task state hall cycle then
    utility Subtype.val state.partition.representative gap out i ⟨j, hj⟩ else 0

def owners (out : Result state hall cycle) (j : Fin n) : Equiv.Perm (Fin n) :=
  if hj : j ∈ Task state hall cycle then owner state visited Subtype.val out ⟨j, hj⟩ else 1

def donations (packages : Root → Package (Fin n) RootId)
    (frames : Root → Frame (Fin n) RootId) (gap : Root → Fin n → Fin n → ℝ)
    (out : Result state hall cycle) : List (Donation (Fin n) RootId) :=
  ordinaryTasks (Task state hall cycle) (packages ∘ donorRoot state hall cycle out)
    (frames ∘ donorRoot state hall cycle out) state.partition.representative
    (owners state hall cycle visited out) (utilities state hall cycle gap out)

@[simp] theorem donorRoot_task (out : Result state hall cycle) (j : Task state hall cycle) :
    donorRoot state hall cycle out j = out.allocation.assigned j := by
  simp [donorRoot, j.property]

@[simp] theorem utilities_task (gap : Root → Fin n → Fin n → ℝ) (out : Result state hall cycle)
    (i : Fin n) (j : Task state hall cycle) :
    utilities state hall cycle gap out i j =
      utility Subtype.val state.partition.representative gap out i j := by
  simp [utilities, j.property]

@[simp] theorem owners_task (out : Result state hall cycle) (j : Task state hall cycle) :
    owners state hall cycle visited out j = owner state visited Subtype.val out j := by
  simp [owners, j.property]

variable (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ) (out : Result state hall cycle)

theorem donations_wellFormed (hlive : ∀ s, (packages s).live = some (frames s))
    (hframes : ∀ s, (frames s).Good)
    (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i) :
    ∀ d ∈ donations state hall cycle visited packages frames gap out, d.WellFormed := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
  have hj' : j ∈ Task state hall cycle := Finset.mem_toList.mp hj
  let task : Task state hall cycle := ⟨j, hj'⟩
  have hgood := ComponentDonors.ordinary_good state visited frames Subtype.val gap out task
    hframes hallowed
  constructor
  · exact hlive _
  · simpa only [Function.comp_apply, donorRoot, utilities, owners, dite_eq_left hj',
      ComponentDonors.ordinary] using hgood

theorem donations_packages_valid (hvalid : ∀ s, (packages s).Valid) :
    ∀ d ∈ donations state hall cycle visited packages frames gap out, d.package.Valid := by
  intro d hd
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hd
  exact hvalid _

theorem payments_at_label (p i : Fin n) :
    payments (donations state hall cycle visited packages frames gap out) i p =
      if i ∈ (Task state hall cycle).filter (fun j => state.partition.representative j = p)
      then EnvyFreeResearch.R7Chores.retainedCredit (utilities state hall cycle gap out) i else 0 :=
  ordinary_tasks_payments _ _ _ _ _ _ _ _

theorem extras_at_label (p i j : Fin n) :
    extras (donations state hall cycle visited packages frames gap out) i j p =
      EnvyFreeResearch.R7Chores.batchLoss
        ((Task state hall cycle).filter (fun j => state.partition.representative j = p))
        (utilities state hall cycle gap out) i j := ordinary_tasks_extras _ _ _ _ _ _ _ _ _

theorem selected_payments (p i : Fin n) (hp : p ∈ state.selected hall cycle) :
    payments (donations state hall cycle visited packages frames gap out) i p =
      if i ∈ state.partition.component p then
        EnvyFreeResearch.R7Chores.retainedCredit (utilities state hall cycle gap out) i else 0 := by
  rw [payments_at_label, state.partition.tasks_at_label _ p hp]

theorem selected_extras (p i j : Fin n) (hp : p ∈ state.selected hall cycle) :
    extras (donations state hall cycle visited packages frames gap out) i j p =
      EnvyFreeResearch.R7Chores.batchLoss (state.partition.component p)
        (utilities state hall cycle gap out) i j := by
  rw [extras_at_label, state.partition.tasks_at_label _ p hp]

theorem other_payments (p i : Fin n) (hp : p ∉ state.selected hall cycle) :
    payments (donations state hall cycle visited packages frames gap out) i p = 0 := by
  rw [payments_at_label, state.partition.tasks_at_other_label _ p hp]
  simp

theorem other_extras (p i j : Fin n) (hp : p ∉ state.selected hall cycle) :
    extras (donations state hall cycle visited packages frames gap out) i j p = 0 := by
  rw [extras_at_label, state.partition.tasks_at_other_label _ p hp]
  simp [EnvyFreeResearch.R7Chores.batchLoss]

end EnvyFreeResearch.Full.Chores.ComponentBatch
