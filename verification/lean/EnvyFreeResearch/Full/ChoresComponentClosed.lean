import EnvyFreeResearch.Full.ChoresComponentAffineTables
import EnvyFreeResearch.Full.ChoresComponentPieceCache
import EnvyFreeResearch.Full.ChoresComponentAssignment

/-! Concrete closed affine donor batches. Nonnegative own values and every
deficit comparison come from the physical SubCore output; omitted observers
are protected by the original full-suffix bound. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentClosed
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle OrderedUnion
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (participants : Finset (Fin n)) (label : Fin n)

abbrev Result := Recorded (Record n) participants Root n

def donorRoot (out : Result (Root := Root) participants) (j : Fin n) : Root :=
  if hj : j ∈ participants then out.allocation.assigned ⟨j, hj⟩
  else Classical.choice (inferInstance : Nonempty Root)

def utilities (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) participants) (i j : Fin n) : ℝ :=
  if hj : j ∈ participants then
    utility Subtype.val state.partition.representative gap out i ⟨j, hj⟩ else 0

def owners (out : Result (Root := Root) participants) (j : Fin n) : Equiv.Perm (Fin n) :=
  if hj : j ∈ participants then owner state visited Subtype.val out ⟨j, hj⟩ else 1

def donations (packages : Root → Package (Fin n) RootId)
    (frames : Root → Frame (Fin n) RootId) (gap : Root → Fin n → Fin n → ℝ)
    (out : Result (Root := Root) participants) : List (Donation (Fin n) RootId) :=
  ComponentAffine.tasks participants (packages ∘ donorRoot participants out)
    (frames ∘ donorRoot participants out) label (owners state visited participants out)
    (utilities state participants gap out)

@[simp] theorem donorRoot_task (out : Result (Root := Root) participants) (j : participants) :
    donorRoot participants out j = out.allocation.assigned j := by
  simp [donorRoot, j.property]

@[simp] theorem utilities_task (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) participants)
    (i : Fin n) (j : participants) :
    utilities state participants gap out i j =
      utility Subtype.val state.partition.representative gap out i j := by
  simp [utilities, j.property]

variable (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) participants)
  (hlabel : ∀ j ∈ participants, state.partition.representative j = label)
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ)
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out)
  (hcorrect : PhysicalCorrect
    (affineUtility cost (domains blocks state.partition.representative)
      (offsets gap state.partition.representative)) Subtype.val out.allocation)

include hparts hcorrect

theorem own_nonnegative (i : Fin n) (hi : i ∈ participants) :
    0 ≤ utilities state participants gap out i i := by
  have h := affine_own_nonnegative cost blocks Subtype.val state.partition.representative gap
    out hparts hcorrect (⟨i, hi⟩ : participants)
  simpa only [utilities, dite_eq_left hi] using h

include hlabel in
theorem comparisons (i j : Fin n) (hi : i ∈ participants) (hj : j ∈ participants) :
    utilities state participants gap out i j ≤ utilities state participants gap out i i := by
  have h := affine_comparison cost blocks Subtype.val state.partition.representative gap out
    hparts hcorrect (⟨i, hi⟩ : participants) (⟨j, hj⟩ : participants)
    ((hlabel j hj).trans (hlabel i hi).symm)
  exact (le_max_right _ _).trans (by simpa only [utilities, dite_eq_left hi, dite_eq_left hj] using h)

include hlabel

omit hcorrect in
theorem protected_utility (i j : Fin n) (hj : j ∈ participants)
    (hprotect : ∀ s, (cost i).real (blocks s label) ≤ gap s label i) :
    utilities state participants gap out i j ≤ 0 := by
  have h := protected_utility_nonpositive cost blocks Subtype.val state.partition.representative gap
    out hparts i (⟨j, hj⟩ : participants) (by simpa only [hlabel j hj] using hprotect _)
  simpa only [utilities, dite_eq_left hj] using h

theorem donations_wellFormed (hlive : ∀ s, (packages s).live = some (frames s))
    (hframes : ∀ s, (frames s).Good)
    (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i) :
    ∀ d ∈ donations state visited participants label packages frames gap out, d.WellFormed := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
  have hj' := Finset.mem_toList.mp hj
  let task : participants := ⟨j, hj'⟩
  have hgood := ComponentDonors.affine_good state visited frames Subtype.val gap out task
    hframes hallowed (affine_own_nonnegative cost blocks Subtype.val state.partition.representative
      gap out hparts hcorrect task)
  constructor
  · exact hlive _
  · simpa only [Function.comp_apply, donorRoot, utilities, owners, dite_eq_left hj',
      ComponentDonors.affine, task, hlabel j hj'] using hgood

theorem payment_coverage
    (hprotect : ∀ i ∉ participants, ∀ s, (cost i).real (blocks s label) ≤ gap s label i)
    (i j p : Fin n) :
    extras (donations state visited participants label packages frames gap out) i j p ≤
      payments (donations state visited participants label packages frames gap out) i p := by
  apply ComponentAffine.task_payment_coverage
  · exact own_nonnegative state participants gap out cost blocks hparts hcorrect
  · intro i hi j hj
    exact comparisons state participants label gap out hlabel cost blocks hparts hcorrect i j hi hj
  · intro i hi j hj
    exact protected_utility state participants label gap out hlabel cost blocks hparts i j hj (hprotect i hi)

def outputPackage (hmany : Fintype.card participants < Fintype.card Root) : Package (Fin n) RootId :=
  mergeClosed (packages (ComponentAssignment.unused out.allocation hmany))
    (donations state visited participants label packages frames gap out)

theorem output_valid (hmany : Fintype.card participants < Fintype.card Root)
    (hlive : ∀ s, (packages s).live = some (frames s)) (hvalid : ∀ s, (packages s).Valid)
    (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
    (hprotect : ∀ i ∉ participants, ∀ s, (cost i).real (blocks s label) ≤ gap s label i) :
    (outputPackage state visited participants label packages frames gap out hmany).Valid := by
  have hframes : ∀ s, (frames s).Good := fun s => (hvalid s).live_good _ (hlive s)
  apply merge_closed_valid _ (hvalid _) _
    (donations_wellFormed state visited participants label packages frames gap out hlabel cost
      blocks hparts hcorrect hlive hframes hallowed)
  · intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    exact hvalid _
  · intro i j p hij
    exact payment_coverage state visited participants label packages frames gap out hlabel cost
      blocks hparts hcorrect hprotect i j p

theorem whole_suffix_retained
    (hcache : Masked.CacheCorrect (measureProfile cost)
      (domains blocks state.partition.representative) out.cache) :
    ∃ j : participants,
      material (out.parts j).suffixParts = blocks (out.allocation.assigned j) label ∧
      (ComponentDonors.affine state visited frames Subtype.val gap out j).execute = true := by
  obtain ⟨j, hj, _⟩ := affine_whole_retained cost blocks Subtype.val
    state.partition.representative gap out hparts hcorrect hcache
  exact ⟨j, by simpa only [hlabel j j.property] using hj, rfl⟩

end EnvyFreeResearch.Full.Chores.ComponentClosed
