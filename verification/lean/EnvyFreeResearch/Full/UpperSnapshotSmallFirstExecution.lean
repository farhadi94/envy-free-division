import EnvyFreeResearch.Full.UpperSnapshotSmallCircle
import EnvyFreeResearch.Full.UpperLogicalPreparationState

/-! The first positive-cell candidate stage. The two new roots are queried
on the chosen subdomain, then all original atoms are refined at those roots.
This restores the complete physical domain while retaining the full history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m : ℕ}

def positiveFlag (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) : Component → Bool :=
  UpperPendingExclusion.selected cuts (fun _ : Unit => selected)

def firstFill (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) : Bool :=
  decide (total (retain origin cuts selected) cutter < t * total origin cutter)

def firstSource (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) : State n :=
  if firstFill origin cutter cuts selected t then selectState origin (fun c => !positiveFlag cuts selected c)
  else retain origin cuts selected

def firstDeficit (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) : ℝ :=
  if firstFill origin cutter cuts selected t then t * total origin cutter - total (retain origin cuts selected) cutter
  else t * total origin cutter

def firstAmount (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) : I :=
  amount (firstDeficit origin cutter cuts selected t) (total (firstSource origin cutter cuts selected t) cutter)

def singleTargets (a : I) : Fin 3 → I := ![0, a, 1]

def firstRun (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) : (Fin 2 → ℝ) × State n :=
  partitionRun policy (firstSource origin cutter cuts selected t) cutter
    (singleTargets (firstAmount origin cutter cuts selected t)) start

def firstRestored (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) : State n :=
  let result := firstRun policy origin cutter cuts selected t start
  ⟨refineEndpoints origin.cells (List.ofFn result.1), result.2.history⟩

def firstFlag (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) (c : Component) : Bool :=
  let result := firstRun policy origin cutter cuts selected t start
  let arc := prefixAtom (firstAmount origin cutter cuts selected t) start (result.1 0) (result.1 1) c
  if firstFill origin cutter cuts selected t then positiveFlag cuts selected c || arc
  else positiveFlag cuts selected c && arc

def firstEndowment (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) : State n :=
  selectState (firstRestored policy origin cutter cuts selected t start)
    (firstFlag policy origin cutter cuts selected t start)

def firstRemainder (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) : State n :=
  selectState (firstRestored policy origin cutter cuts selected t start)
    (fun c => !firstFlag policy origin cutter cuts selected t start c)

theorem firstSource_history (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) :
    (firstSource origin cutter cuts selected t).history = origin.history := by
  unfold firstSource
  split_ifs <;> rfl

theorem firstRestored_domain (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    domain (firstRestored policy origin cutter cuts selected t start).cells = domain origin.cells :=
  refineEndpoints_domain _ _

theorem firstRestored_query_bound (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    (firstRestored policy origin cutter cuts selected t start).history.length ≤ origin.history.length + 2 * (n + 1) := by
  have h := execute_query_bound policy (firstSource origin cutter cuts selected t) cutter
    (shifts (singleTargets (firstAmount origin cutter cuts selected t))) start
  simpa only [firstRestored, firstRun, partitionRun, firstSource_history] using h

theorem firstRestored_cut_bound (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    ((firstRestored policy origin cutter cuts selected t start).history.map Prod.fst).countP isCut ≤
      (origin.history.map Prod.fst).countP isCut + 2 := by
  have h := execute_cut_bound policy (firstSource origin cutter cuts selected t) cutter
    (shifts (singleTargets (firstAmount origin cutter cuts selected t))) start
  simpa only [firstRestored, firstRun, partitionRun, firstSource_history] using h

section Correctness
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem firstSource_wellFormed (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) :
    WellFormed μ (firstSource origin cutter cuts selected t) := by
  unfold firstSource
  split_ifs
  · exact selectState_wellFormed μ origin hgood _
  · exact retain_wellFormed μ origin hgood cuts selected

theorem firstRestored_wellFormed (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (hsource : 0 < (μ cutter).real (domain (firstSource origin cutter cuts selected t).cells)) (start : Circle) :
    WellFormed μ (firstRestored policy origin cutter cuts selected t start) := by
  have hw := firstSource_wellFormed μ origin hgood cutter cuts selected t
  have hr := execute_records μ policy hpolicy (firstSource origin cutter cuts selected t) hw cutter hsource
    (shifts (singleTargets (firstAmount origin cutter cuts selected t))) start
  have hf := execute_wellFormed μ policy hpolicy (firstSource origin cutter cuts selected t) hw cutter hsource
    (shifts (singleTargets (firstAmount origin cutter cuts selected t))) start
  let restored : State n := ⟨origin.cells, (firstRun policy origin cutter cuts selected t start).2.history⟩
  have hrestored : WellFormed μ restored := by
    refine ⟨hgood.1, hgood.2.1, hf.2.2.1, ?_⟩
    apply UpperEndpointCache.recordedHistory_mono _ hgood.2.2.2
    simpa only [restored, firstRun, partitionRun, firstSource_history] using hr.1
  apply refineEndpoints_wellFormed μ restored hrestored
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact (hr.2 j).2

theorem first_partition (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (hsource : 0 < (μ cutter).real (domain (firstSource origin cutter cuts selected t).cells)) (start : Circle) :
    WellFormed μ (firstEndowment policy origin cutter cuts selected t start) ∧
    WellFormed μ (firstRemainder policy origin cutter cuts selected t start) ∧
    domain (firstRemainder policy origin cutter cuts selected t start).cells =
      domain origin.cells \ domain (firstEndowment policy origin cutter cuts selected t start).cells := by
  have hw := firstRestored_wellFormed μ policy hpolicy origin hgood cutter cuts selected t hsource start
  refine ⟨selectState_wellFormed μ _ hw _, selectState_wellFormed μ _ hw _, ?_⟩
  change domain ((firstRestored policy origin cutter cuts selected t start).cells.filter
    (fun c => !firstFlag policy origin cutter cuts selected t start c)) = _
  rw [whole_filter_domain _ hw.2.1, firstRestored_domain]
  rfl

end Correctness
end EnvyFreeResearch.Full.UpperSnapshotSmall
