import EnvyFreeResearch.Full.UpperSnapshotSmallSecondExecution

/-! A rejected two-circle candidate retains the entire original domain and
all queried endpoints in its complete history for the next adapted trial. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ}

def secondRestored (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (first second : Circle) : State n :=
  let out := secondRun (J := J) policy origin cutter cuts selected t first second
  ⟨refineEndpoints (firstRestored policy origin cutter cuts selected t first).cells (List.ofFn out.1),
    out.2.history⟩

theorem secondRestored_domain (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) (first second : Circle) :
    domain (secondRestored (J := J) policy origin cutter cuts selected t first second).cells = domain origin.cells := by
  unfold secondRestored
  rw [refineEndpoints_domain, firstRestored_domain]

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
  (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
  (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
include hpolicy hgood hpositive hzero hmono hsep ht ht1

theorem secondRestored_wellFormed (first second : Circle) :
    WellFormed μ (secondRestored (J := J) policy origin cutter cuts selected t first second) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hw := firstRestored_wellFormed μ policy hpolicy origin hgood cutter cuts selected t hs first
  have hp := firstRemainder_positive μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first
  have hr := (first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first).2.1
  have hex := execute_records μ policy hpolicy _ hr cutter hp (shifts (remainderTargets J t)) second
  have ho := execute_wellFormed μ policy hpolicy _ hr cutter hp (shifts (remainderTargets J t)) second
  let restored : State n := ⟨(firstRestored policy origin cutter cuts selected t first).cells,
    (secondRun (J := J) policy origin cutter cuts selected t first second).2.history⟩
  have hrestored : WellFormed μ restored := by
    refine ⟨hw.1,hw.2.1,ho.2.2.1,?_⟩
    exact UpperEndpointCache.recordedHistory_mono _ hw.2.2.2 hex.1
  apply refineEndpoints_wellFormed μ restored hrestored
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  exact (hex.2 j).2

end EnvyFreeResearch.Full.UpperSnapshotSmall
