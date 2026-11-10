import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepairSubset
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepairBalance
import EnvyFreeResearch.Full.RefinedUpperRepairFailure

/-! Actual successful Repair supplies the whole-label physical transport,
all-original-observer mass identity and active quarter-spending bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperRepairPreparationChecks
  RefinedUpperRepair RefinedUpperPreparation RefinedUpperRepairFinalCache
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (nearError n))
  (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
  (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (holdHistory : ∀ j, (old j).history ⊆ origin.history) (p : RefinedUpperRepair.Tape n k)
  (hsuccess : (RefinedUpperRepair.execute policy hk chores active origin old p).2.2 = false)

include hpolicy hinj hgood hpositive hold hnear holdpair holdbuffer holdHistory hsuccess in
theorem actual_transport :
    ∃ f : Equiv.Perm (Fin k), ∃ added : Fin k → State n,
      (∀ j, domain ((RefinedUpperRepair.execute policy hk chores active origin old p).1 (f j)).cells =
        domain (old j).cells ∪ domain (added j).cells) ∧
      (∀ j, domain (added j).cells ⊆ domain origin.cells) ∧
      (∀ i, (∑ j, (μ i).real (domain (added j).cells)) +
        (μ i).real (domain (RefinedUpperRepair.execute policy hk chores active origin old p).2.1.cells) =
          (μ i).real (domain origin.cells)) ∧
      (∀ i, (∑ j, (μ (active i)).real (domain (added j).cells)) <
        (μ (active i)).real (domain origin.cells) / 4) := by
  have facts := RefinedUpperRepair.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive
    old hold hnear holdpair holdbuffer holdHistory p hsuccess
  obtain ⟨ha,he,hs⟩ := RefinedUpperRepairProgram.accepted_output policy hk chores active origin old
    (coarse n) (fine n) (repeats n) p.1.1 p.1.2.1 p.1.2.2 (cellBound n) (gapMultiplier n) p.2 hsuccess
  let d := UpperGridMerge.prepare policy active origin (coarse n) (fine n) p.1.1
  let prepared := RefinedUpperPreparationProgram.finish hk chores active origin old d (repeats n) p.1.2.1 p.1.2.2
  let stage := executeStage policy active (dataRetained active origin d (repeats n)) (UpperGridData.cuts d)
    (RefinedUpperRepairTargets.targets chores active prepared (cellBound n) (gapMultiplier n))
    (cellBound n) (gapMultiplier n) p.2
  let f := receiver hk chores active origin old d (repeats n) p.1.2.1 p.1.2.2
  let added := additions hk chores active origin old d (repeats n) p.1.2.1 p.1.2.2 stage
  have hl : ∀ j, domain ((RefinedUpperRepair.execute policy hk chores active origin old p).1 (f j)).cells =
      domain (old j).cells ∪ domain (added j).cells := by
    intro j
    change domain ((RefinedUpperRepairProgram.execute policy hk chores active origin old (coarse n) (fine n)
      (repeats n) p.1.1 p.1.2.1 p.1.2.2 (cellBound n) (gapMultiplier n) p.2).1 (f j)).cells = _
    rw [he]
    exact whole_label_identity hk chores active origin old d (repeats n) p.1.2.1 p.1.2.2 stage j
  have hsub : ∀ j, domain (added j).cells ⊆ domain origin.cells := by
    intro j
    exact actual_additions_subset μ policy hpolicy hk chores active origin hgood hpositive old
      (coarse n) (fine n) (repeats n) p.1.1 (cellBound n) (gapMultiplier n)
      p.1.2.1 p.1.2.2 p.2 hs j
  refine ⟨f,added,hl,hsub,?_,?_⟩
  · exact success_additions_balance μ chores active origin old added _ facts f hl holdbuffer hsub
  · exact success_additions_quarter μ chores active origin old added _ facts f hl holdbuffer hsub

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
