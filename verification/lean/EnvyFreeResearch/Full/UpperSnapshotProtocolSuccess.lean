import EnvyFreeResearch.Full.UpperSnapshotProtocolSmallFacts
import EnvyFreeResearch.Full.UpperSnapshotProtocolLargeFacts

/-! Every accepted output of the complete executed Snapshot program has the
full physical contract. This theorem is pathwise and does not assume a random
good event or a positive acceptance probability. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotCandidates UpperDomainDifference UpperSortedGrid UpperCommonGrid
variable {n k : ℕ} [Nonempty (Fin k)]

theorem SnapshotSuccessFacts.of_domain_eq
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (chores : Bool) (active : Fin k → Fin n) (origin whole : State n) (result : PhysicalResult n k)
    (hf : SnapshotSuccessFacts μ chores active origin result) (hd : domain origin.cells = domain whole.cells) :
    SnapshotSuccessFacts μ chores active whole result :=
  ⟨hf.allocation_wellFormed,hf.residue_wellFormed,hf.allocation_disjoint,hf.residue_disjoint,
    hf.material_preserved.trans hd,hf.envyFree,hf.common_history,hf.terminal_or_margin⟩

theorem snapshot_success_facts
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (tape : Tape n k)
    (hs : (snapshotExecute policy hk chores active origin cutter tape).2.2=false) :
    SnapshotSuccessFacts μ chores active origin (snapshotExecute policy hk chores active origin cutter tape) := by
  let data := UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) tape.1
  let values := UpperGridData.table active origin data
  let D := selectedDistance (by omega) values cutter
  have hw : WellFormed μ (UpperGridData.aligned data) :=
    UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive _ _ _
  have hd : domain (UpperGridData.aligned data).cells = domain origin.cells :=
    UpperGridCache.aligned_domain policy active origin _ _ _
  have hp : ∀ i, 0 < (μ (active i)).real (domain (UpperGridData.aligned data).cells) := by
    simpa only [hd] using hpositive
  have hnonneg : 0 ≤ D := rowDistance_nonnegative values cutter _
  change (fromDataExecute policy hk chores active origin cutter data tape.2.1 tape.2.2.1 tape.2.2.2).2.2=false at hs
  change SnapshotSuccessFacts μ chores active origin
    (fromDataExecute policy hk chores active origin cutter data tape.2.1 tape.2.2.1 tape.2.2.2)
  unfold fromDataExecute at hs ⊢
  by_cases hz : D=0
  · dsimp only [D,values] at hz
    simp only [hz,ite_true] at hs ⊢
    exact SnapshotSuccessFacts.of_domain_eq μ chores active _ origin _
      (zero_snapshot_facts μ policy hpolicy (by omega) chores active _ hw cutter (hp cutter) tape.2.1 hs) hd
  · have hD : 0<D := lt_of_le_of_ne hnonneg (Ne.symm hz)
    dsimp only [D,values] at hz
    simp only [hz,ite_false] at hs ⊢
    by_cases hsmall : D<UpperRepair.nearError n/16
    · dsimp only [D,values] at hsmall
      simp only [hsmall,ite_true] at hs ⊢
      have hend := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive
        (UpperRepair.coarse n) (UpperRepair.fine n) tape.1
      have hmono : Monotone (UpperGridData.cuts data) := grid_monotone _
      have hsep : ∀ e, SeparatedAt (UpperGridData.cuts data e) (UpperGridData.aligned data).cells :=
        UpperGridCache.aligned_separated policy active origin _ _ _
      exact SnapshotSuccessFacts.of_domain_eq μ chores active _ origin _
        (small_snapshot_facts μ policy hpolicy (by omega) chores active hinj _ hw cutter (hp cutter)
          (UpperGridData.cuts data) hend.1 hmono hsep
          (fun e => values (selectedRow (by omega) values cutter) e-values cutter e)
          D hD hsmall tape.2.2.1 tape.2.2.2 hs) hd
    · dsimp only [D,values] at hsmall
      simp only [hsmall,ite_false] at hs ⊢
      exact large_snapshot_facts μ policy hpolicy hk chores active hinj origin hgood hpositive
        tape.1 cutter hD tape.2.2.2 hs
end EnvyFreeResearch.Full.UpperSnapshotProtocol
