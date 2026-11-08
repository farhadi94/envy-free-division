import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableProgramState
import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableSecond
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocation

/-! The actual pure allocation packet is Borel for arbitrary raw first/second
outputs. This supplies the postprocessing certificate of the query program. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperDomainDifference UpperGridRecords Chores
variable {n m J : ℕ} {X : Type*} [MeasurableSpace X]

theorem firstAllocationFrom_joint_measurable (origin : X → State n) (cutter : Fin n)
    (cuts : X → Fin (m+2) → ℝ) (selected : X → Finset (Fin (m+1))) (t : X → ℝ) (first : X → Circle)
    (rawFirst : X → (Fin 2 → ℝ) × State n) (rawSecond : X → (Fin J → ℝ) × State n)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e)) (hs : Measurable selected)
    (ht : Measurable t) (hf : Measurable first) (hr₁ : Measurable rawFirst) (hr₂ : Measurable rawSecond) :
    Measurable (fun x => firstAllocationFrom (origin x) cutter (cuts x) (selected x) (t x) (first x)
      (rawFirst x) (rawSecond x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x => ((restoredFrom (origin x) (rawFirst x)).cells.filter
    (flagFrom (origin x) cutter (cuts x) (selected x) (t x) (first x) (rawFirst x)), (rawSecond x).2.history))
  exact (list_filter_measurable _ _
    (flagFrom_joint_measurable origin cutter cuts selected t first rawFirst ho hc hs ht hf hr₁)
    (state_cells_measurable.comp (restoredFrom_joint_measurable origin rawFirst ho hr₁))).prodMk
    (state_history_measurable.comp (measurable_snd.comp hr₂))

theorem secondAllocationFrom_joint_measurable (hJ : 0 < J) (t : X → ℝ) (start : X → Circle)
    (raw : X → (Fin J → ℝ) × State n) (ht : Measurable t) (hs : Measurable start)
    (hr : Measurable raw) (j : Fin J) :
    Measurable (fun x => secondAllocationFrom hJ (t x) (start x) (raw x) j) := by
  have hp (i : Fin J) : Measurable (fun x => (raw x).1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp hr)
  have hb (i : Fin (J+1)) : Measurable (fun x => boundary hJ (raw x).1 i) :=
    boundary_measurable hJ _ hp i
  have ha (i : Fin (J+1)) : Measurable (fun p : X × Component =>
      prefixAtom (remainderTargets J (t p.1) i) (start p.1) ((raw p.1).1 ⟨0,hJ⟩)
        (boundary hJ (raw p.1).1 i) p.2) :=
    prefixAtom_measurable _ _ _ _ _ ((remainderTargets_joint_measurable t ht i).comp measurable_fst)
      (hs.comp measurable_fst) ((hp _).comp measurable_fst) ((hb i).comp measurable_fst) measurable_snd
  exact selectState_measurable _ _ (measurable_snd.comp hr)
    ((measurable_of_countable (fun p : Bool × Bool => p.1 && !p.2)).comp
      ((ha j.succ).prodMk (ha j.castSucc)))

theorem allocationFrom_joint_measurable (hJ : 0 < J) (origin : X → State n) (cutter : Fin n)
    (cuts : X → Fin (m+2) → ℝ) (selected : X → Finset (Fin (m+1))) (t : X → ℝ) (first second : X → Circle)
    (rawFirst : X → (Fin 2 → ℝ) × State n) (rawSecond : X → (Fin J → ℝ) × State n)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e)) (hs : Measurable selected)
    (ht : Measurable t) (hf : Measurable first) (hsecond : Measurable second)
    (hr₁ : Measurable rawFirst) (hr₂ : Measurable rawSecond) :
    Measurable (fun x => allocationFrom hJ (origin x) cutter (cuts x) (selected x) (t x) (first x) (second x)
      (rawFirst x) (rawSecond x)) := by
  have ha := firstAllocationFrom_joint_measurable origin cutter cuts selected t first rawFirst rawSecond
    ho hc hs ht hf hr₁ hr₂
  have hb := secondAllocationFrom_joint_measurable hJ t second rawSecond ht hsecond hr₂
  have hw : Measurable (fun x =>
      (⟨refineEndpoints (restoredFrom (origin x) (rawFirst x)).cells (List.ofFn (rawSecond x).1),
        (rawSecond x).2.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => (refineEndpoints (restoredFrom (origin x) (rawFirst x)).cells
      (List.ofFn (rawSecond x).1), (rawSecond x).2.history))
    exact (refineEndpoints_measurable _ _
      (state_cells_measurable.comp (restoredFrom_joint_measurable origin rawFirst ho hr₁))
      ((UpperRecordedGrid.ofFn_measurable J).comp (measurable_fst.comp hr₂))).prodMk
      (state_history_measurable.comp (measurable_snd.comp hr₂))
  apply Measurable.prodMk _ ((hb ⟨J-1,by omega⟩).prodMk hw)
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j.val=0
  · simpa only [allocationFrom,dite_eq_left hj] using ha
  · simpa only [allocationFrom,dite_eq_right hj] using hb ⟨j.val-1,by omega⟩
end EnvyFreeResearch.Full.UpperSnapshotSmall
