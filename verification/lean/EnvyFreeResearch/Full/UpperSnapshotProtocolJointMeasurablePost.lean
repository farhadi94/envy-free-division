import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurableDomain
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallJoint
import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableProgramAllocation

/-! The actual cache-only acceptance postprocessor is Borel even on arbitrary
raw reply packets; no legal-policy or physical-state premise is used. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotProtocol ProtocolMeasurable UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable
variable {n m J : ℕ} {X : Type*} [MeasurableSpace X]

theorem interpolationCheck_varying_domain_measurable
    (hJ : 2≤J) (cutter : Fin n) (U : X → Set ℝ) (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1})
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (t : X → ℝ) (first second : X → Circle)
    (rawFirst : X → (Fin 2 → ℝ) × State n) (rawSecond : X → (Fin J → ℝ) × State n)
    (ho : Measurable origin) (hc : ∀ e,Measurable (fun x => cuts x e))
    (hs : ∀ e,Measurable (fun x => score x e)) (ht : Measurable t)
    (hf : Measurable first) (hg : Measurable second) (hr₁ : Measurable rawFirst) (hr₂ : Measurable rawSecond) :
    Measurable (fun x => interpolationCheck hJ cutter (cuts x) (score x) (U x) (t x)
      (origin x) (first x,second x) (rawFirst x) (rawSecond x)) := by
  have hp := positiveIndices_measurable score hs
  have hfirst : Measurable (fun x => firstFrom (origin x) cutter (cuts x) (positiveIndices (score x)) (t x) (first x) (rawFirst x)) :=
    selectState_measurable _ _ (restoredFrom_joint_measurable origin rawFirst ho hr₁)
      (flagFrom_joint_measurable origin cutter cuts (fun x => positiveIndices (score x)) t first rawFirst ho hc hp ht hf hr₁)
  have hsecond : Measurable (fun x => secondFrom (J:=J) (by omega) (t x) (second x) (rawSecond x) ⟨0,by omega⟩) :=
    secondAllocationFrom_joint_measurable (by omega) t second rawSecond ht hg hr₂ ⟨0,by omega⟩
  have hcontrast := (varying_interpolatedTotal_measurable U hU score hs cuts hc _
    (state_cells_measurable.comp hfirst)).sub
    (varying_interpolatedTotal_measurable U hU score hs cuts hc _ (state_cells_measurable.comp hsecond))
  have hD : Measurable (fun x => (∑ e,|score x e|)/(8*(J:ℝ))) :=
    (Finset.measurable_sum Finset.univ (fun e _ => (hs e).abs)).div_const _
  exact decide_measurable _ (measurableSet_le hD hcontrast)

theorem smallPost_varying_domain_measurable
    (hJ : 2≤J) (cutter : Fin n) (U : X → Set ℝ) (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1})
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (t : X → ℝ) (first second : X → Circle)
    (rawFirst : X → (Fin 2 → ℝ) × State n) (rawSecond : X → (Fin J → ℝ) × State n)
    (ho : Measurable origin) (hc : ∀ e,Measurable (fun x => cuts x e))
    (hs : ∀ e,Measurable (fun x => score x e)) (ht : Measurable t)
    (hf : Measurable first) (hg : Measurable second) (hr₁ : Measurable rawFirst) (hr₂ : Measurable rawSecond) :
    Measurable (fun x => smallPost (origin x)
      (interpolationCheck hJ cutter (cuts x) (score x) (U x) (t x) (origin x) (first x,second x))
      (rawFirst x) (rawSecond x)) := by
  have hnext : Measurable (fun x => secondRestoredFrom (origin x) (rawFirst x) (rawSecond x)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => (refineEndpoints (restoredFrom (origin x) (rawFirst x)).cells
      (List.ofFn (rawSecond x).1), (rawSecond x).2.history))
    exact (refineEndpoints_measurable _ _
      (state_cells_measurable.comp (restoredFrom_joint_measurable origin rawFirst ho hr₁))
      ((UpperRecordedGrid.ofFn_measurable J).comp (measurable_fst.comp hr₂))).prodMk
      (state_history_measurable.comp (measurable_snd.comp hr₂))
  have hcheck := interpolationCheck_varying_domain_measurable hJ cutter U hU origin cuts score t first second rawFirst rawSecond
    ho hc hs ht hf hg hr₁ hr₂
  exact hnext.prodMk ((measurable_some.comp (hr₁.prodMk hr₂)).ite
    (measurableSet_eq_fun hcheck measurable_const) measurable_const)

end EnvyFreeResearch.Full.UpperSnapshotRepetition
