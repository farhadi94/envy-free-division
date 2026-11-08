import EnvyFreeResearch.Full.UpperGridDataMeasurable
import EnvyFreeResearch.Full.UpperLogicalPreparationGuard

/-! Snapshot strengthens the cached Repair guard by its missing upper-reserve
check. The independent two-sided mass exception will be charged once. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRecordedQuantiles UpperDomainDifference Chores
variable {n coarse fine : ℕ} {Agent : Type*} [Fintype Agent]

def upperReserve (active : Agent → Fin n) (origin reserve : State n) (theta : I) : Bool :=
  decide (∀ a, total reserve (active a) ≤ 3 * (theta : ℝ) / 2 * total origin (active a))

theorem upperReserve_eq_true (active : Agent → Fin n) (origin reserve : State n) (theta : I) :
    upperReserve active origin reserve theta = true ↔
      ∀ a, total reserve (active a) ≤ 3 * (theta : ℝ) / 2 * total origin (active a) := decide_eq_true_iff

/-- Pure cached post-grid Boolean; it never calls a response policy. -/
def dataGuard (active : Agent → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ) (labels : Fin (coarse + 1) → I) : Bool :=
  UpperGridData.guard active origin data jobs theta cap labels &&
    upperReserve active origin (UpperGridData.reserve data theta labels) theta

variable {X : Type*} [MeasurableSpace X]

theorem upperReserve_measurable (active : Agent → Fin n) (origin reserve : X → State n) (theta : I)
    (horigin : Measurable origin) (hreserve : Measurable reserve) :
    Measurable (fun x => upperReserve active (origin x) (reserve x) theta) := by
  apply decide_measurable
  have heq : {x | ∀ a, total (reserve x) (active a) ≤ 3 * (theta : ℝ) / 2 * total (origin x) (active a)} =
      ⋂ a, {x | total (reserve x) (active a) ≤ 3 * (theta : ℝ) / 2 * total (origin x) (active a)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter (fun a => measurableSet_le
    (total_measurable reserve (fun _ => active a) hreserve measurable_const)
    (measurable_const.mul (total_measurable origin (fun _ => active a) horigin measurable_const)))

theorem dataGuard_measurable (active : Agent → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (jobs : List (Agent × Agent)) (theta : I)
    (cap : X → ℝ) (labels : X → Fin (coarse + 1) → I) (horigin : Measurable origin)
    (hdata : Measurable data) (hcap : Measurable cap) (hlabels : ∀ p, Measurable (fun x => labels x p)) :
    Measurable (fun x => dataGuard active (origin x) (data x) jobs theta (cap x) (labels x)) :=
  (measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp
    ((UpperGridData.guard_measurable active origin data jobs theta cap labels horigin hdata hcap hlabels).prodMk
      (upperReserve_measurable active origin (fun x => UpperGridData.reserve (data x) theta (labels x)) theta
        horigin (UpperGridData.reserve_measurable data theta labels hdata hlabels)))

variable [Nonempty Agent]

def snapshotGuard (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I) : Bool :=
  UpperLogicalPreparationGuard.guard policy active origin q m jobs theta cap draw labels &&
    upperReserve active origin (reserveState policy active origin q m draw theta labels) theta

theorem dataGuard_execute (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    dataGuard active origin (UpperGridMerge.prepare policy active origin q m draw) jobs theta cap labels =
      snapshotGuard policy active origin q m jobs theta cap draw labels := by
  simp only [dataGuard, snapshotGuard, UpperGridData.guard_execute, UpperGridData.reserve_execute]

omit [Nonempty Agent] in
/-- Adding the upper check replaces the preparation event, rather than
adding a second mass-deviation charge to its existing probability bound. -/
theorem snapshotGuard_false (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    snapshotGuard policy active origin q m jobs theta cap draw labels = false ↔
      UpperLogicalPreparationGuard.guard policy active origin q m jobs theta cap draw labels = false ∨
      upperReserve active origin (reserveState policy active origin q m draw theta labels) theta = false :=
  Bool.and_eq_false_iff

omit [Nonempty Agent] in
theorem snapshotGuard_passes (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : snapshotGuard policy active origin q m jobs theta cap draw labels = true) :
    UpperLogicalPreparationGuard.guard policy active origin q m jobs theta cap draw labels = true ∧
      ∀ a, total (reserveState policy active origin q m draw theta labels) (active a) ≤
        3 * (theta : ℝ) / 2 * total origin (active a) := by
  exact ⟨(Bool.and_eq_true_iff.mp hpass).1, (upperReserve_eq_true _ _ _ _).mp (Bool.and_eq_true_iff.mp hpass).2⟩

section Measurability
variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem snapshotGuard_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ) :
    Measurable (fun p : (Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I) =>
      snapshotGuard policy active origin q m jobs theta cap p.1 p.2) := by
  let X := (Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I)
  have hstate : Measurable (fun p : X => reserveState policy active origin q m p.1 theta p.2) :=
    UpperLogicalPreparationGuard.fixed_origin_measurable
      (fun p : (State n × (Fin m → Agent × I)) × (Fin (count (Agent := Agent) q + 1) → I) =>
        reserveState policy active p.1.1 q m p.1.2 theta p.2)
      (reserveState_measurable policy hmeas active q m theta) origin
  exact (measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp
    ((UpperLogicalPreparationGuard.guard_measurable policy hmeas active origin q m jobs theta cap).prodMk
      (upperReserve_measurable active (fun _ => origin) _ theta measurable_const hstate))
end Measurability

/-- A passed strengthened guard has both literal raw-mass checks, using the
actual final full-history reserve and its proved cache correctness. -/
theorem snapshotGuard_mass (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : snapshotGuard policy active origin q m jobs theta cap draw labels = true) (a : Agent) :
    (theta : ℝ) / 2 * (μ (active a)).real (domain origin.cells) ≤
        (μ (active a)).real (domain (reserveState policy active origin q m draw theta labels).cells) ∧
      (μ (active a)).real (domain (reserveState policy active origin q m draw theta labels).cells) ≤
        3 * (theta : ℝ) / 2 * (μ (active a)).real (domain origin.cells) := by
  have hp := snapshotGuard_passes policy active origin q m jobs theta cap draw labels hpass
  refine ⟨UpperLogicalPreparationGuard.passing_lower_mass μ policy hpolicy active origin hgood hpositive
    q m jobs theta cap draw labels hp.1 a, ?_⟩
  have hu := hp.2 a
  rw [total_correct μ origin hgood,
    total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels)] at hu
  exact hu

end EnvyFreeResearch.Full.UpperSnapshotCandidates
