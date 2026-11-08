import EnvyFreeResearch.Full.NonnegativeEndpointCapture
import EnvyFreeResearch.Full.NonnegativeRealLedger

namespace EnvyFreeResearch.Full.NonnegativeMainEvents

open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeExperiment
open NonnegativeRandomOutput NonnegativeRetainedFailure NonnegativeEndpointCapture
open NonnegativeEndpointLaw NonnegativeShift NonnegativeDetection NonnegativeDecoderLedger
open NonnegativeProbability NonnegativeRealLedger NonnegativeMeasurableDetection
open scoped Classical ENNReal Topology

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

noncomputable def baseline
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n))) (flag : Bool) (fuel : ℕ)
    (tape : Tape) : PhysicalExecution n := run next (flaggedOracle flag uniform) tape fuel []

theorem baseline_measurable
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (fuel : ℕ) : Measurable (baseline next flag fuel) :=
  measurable_run_at_history next (flaggedOracle flag uniform) hnext (uniformFlagged_measurable flag) fuel []

def inputGood (chores : Bool) (h : ℝ) : Set (Input n × Allocation (Fin n)) :=
  {z | Fair chores (inputRows h z.1) z.2}

theorem inputGood_measurable (chores : Bool) (h : ℝ) : MeasurableSet (inputGood (n := n) chores h) := by
  cases chores
  · exact inputCakeEF_measurable h
  · exact inputChoreEF_measurable h

def failure (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag chores : Bool) (h : ℝ) : Set (Tape × Input n) :=
  Prod.swap ⁻¹' (jointSuccess next (inputOracle flag h) [] (inputGood chores h))ᶜ

theorem failure_measurable
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (h : ℝ) : MeasurableSet (failure next flag chores h) :=
  (measurable_jointSuccess next (inputOracle flag h) hnext (inputOracle_measurable flag h) []
    (inputGood chores h) (inputGood_measurable chores h)).compl.preimage measurable_swap

def success (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) : Set (Tape × Input n) :=
  {z | Successful {A | UniformEF A} (baseline next flag fuel z.1)}

def detected (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) : Set (Tape × Input n) :=
  {z | z.2 ∈ detection (baselineRequests uniform (baseline next flag fuel z.1))}

def gapLoss (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) (h : ℝ) : Set Tape :=
  {tape | Successful {A | ¬ UniformEF A} (baseline next flag fuel tape)} ∩
    {tape | outputGap (baseline next flag fuel tape) ≤ h}

def geometricLoss (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) (h : ℝ) : Set (Tape × Input n) :=
  endpointHit (fun tape => endpointCount uniform (baseline next flag fuel tape))
    (fun tape k => endpoint uniform (baseline next flag fuel tape) k) centerFirst h ∪
  (endpointHit (fun tape => endpointCount uniform (baseline next flag fuel tape))
    (fun tape k => endpoint uniform (baseline next flag fuel tape) k) centerSecond h ∪
    Prod.fst ⁻¹' gapLoss next flag fuel h)

def capLoss (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) : Set (Tape × Input n) :=
  {z | Exhausted (baseline next flag fuel z.1)}

theorem success_measurable
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (fuel : ℕ) : MeasurableSet (success next flag fuel) :=
  (measurable_successful _ measurable_uniformEF).preimage
    ((baseline_measurable next hnext flag fuel).comp measurable_fst)

theorem gapLoss_measurable
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (fuel : ℕ) (h : ℝ) : MeasurableSet (gapLoss next flag fuel h) :=
  ((measurable_successful _ measurable_uniformEF.compl).preimage
    (baseline_measurable next hnext flag fuel)).inter
      (measurableSet_le (measurable_outputGap.comp (baseline_measurable next hnext flag fuel)) measurable_const)

/-- All geometric premises of concrete replay and both physical decoders
are discharged by membership outside the actual endpoint/gap loss events. -/
theorem retained_event_inclusion [NeZero n]
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag chores : Bool) (fuel : ℕ) (h : ℝ) (hh : 0 < h) :
    ((success next flag fuel)ᶜ ∪ decoded (baseline next flag fuel) chores) \
      (detected next flag fuel ∪ (geometricLoss next flag fuel h ∪ capLoss next flag fuel)) ⊆
      failure next flag chores h := by
  rintro z ⟨hretained, hnot⟩
  have hdetect : z ∉ detected next flag fuel := fun hz => hnot (Or.inl hz)
  have hgeometry : z ∉ geometricLoss next flag fuel h := fun hz => hnot (Or.inr (Or.inl hz))
  have hcap : z ∉ capLoss next flag fuel := fun hz => hnot (Or.inr (Or.inr hz))
  have hsafe : CoordinatesSafe uniform (baseline next flag fuel z.1) h
      (centerFirst z.2) (centerSecond z.2) :=
    coordinatesSafe_of_no_hit uniform (baseline next flag fuel) z.1 z.2 h hh.le
      (fun hz => hgeometry (Or.inl hz)) (fun hz => hgeometry (Or.inr (Or.inl hz)))
  have hc : centerFirst z.2 ∈ Ioc (0 : ℝ) 1 := representative_range _
  have hd : centerSecond z.2 ∈ Ioc (0 : ℝ) 1 := representative_range _
  obtain ⟨hc0, hc1, hd0, hd1⟩ := coordinatesSafe_nonwrapping uniform
    (baseline next flag fuel z.1) h (centerFirst z.2) (centerSecond z.2) hc hd hsafe
  have hterminal : Terminal (baseline next flag fuel z.1).stop := by
    intro query hquery
    exact hcap ⟨query, hquery⟩
  have hgap : ∀ A, (baseline next flag fuel z.1).stop = .returned A →
      ¬ UniformEF A → h < uniformGap A := by
    intro A hreturned hwrong
    by_contra hlarge
    apply hgeometry
    right
    right
    refine ⟨⟨A, hreturned, hwrong⟩, ?_⟩
    change outputGap (baseline next flag fuel z.1) ≤ h
    simpa only [outputGap, returnedValue, hreturned] using le_of_not_gt hlarge
  have hretention : ¬ Successful {A | UniformEF A} (baseline next flag fuel z.1) ∨
      ∃ A, (baseline next flag fuel z.1).stop = .returned A ∧
        UniformEF A ∧ Favorable chores A z.2.1 z.2.2 := by
    rcases hretained with hold | ⟨A, hreturned, hgood⟩
    · exact Or.inl hold
    · exact Or.inr ⟨A, hreturned, hgood⟩
  exact actual_retained_failure next flag chores z.1 fuel z.2.1 z.2.2 h hh
    hc0 hc1 hd0 hd1 (coordinatesSafe_query _ _ _ _ _ hsafe) hdetect hterminal
    (fun A hreturned => coordinatesSafe_output _ _ _ _ _ A hreturned hsafe) hgap hretention

theorem fst_lift_mass {Parameter : Type*} [MeasurableSpace Parameter]
    (μ : Measure Tape) (ν : Measure Parameter) [IsProbabilityMeasure ν] (A : Set Tape) :
    (μ.prod ν) (Prod.fst ⁻¹' A) = μ A := by
  have heq : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set Parameter) := by ext z; simp
  rw [heq, Measure.prod_prod, measure_univ, mul_one]

theorem geometricLoss_mass_le
    (μ : Measure Tape) (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) (h : ℝ) :
    (μ.prod (perturbLaw n w)) (geometricLoss next flag fuel h) ≤
      (μ.prod (perturbLaw n w)) (endpointHit
        (fun tape => endpointCount uniform (baseline next flag fuel tape))
        (fun tape k => endpoint uniform (baseline next flag fuel tape) k) centerFirst h) +
      (μ.prod (perturbLaw n w)) (endpointHit
        (fun tape => endpointCount uniform (baseline next flag fuel tape))
        (fun tape k => endpoint uniform (baseline next flag fuel tape) k) centerSecond h) +
      μ (gapLoss next flag fuel h) := by
  let := perturbLaw_probability n hn w hw
  apply (measure_union_le _ _).trans
  have hinner := measure_union_le (μ := μ.prod (perturbLaw n w))
    (endpointHit (fun tape => endpointCount uniform (baseline next flag fuel tape))
      (fun tape k => endpoint uniform (baseline next flag fuel tape) k) centerSecond h)
    (Prod.fst ⁻¹' gapLoss next flag fuel h)
  rw [fst_lift_mass μ (perturbLaw n w)] at hinner
  exact (add_le_add le_rfl hinner).trans_eq (add_assoc _ _ _).symm

end EnvyFreeResearch.Full.NonnegativeMainEvents

#print axioms EnvyFreeResearch.Full.NonnegativeMainEvents.retained_event_inclusion
#print axioms EnvyFreeResearch.Full.NonnegativeMainEvents.geometricLoss_mass_le
