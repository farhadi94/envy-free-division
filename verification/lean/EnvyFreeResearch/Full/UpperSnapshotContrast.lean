import EnvyFreeResearch.Full.UpperSnapshotContrastTrial
import EnvyFreeResearch.Full.UpperSnapshotContrastSelectedPhysical

/-! Snapshot contrast preservation: actual fresh seed symmetry, arbitrary
full-history averaging, and the physical margin consequence on Repair return.
The successful physical joining contract is an explicit interface to Repair. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
open UpperLogicalIsolation UpperRepairJobs
variable {k L : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- The observable finite-pair margin event is measurable whenever its actual
physical masses are measurable. -/
theorem physical_margin_event_measurable (chores : Bool) (μ : Fin k → Measure ℝ)
    (allocation : Ω → Fin k → Set ℝ) (residue : Ω → Set ℝ) (G : Set Ω) (hG : MeasurableSet G)
    (hallocation : ∀ i j, Measurable (fun z => (μ i).real (allocation z j)))
    (hresidue : ∀ i, Measurable (fun z => (μ i).real (residue z))) (Lambda : ℝ) :
    MeasurableSet {z | z ∈ G ∧ ∃ a b, a ≠ b ∧ 0 < physicalGap chores μ (allocation z) a b ∧
      Lambda / 8 * (μ a).real (residue z) ≤ physicalGap chores μ (allocation z) a b} := by
  suffices hp : MeasurableSet {z | ∃ a b, a ≠ b ∧ 0 < physicalGap chores μ (allocation z) a b ∧
      Lambda / 8 * (μ a).real (residue z) ≤ physicalGap chores μ (allocation z) a b} by
    exact hG.inter hp
  simp_rw [ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  have hgap : Measurable (fun z => physicalGap chores μ (allocation z) a b) :=
    signedGap_measurable chores (fun z i j => (μ i).real (allocation z j)) hallocation a b
  by_cases hab : a = b
  · simp only [hab, ne_eq, not_true_eq_false, false_and, ofPred_false]
    exact MeasurableSet.empty
  · have hgood : MeasurableSet {z | 0 < physicalGap chores μ (allocation z) a b ∧
        Lambda / 8 * (μ a).real (residue z) ≤ physicalGap chores μ (allocation z) a b} :=
      (measurableSet_lt (measurable_const : Measurable (fun _ : Ω => (0 : ℝ))) hgap).inter
        (measurableSet_le ((measurable_const : Measurable (fun _ : Ω => Lambda / 8)).mul (hresidue a)) hgap)
    simpa only [ne_eq, hab, not_false_eq_true, true_and] using hgood

/-- Concrete contrast-preservation lemma, including its stated whole-trial
constant. The only probability input besides the fresh-tape projection law
is the already proved whole-trial Repair failure bound. -/
theorem original_trial_physical_margin (hk : 2 ≤ k) (chores : Bool)
    (P : Measure X) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (projection : Ω → X × IsolationDraw k L)
    (hprojection : MeasurePreserving projection Q (P.prod (isolationLaw k L)))
    (w : X → Job k → Fin L → Fin k → ℝ) (old : X → Fin k → Fin k → ℝ)
    (chosen : X → Selection k) (hw : ∀ j a i, Measurable (fun x => w x j a i))
    (hchosen : Measurable chosen)
    (μ : Fin k → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (buffer : Set ℝ) (reserve residue : Ω → Set ℝ) (allocation : Ω → Fin k → Set ℝ)
    (pi : Ω → Equiv.Perm (Fin k)) (t : Ω → Fin k → ℝ) (e : Ω → Fin k → Fin k → ℝ)
    (G : Set Ω) (hfailure : Q.real Gᶜ < 1 / 64)
    (hvalues : ∀ z ∈ G, ∀ i j, normalizedValues μ (reserve z) (allocation z) i j =
      paid (coreMatrix hk (w (projection z).1) (old (projection z).1) (projection z).2.1 (projection z).2.2)
        (pi z) (t z) i j + e z i j)
    (herr : ∀ z ∈ G, ∀ i j, |e z i j| ≤ signedGap chores (normalizedValues μ (reserve z) (allocation z)) i j)
    (Lambda theta : ℝ) (hLambda : 0 < Lambda) (htheta : 0 < theta)
    (hold : ∀ z ∈ G, Lambda / theta ≤ contrast (old (projection z).1)
      (chosen (projection z).1).1.1 (chosen (projection z).1).1.2 (chosen (projection z).1).2.1 (chosen (projection z).1).2.2)
    (hbuffer : ∀ i, 0 < (μ i).real buffer)
    (hreserve : ∀ z ∈ G, ∀ i, theta / 2 * (μ i).real buffer ≤ (μ i).real (reserve z))
    (hresidue : ∀ z ∈ G, residue z ⊆ buffer) :
    31 / 64 < Q.real {z | z ∈ G ∧ ∃ a b, a ≠ b ∧ 0 < physicalGap chores μ (allocation z) a b ∧
      Lambda / 8 * (μ a).real (residue z) ≤ physicalGap chores μ (allocation z) a b} := by
  have hp := original_trial_preservation_strict hk P Q projection hprojection w old chosen hw hchosen G hfailure
  apply hp.trans_le
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  obtain ⟨a, b, hab, hpositive, hmargin, _⟩ := exists_physical_margin (by omega) chores μ buffer
    (reserve z) (residue z) (allocation z)
    (coreMatrix hk (w (projection z).1) (old (projection z).1) (projection z).2.1 (projection z).2.2)
    (e z) (pi z) (t z) (hvalues z hz.1) (herr z hz.1)
    (chosen (projection z).1).1.1 (chosen (projection z).1).1.2
    (chosen (projection z).1).2.1 (chosen (projection z).1).2.2 Lambda theta hLambda htheta
    ((hold z hz.1).trans hz.2) hbuffer (hreserve z hz.1) (hresidue z hz.1)
  exact ⟨hz.1, a, b, hab, hpositive, hmargin⟩

end EnvyFreeResearch.Full.UpperSnapshotContrast
