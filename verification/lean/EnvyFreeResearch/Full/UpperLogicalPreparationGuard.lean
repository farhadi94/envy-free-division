import EnvyFreeResearch.Full.UpperLogicalPreparationGuardProbability

/-! Original-tape preparation guard for the complete repeated-witness stage. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalPreparationGuard

open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperStageMeasurable UpperRecordedQuantiles UpperWitnessExtraction Chores

variable {n M L : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

/-- The combined preparation rejection bound on the original fine sampler
and independent parent-label tape, with the manuscript's exact three terms. -/
theorem repeated_original_failure_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (jobs : Fin (M + 1) → Agent × Agent)
    (hbudget : 2 * ((M + 1) * L) < q + 1) (hgrid : count (Agent := Agent) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap) :
    originalLaw q m {p | guard policy active origin q m (roundJobs (repeatedJobs (L := L) jobs)) theta cap p.1 p.2 = false} ≤
      ENNReal.ofReal (4 * Fintype.card Agent / ((theta : ℝ) * (q + 1 : ℝ)) +
        2 * (theta : ℝ) * m / cap + 2 * ((M + 1) * L) * (theta : ℝ)) := by
  simpa only [failureBudget, roundJobs, List.length_ofFn, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    original_tape_failure_probability μ policy hpolicy hmeas active origin hgood hpositive q m
      (roundJobs (repeatedJobs (L := L) jobs))
      (by simpa only [roundJobs, List.length_ofFn, Fintype.card_prod, Fintype.card_fin] using hbudget)
      hgrid theta htheta cap hcap

/-- Passing the actual Boolean guard supplies actual returned witnesses with
physical disjointness from one another and from the final recorded reserve,
and their quantitative gap after any reserve-dependent normalization. -/
theorem passing_repeated_witnesses (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I)
    (jobs : Fin (M + 1) → Agent × Agent) (column : Fin (M + 1) → Agent)
    (hbudget : 2 * ((M + 1) * L) < q + 1)
    (theta : I) (cap : ℝ) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : guard policy active origin q m (roundJobs (repeatedJobs (L := L) jobs)) theta cap draw labels = true)
    (normalizer : Agent → ℝ) :
    let values := UpperGridCache.table policy active origin q m draw
    let parent := UpperRecordedParents.parent policy active origin q m draw
    let fine := UpperGridMerge.logicalCells policy active origin q m draw
    ∃ pairs final,
      representativeRun policy active origin q m draw (roundJobs (repeatedJobs (L := L) jobs)) = some (pairs, final) ∧
      pairs.length = Fintype.card (Fin (M + 1) × Fin L) ∧
      Seeds.DisjointCells (witnessCells (L := L) fine values normalizer jobs pairs 0) ∧
      ∀ (j : Fin (M + 1)) (a : Fin L),
        reserveGap values normalizer (reserveCells parent theta labels) (jobs j).1 (jobs j).2 / 3 ≤
          |UpperSeedMatrix.difference (witnessSystem (L := L) values normalizer jobs column pairs 0) j a| ∧
        Disjoint (witnessCells (L := L) fine values normalizer jobs pairs 0 j a)
          (domain (reserveState policy active origin q m draw theta labels).cells) := by
  dsimp only
  obtain ⟨pairs, final, hexec, hlength, _, hspec⟩ :=
    recorded_representatives μ policy hpolicy active origin hgood hpositive q m draw jobs column hbudget
  have hparents := ((guard_eq_true policy active origin q m (roundJobs (repeatedJobs (L := L) jobs)) theta cap draw labels).mp hpass).2.2
  rw [selectedParents_eq policy active origin q m draw (roundJobs (repeatedJobs (L := L) jobs)) pairs final hexec] at hparents
  refine ⟨pairs, final, hexec, hlength, (hspec normalizer).1, ?_⟩
  intro j a
  exact ⟨(hspec normalizer).2 theta labels hparents j a,
    passing_witness_disjoint μ policy hpolicy active origin hgood hpositive q m draw
      (repeatedJobs (L := L) jobs) normalizer theta cap labels hpass pairs final hexec hlength (j, a)⟩

end EnvyFreeResearch.Full.UpperLogicalPreparationGuard
