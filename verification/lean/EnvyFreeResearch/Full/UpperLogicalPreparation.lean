import EnvyFreeResearch.Full.UpperLogicalPreparationFrozen
import EnvyFreeResearch.Full.UpperLogicalPreparationIndexed
import EnvyFreeResearch.Full.UpperLogicalPreparationSeeds

/-!
# Logical preparation for the recorded randomized correction stage

The façade assembles actual representative-loop completion, repeated indexed
witnesses, literal seed unions, and the full-history labelled reserve. The
sampling buffer and frozen error reserve remain distinct physical domains.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRecordedQuantiles UpperCommonGrid UpperRepresentativeSupply UpperWitnessExtraction Chores

variable {n M L : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

/-- The actual representative computation on the recorded sampled grid. -/
def representativeRun (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent)) :=
  UpperRepresentativeSupply.run (UpperGridCache.table policy active origin q m draw)
    (UpperRecordedParents.parent policy active origin q m draw)
    (List.ofFn (fun i : Fin (count (Agent := Agent) q + m + 1) => i)) jobs ∅

theorem representativeRun_measurable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (active : Agent → Fin n)
    (q m : ℕ) (jobs : List (Agent × Agent)) :
    Measurable (fun p : State n × (Fin m → Agent × I) => representativeRun policy active p.1 q m p.2 jobs) :=
  table_run_measurable _ (UpperRecordedParents.parent_measurable policy hpolicy active q m)
    _ jobs _ (UpperGridCache.table_measurable policy hpolicy active q m) _ measurable_const

/-- The actual cache and actual parent map produce all repeated witnesses.
For every later reserve normalization the chosen logical cells are physically
disjoint, and the selected-parent label test gives their quantitative gap. -/
theorem recorded_representatives (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I)
    (jobs : Fin (M + 1) → Agent × Agent) (column : Fin (M + 1) → Agent)
    (hbudget : (2 * ((M + 1) * L) : ℕ) < q + 1) :
    let values := UpperGridCache.table policy active origin q m draw
    let parent := UpperRecordedParents.parent policy active origin q m draw
    let cells := List.ofFn (fun i : Fin (count (Agent := Agent) q + m + 1) => i)
    let fine := UpperGridMerge.logicalCells policy active origin q m draw
    ∃ pairs final,
      UpperRepresentativeSupply.run values parent cells (roundJobs (repeatedJobs (L := L) jobs)) ∅ = some (pairs, final) ∧
      pairs.length = Fintype.card (Fin (M + 1) × Fin L) ∧
      final.card ≤ 2 * ((M + 1) * L) ∧
      ∀ normalizer : Agent → ℝ,
        Seeds.DisjointCells (witnessCells (L := L) fine values normalizer jobs pairs 0) ∧
        ∀ theta labels, (∀ p ∈ final, ¬labels p ≤ theta) → ∀ (j : Fin (M + 1)) (a : Fin L),
          reserveGap values normalizer (reserveCells parent theta labels) (jobs j).1 (jobs j).2 / 3 ≤
            |UpperSeedMatrix.difference (witnessSystem (L := L) values normalizer jobs column pairs 0) j a| := by
  dsimp only
  have hb : (((∅ : Finset (Fin (count (Agent := Agent) q + 1))).card +
      2 * (roundJobs (repeatedJobs (L := L) jobs)).length : ℕ) : ℝ) * (1 / (q + 1 : ℝ)) < 1 := by
    simp only [Finset.card_empty, zero_add, roundJobs, List.length_ofFn, Fintype.card_prod, Fintype.card_fin,
      mul_one_div]
    apply (div_lt_one (by positivity : (0 : ℝ) < q + 1)).mpr
    exact_mod_cast hbudget
  obtain ⟨pairs, final, hexec, hlength, _, hcard⟩ := recorded_run_completes μ policy hpolicy active origin hgood hpositive
    q m draw (roundJobs (repeatedJobs (L := L) jobs)) ∅ hb
  have hl : pairs.length = Fintype.card (Fin (M + 1) × Fin L) := by
    simpa only [roundJobs, List.length_ofFn] using hlength
  refine ⟨pairs, final, hexec, hl, ?_, ?_⟩
  · simpa only [Finset.card_empty, zero_add, roundJobs, List.length_ofFn, Fintype.card_prod, Fintype.card_fin] using hcard
  · intro normalizer
    refine ⟨?_, ?_⟩
    · exact witnessCells_disjoint _ _ _
        (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw) normalizer _ _
        (UpperRecordedParents.cell_subset_parent μ policy hpolicy active origin hgood hpositive q m draw)
        (UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q).1
        jobs ∅ pairs final hexec hl 0
    · intro theta labels hpass j a
      exact witnessSystem_gap _
        (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw) normalizer _ _
        (fun c => List.mem_ofFn.mpr ⟨c, rfl⟩) jobs column ∅ pairs final hexec hl 0 theta labels hpass j a

end EnvyFreeResearch.Full.UpperLogicalPreparation
