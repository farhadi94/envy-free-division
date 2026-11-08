import EnvyFreeResearch.Full.UpperLogicalIsolationGap

/-!
# Actual cached inputs for logical seed isolation

The representative result is read by total finite operations. All row scales
come from recorded old-buffer and reserve totals, and the disagreement is
exactly the existing correction-table maximum.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalIsolation

open UpperLogicalPreparation UpperLogicalPreparationGuard UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperWitnessExtraction UpperRepairJobs
  UpperRepresentativeSupply Chores

variable {n k L : ℕ}

abbrev Fine (k q m : ℕ) := Fin (count (Agent := Fin k) q + m + 1)
abbrev Parent (k q : ℕ) := Fin (count (Agent := Fin k) q + 1)
abbrev Round (k L : ℕ) := Job k × Fin L

def requests (k L : ℕ) : List (Fin k × Fin k) :=
  roundJobs (UpperPreparedIsolation.rows (k := k) (L := L))

theorem requests_length (k L : ℕ) : (requests k L).length = jobCount k * L := by
  simp only [requests, roundJobs, List.length_ofFn]
  rw [Fintype.card_prod, job_card, Fintype.card_fin]

def representativePairs (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) : List (Fine k q m × Fine k q m) :=
  match representativeRun policy active origin q m draw (requests k L) with
  | none => []
  | some result => result.1

def chosenCell (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I)
    (job : Job k) (a : Fin L) : Fine k q m :=
  picked (UpperGridCache.table policy active origin q m draw)
    (multipliers active origin (reserveState policy active origin q m draw theta labels))
    UpperPreparedIsolation.rows (representativePairs policy active origin q m L draw) 0 (job, a)

def weights (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I)
    (job : Job k) (a : Fin L) (i : Fin k) : ℝ :=
  multipliers active origin (reserveState policy active origin q m draw theta labels) i *
    UpperGridCache.table policy active origin q m draw i (chosenCell policy active origin q m L draw theta labels job a)

def disagreement (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I) : Fin k → Fin k → ℝ :=
  UpperPayments.cellGap (UpperCorrectionSetup.table active (reserveState policy active origin q m draw theta labels)
    (UpperGridMerge.cuts policy active origin q m draw))

def oldMatrix (active : Fin k → Fin n) (old : Fin k → State n) (reserve : State n) (i j : Fin k) : ℝ :=
  total (old j) (active i) / total reserve (active i)

section Correctness

variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

/-- The list read by `chosenCell` is the actual complete returned list. -/
theorem representativePairs_spec (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1) :
    ∃ final, representativeRun policy active origin q m draw (requests k L) =
      some (representativePairs policy active origin q m L draw, final) ∧
      (representativePairs policy active origin q m L draw).length = Fintype.card (Round k L) ∧
      final = selectedParents policy active origin q m draw (requests k L) := by
  have hb : (((∅ : Finset (Parent k q)).card + 2 * (requests k L).length : ℕ) : ℝ) * (1 / (q + 1 : ℝ)) < 1 := by
    simp only [Finset.card_empty, zero_add, requests_length, mul_one_div]
    apply (div_lt_one (by positivity : (0 : ℝ) < q + 1)).mpr
    exact_mod_cast hbudget
  obtain ⟨pairs, final, hexec, hlength, _, _⟩ := recorded_run_completes μ policy hpolicy active origin hgood hpositive
    q m draw (requests k L) ∅ hb
  have hr : representativeRun policy active origin q m draw (requests k L) = some (pairs, final) := hexec
  have hp : representativePairs policy active origin q m L draw = pairs := by simp only [representativePairs, hr]
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa only [hp] using hr
  · rw [hp]
    simpa only [requests, roundJobs, List.length_ofFn] using hlength
  · exact (selectedParents_eq policy active origin q m draw (requests k L) pairs final hr).symm

/-- Passing the actual guard proves the witness-gap input of both isolation
theorems against the actual correction-table disagreement. -/
theorem weights_gap (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1) (theta : I) (cap : ℝ) (labels : Parent k q → I)
    (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true)
    (job : Job k) (a : Fin L) :
    disagreement policy active origin q m draw theta labels job.1.1.1 job.1.1.2 / 3 ≤
      |weights policy active origin q m L draw theta labels job a job.1.1.1 -
        weights policy active origin q m L draw theta labels job a job.1.1.2| := by
  obtain ⟨final, hexec, hlength, hfinal⟩ := representativePairs_spec μ policy hpolicy active origin hgood hpositive q m L draw hbudget
  have hp := ((guard_eq_true policy active origin q m (requests k L) theta cap draw labels).mp hpass).2.2
  rw [← hfinal] at hp
  rw [disagreement, reserve_cellGap μ policy hpolicy active origin hgood hpositive]
  exact picked_controls_reserve _ (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw)
    _ _ _ UpperPreparedIsolation.rows ∅ _ final hexec hlength 0 _
    (fun c hc => ⟨List.mem_ofFn.mpr ⟨c, rfl⟩, fun hf => hp _ hf (Finset.mem_filter.mp hc).2⟩) (job, a)

omit [Nonempty (Fin k)] in
/-- Actual normalized witness mass, including witnesses outside the reserve.
The immutable cache snapshots supply both normalization constants. -/
theorem weights_physical (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (job : Job k) (a : Fin L) (i : Fin k) :
    weights policy active origin q m L draw theta labels job a i =
      (μ (active i)).real (UpperGridMerge.logicalCells policy active origin q m draw
        (chosenCell policy active origin q m L draw theta labels job a)) /
      (μ (active i)).real (domain (reserveState policy active origin q m draw theta labels).cells) := by
  unfold weights multipliers
  rw [total_correct μ origin hgood,
    total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels),
    UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive]
  field_simp [(hpositive i).ne']

omit [Nonempty (Fin k)] in
theorem oldMatrix_physical (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (q m : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I) (i j : Fin k) :
    oldMatrix active old (reserveState policy active origin q m draw theta labels) i j =
      (μ (active i)).real (domain (old j).cells) /
        (μ (active i)).real (domain (reserveState policy active origin q m draw theta labels).cells) := by
  rw [oldMatrix, total_correct μ (old j) (hold j),
    total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels)]

end Correctness

end EnvyFreeResearch.Full.UpperLogicalIsolation
