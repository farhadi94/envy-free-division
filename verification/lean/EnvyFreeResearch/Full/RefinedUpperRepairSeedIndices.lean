import EnvyFreeResearch.Full.RefinedUpperPreparationPackages
import EnvyFreeResearch.Full.UpperRepairResidue

/-! Pure logical indices for the actual permuted threshold seeds. These
indices connect recorded package states to full-buffer complement filtering. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairSeedIndices

open UpperRecordedDomain UpperCorrectionExecution UpperLogicalPreparation UpperLogicalIsolation RefinedUpperPreparation
  UpperRepairJobs UpperSeedMatrix UpperBatchPermutation UpperCircularStage UpperStageMeasurable UpperLogicalCells

variable {n k coarse fine : ℕ}

def indices (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) : Finset (Fin (coarse + fine + 1)) :=
  seedIndices (dataChosen active origin data L (permuteJob pi (jobEquiv hk j)))
    (difference (system hk (permutedWeights (dataWeights active origin data L) pi)) j) (threshold j)

theorem dataSeedState_eq_retain (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) :
    dataSeedState hk active origin data L pi threshold j =
      retain (UpperGridData.aligned data) (UpperGridData.cuts data)
        (indices hk active origin data L pi threshold j) := rfl

set_option maxHeartbeats 500000 in
theorem indices_measurable {X : Type} [MeasurableSpace X] (hk : 2 ≤ k) (active : Fin k → Fin n)
    (origin : X → State n) (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (horigin : Measurable origin) (hdata : Measurable data)
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j))
    (j : Fin (jobCount k - 1 + 1)) :
    Measurable (fun x => indices hk active (origin x) (data x) L (pi x) (threshold x) j) := by
  have hfixed (t : Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) :
      Measurable (fun x => indices hk active (origin x) (data x) L t.1 t.2 j) := by
    apply seedIndices_measurable
    · exact dataChosen_measurable active origin data L horigin hdata _
    · intro a
      exact (dataWeights_measurable active origin data L horigin hdata _ a _).sub
        (dataWeights_measurable active origin data L horigin hdata _ a _)
    · exact measurable_const
  have hall : Measurable (fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
      indices hk active (origin p.1) (data p.1) L p.2.1 p.2.2 j) :=
    measurable_from_prod_countable_left
      (f := fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
        indices hk active (origin p.1) (data p.1) L p.2.1 p.2.2 j) hfixed
  convert hall.comp (measurable_id.prodMk (hpi.prodMk (Measurable.of_eval hthreshold))) using 1
  funext x
  rfl

variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem selected_seed (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    selectedUnion (cell (domain (UpperGridData.aligned data).cells) (UpperGridData.cuts data))
      (indices hk active origin data L pi threshold j) =
      domain (dataSeedState hk active origin data L pi threshold j).cells := by
  dsimp only
  rw [dataSeedState_eq_retain, retain_domain]
  · exact (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  · exact UpperCommonGrid.grid_monotone _
  · exact UpperGridCache.aligned_separated policy active origin q m draw

def reserved (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) : Finset (Fin (coarse+fine+1)) :=
  reserveCells (UpperGridData.parent data) 0 (retentionLabels (dataResult active origin data L).2)

omit hpolicy hgood hpositive in
lemma reserved_measurable {X : Type} [MeasurableSpace X]
    (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (ho : Measurable origin) (hd : Measurable data) :
    Measurable (fun x => reserved active (origin x) (data x) L) := by
  apply reserveCells_measurable _ 0 _ (UpperGridData.parent_measurable data hd)
  intro p
  exact (measurable_of_countable (fun removed => retentionLabels removed p)).comp
    (measurable_snd.comp (dataResult_measurable active origin data L ho hd))

theorem selected_reserve (q m L : ℕ) (draw : Fin m → Fin k × I) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    selectedUnion (cell (domain (UpperGridData.aligned data).cells) (UpperGridData.cuts data))
      (reserved active origin data L) = domain (dataRetained active origin data L).cells := by
  dsimp only
  rw [reserved,dataRetained,UpperGridData.reserve,retain_domain]
  · exact (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  · exact UpperCommonGrid.grid_monotone _
  · exact UpperGridCache.aligned_separated policy active origin q m draw

end EnvyFreeResearch.Full.RefinedUpperRepairSeedIndices
