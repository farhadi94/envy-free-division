import EnvyFreeResearch.Full.UpperRepairPackages
import EnvyFreeResearch.Full.UpperRepairResidue

/-! Pure logical indices for the actual permuted threshold seeds. These
indices connect recorded package states to full-buffer complement filtering. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairSeedIndices

open UpperRecordedDomain UpperCorrectionExecution UpperLogicalPreparation UpperLogicalIsolation
  UpperRepairJobs UpperSeedMatrix UpperBatchPermutation UpperCircularStage UpperStageMeasurable UpperLogicalCells

variable {n k coarse fine : ℕ}

def indices (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) : Finset (Fin (coarse + fine + 1)) :=
  seedIndices (dataChosen active origin data L theta labels (permuteJob pi (jobEquiv hk j)))
    (difference (system hk (permutedWeights (dataWeights active origin data L theta labels) pi)) j) (threshold j)

theorem dataSeedState_eq_retain (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) :
    dataSeedState hk active origin data L theta labels pi threshold j =
      retain (UpperGridData.aligned data) (UpperGridData.cuts data)
        (indices hk active origin data L theta labels pi threshold j) := rfl

set_option maxHeartbeats 500000 in
theorem indices_measurable {X : Type} [MeasurableSpace X] (hk : 2 ≤ k) (active : Fin k → Fin n)
    (origin : X → State n) (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (theta : I)
    (labels : X → Fin (coarse + 1) → I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (horigin : Measurable origin) (hdata : Measurable data) (hlabels : ∀ p, Measurable (fun x => labels x p))
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j))
    (j : Fin (jobCount k - 1 + 1)) :
    Measurable (fun x => indices hk active (origin x) (data x) L theta (labels x) (pi x) (threshold x) j) := by
  have hfixed (t : Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) :
      Measurable (fun x => indices hk active (origin x) (data x) L theta (labels x) t.1 t.2 j) := by
    apply seedIndices_measurable
    · exact dataChosen_measurable active origin data L theta labels horigin hdata hlabels _
    · intro a
      exact (dataWeights_measurable active origin data L theta labels horigin hdata hlabels _ a _).sub
        (dataWeights_measurable active origin data L theta labels horigin hdata hlabels _ a _)
    · exact measurable_const
  have hall : Measurable (fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
      indices hk active (origin p.1) (data p.1) L theta (labels p.1) p.2.1 p.2.2 j) :=
    measurable_from_prod_countable_left
      (f := fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
        indices hk active (origin p.1) (data p.1) L theta (labels p.1) p.2.1 p.2.2 j) hfixed
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
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    selectedUnion (cell (domain (UpperGridData.aligned data).cells) (UpperGridData.cuts data))
      (indices hk active origin data L theta labels pi threshold j) =
      domain (dataSeedState hk active origin data L theta labels pi threshold j).cells := by
  dsimp only
  rw [dataSeedState_eq_retain, retain_domain]
  · exact (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  · exact UpperCommonGrid.grid_monotone _
  · exact UpperGridCache.aligned_separated policy active origin q m draw

theorem selected_reserve (q m : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    selectedUnion (cell (domain (UpperGridData.aligned data).cells) (UpperGridData.cuts data))
      (reserveCells (UpperGridData.parent data) theta labels) = domain (UpperGridData.reserve data theta labels).cells := by
  dsimp only
  rw [UpperGridData.reserve, retain_domain]
  · exact (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  · exact UpperCommonGrid.grid_monotone _
  · exact UpperGridCache.aligned_separated policy active origin q m draw

end EnvyFreeResearch.Full.UpperRepairSeedIndices
