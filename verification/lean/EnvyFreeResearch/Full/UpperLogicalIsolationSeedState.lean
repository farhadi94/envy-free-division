import EnvyFreeResearch.Full.UpperLogicalIsolationPure
import EnvyFreeResearch.Full.UpperLogicalIsolationPhysical

/-! Query-free recorded seed pieces from the actual returned grid. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperStageMeasurable UpperRepairJobs UpperSeedMatrix UpperBatchPermutation UpperRepresentatives Chores
variable {n k coarse fine L : ℕ}

def dataChosen (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I) : Job k → Fin L → Fin (coarse + fine + 1) :=
  coreChosen (UpperGridData.table active origin data)
    (multipliers active origin (UpperGridData.reserve data theta labels)) (dataPairs active origin data L) 0

def dataSeedState (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) : State n :=
  seedState (UpperGridData.aligned data) (UpperGridData.cuts data)
    (dataChosen active origin data L theta labels (permuteJob pi (jobEquiv hk j)))
    (difference (system hk (permutedWeights (dataWeights active origin data L theta labels) pi)) j) (threshold j)

theorem dataSeedState_history (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) :
    (dataSeedState hk active origin data L theta labels pi threshold j).history = data.2.2.history := rfl

variable {X : Type*} [MeasurableSpace X]

theorem dataChosen_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : X → Fin (coarse + 1) → I)
    (horigin : Measurable origin) (hdata : Measurable data) (hlabels : ∀ p, Measurable (fun x => labels x p))
    (j : Job k) (a : Fin L) :
    Measurable (fun x => dataChosen active (origin x) (data x) L theta (labels x) j a) := by
  apply coreChosen_measurable
  · exact UpperGridData.table_measurable active origin data horigin hdata
  · intro r
    exact (total_measurable origin _ horigin measurable_const).div
      (total_measurable _ _ (UpperGridData.reserve_measurable data theta labels hdata hlabels) measurable_const)
  · exact dataPairs_measurable active origin data L horigin hdata

theorem dataSeedState_measurable (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : X → Fin (coarse + 1) → I)
    (pi : X → Equiv.Perm (Fin k)) (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (horigin : Measurable origin) (hdata : Measurable data) (hlabels : ∀ p, Measurable (fun x => labels x p))
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j))
    (j : Fin (jobCount k - 1 + 1)) :
    Measurable (fun x => dataSeedState hk active (origin x) (data x) L theta (labels x) (pi x) (threshold x) j) := by
  have hfixed (t : Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) :
      Measurable (fun x => dataSeedState hk active (origin x) (data x) L theta (labels x) t.1 t.2 j) := by
    apply seedState_measurable
    · exact UpperGridData.aligned_measurable data hdata
    · exact fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata)
    · intro a
      exact dataChosen_measurable active origin data L theta labels horigin hdata hlabels _ a
    · intro a
      exact (dataWeights_measurable active origin data L theta labels horigin hdata hlabels _ a _).sub
        (dataWeights_measurable active origin data L theta labels horigin hdata hlabels _ a _)
    · exact measurable_const
  have hall : Measurable (fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
      dataSeedState hk active (origin p.1) (data p.1) L theta (labels p.1) p.2.1 p.2.2 j) :=
    measurable_from_prod_countable_left
      (f := fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
        dataSeedState hk active (origin p.1) (data p.1) L theta (labels p.1) p.2.1 p.2.2 j) hfixed
  have ht : Measurable threshold := Measurable.of_eval hthreshold
  have hmap : Measurable (fun x : X => (x, (pi x, threshold x))) := measurable_id.prodMk (hpi.prodMk ht)
  convert hall.comp hmap using 1
  funext x
  rfl

section Correctness
variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem dataSeedState_wellFormed (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    WellFormed μ (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold j) :=
  seedState_wellFormed μ _ (UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw) _ _ _ _

theorem dataSeedState_domain (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold j).cells =
      Seeds.seed (seedSystem hk policy active origin q m L draw theta labels pi)
        (seedCells hk policy active origin q m L draw theta labels pi) threshold j := by
  unfold dataSeedState
  rw [UpperGridData.aligned_execute, UpperGridData.cuts_execute,
    seedState_domain _ _ (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
      (UpperCommonGrid.grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw),
    UpperGridCache.aligned_domain, dataWeights_execute]
  have hc : dataChosen active origin (UpperGridMerge.prepare policy active origin q m draw) L theta labels =
      chosenCell policy active origin q m L draw theta labels := by
    unfold dataChosen coreChosen chosenCell
    rw [UpperGridData.table_execute, UpperGridData.reserve_execute, dataPairs_execute]
  rw [hc]
  rfl

end Correctness
end EnvyFreeResearch.Full.UpperLogicalIsolation
