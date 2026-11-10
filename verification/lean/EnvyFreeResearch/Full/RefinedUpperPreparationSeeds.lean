import EnvyFreeResearch.Full.RefinedUpperPreparationPhysical
import EnvyFreeResearch.Full.UpperLogicalIsolationSeedState

/-! Physical threshold seeds built from the new maximum-determinant preparation. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperStageMeasurable UpperRepairJobs UpperSeedMatrix UpperBatchPermutation Chores
variable {n k coarse fine L : ℕ}

def dataSeedState (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) : State n :=
  seedState (UpperGridData.aligned data) (UpperGridData.cuts data)
    (dataChosen active origin data L (UpperLogicalIsolation.permuteJob pi (jobEquiv hk j)))
    (difference (system hk (permutedWeights (dataWeights active origin data L) pi)) j) (threshold j)

theorem dataSeedState_history (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (j : Fin (jobCount k - 1 + 1)) :
    (dataSeedState hk active origin data L pi threshold j).history = data.2.2.history := rfl

variable {X : Type*} [MeasurableSpace X]

theorem dataSeedState_measurable (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (pi : X → Equiv.Perm (Fin k)) (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (horigin : Measurable origin) (hdata : Measurable data)
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j))
    (j : Fin (jobCount k - 1 + 1)) :
    Measurable (fun x => dataSeedState hk active (origin x) (data x) L (pi x) (threshold x) j) := by
  have hfixed (t : Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) :
      Measurable (fun x => dataSeedState hk active (origin x) (data x) L t.1 t.2 j) := by
    apply seedState_measurable
    · exact UpperGridData.aligned_measurable data hdata
    · exact fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata)
    · intro a
      exact dataChosen_measurable active origin data L horigin hdata _ a
    · intro a
      exact (dataWeights_measurable active origin data L horigin hdata _ a _).sub
        (dataWeights_measurable active origin data L horigin hdata _ a _)
    · exact measurable_const
  have hall : Measurable (fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
      dataSeedState hk active (origin p.1) (data p.1) L p.2.1 p.2.2 j) :=
    measurable_from_prod_countable_left
      (f := fun p : X × (Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))) =>
        dataSeedState hk active (origin p.1) (data p.1) L p.2.1 p.2.2 j) hfixed
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
    (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    WellFormed μ (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
      L pi threshold j) :=
  seedState_wellFormed μ _ (UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw) _ _ _ _

theorem dataSeedState_domain (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
      L pi threshold j).cells =
      Seeds.seed (seedSystem hk policy active origin q m L draw pi)
        (seedCells hk policy active origin q m L draw pi) threshold j := by
  unfold dataSeedState
  rw [UpperGridData.aligned_execute, UpperGridData.cuts_execute,
    seedState_domain _ _ (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
      (UpperCommonGrid.grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw),
    UpperGridCache.aligned_domain]
  rfl

end Correctness
end EnvyFreeResearch.Full.RefinedUpperPreparation
