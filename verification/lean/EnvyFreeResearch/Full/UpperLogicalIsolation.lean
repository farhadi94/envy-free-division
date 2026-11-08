import EnvyFreeResearch.Full.UpperLogicalIsolationOriginal
import EnvyFreeResearch.Full.UpperLogicalIsolationTargets
import EnvyFreeResearch.Full.UpperLogicalIsolationSeedState

/-!
# Actual logical preparation to seed isolation and ideal payments

All finite selectors use recorded caches. Their pure `UpperGridData.Data`
forms do not invoke a policy. Physical package values, original-law cycle
bounds, target budgets, and successful-branch ideal inequalities are proved.
-/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperRepairJobs UpperIdealPayments UpperAssignment UpperSeedMatrix
variable {n k : ℕ}

theorem dataMatrix_execute [Nonempty (Fin k)] (hk : 2 ≤ k) (policy : Policy n)
    (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n) (q m L : ℕ)
    (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    dataMatrix hk active origin old (UpperGridMerge.prepare policy active origin q m draw) L theta labels pi threshold =
      cachedMatrix hk policy active origin old q m L draw theta labels pi threshold := by
  unfold dataMatrix cachedMatrix coreMatrix seedSystem
  rw [dataWeights_execute, UpperGridData.reserve_execute]

theorem cycleReject_eq_false (chores : Bool) (V A : Fin k → Fin k → ℝ) (lam : ℝ) :
    cycleReject chores V A lam = false ↔ findPositive (signedTable chores V) A lam = none := by
  simp only [cycleReject, decide_eq_false_iff_not, not_not]

/-- The computed cake potentials satisfy the ideal inequalities on the
actual accepting finite-search branch. -/
theorem actual_cake_ideal (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (lam : ℝ)
    (haccept : cycleReject false (cachedMatrix hk policy active origin old q m L draw theta labels pi threshold)
      (disagreement policy active origin q m draw theta labels) lam = false) (i j : Fin k) :
    let V := cachedMatrix hk policy active origin old q m L draw theta labels pi threshold
    let A := disagreement policy active origin q m draw theta labels
    2 * lam * A i j ≤ V i (maximize V i) + cakeTargets V A lam i - V i (maximize V j) - cakeTargets V A lam j := by
  exact cake_ideal_inequalities _ _ lam (UpperPayments.cellGap_diagonal _)
    ((cycleReject_eq_false _ _ _ _).mp haccept) i j

/-- The computed shifted chore potentials satisfy the reverse ideal
inequalities on the actual accepting finite-search branch. -/
theorem actual_chore_ideal (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (lam : ℝ)
    (haccept : cycleReject true (cachedMatrix hk policy active origin old q m L draw theta labels pi threshold)
      (disagreement policy active origin q m draw theta labels) lam = false) (i j : Fin k) :
    let V := cachedMatrix hk policy active origin old q m L draw theta labels pi threshold
    let A := disagreement policy active origin q m draw theta labels
    2 * lam * A i j ≤ V i (minimize V j) + choreTargets V A lam (cellCap q theta) j -
      V i (minimize V i) - choreTargets V A lam (cellCap q theta) i := by
  exact chore_ideal_inequalities _ _ lam _ (UpperPayments.cellGap_diagonal _)
    ((cycleReject_eq_false _ _ _ _).mp haccept) i j

def dataTargets (hk : 2 ≤ k) (q : ℕ) (chores : Bool) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) {coarse fine : ℕ} (data : UpperGridData.Data n coarse fine)
    (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (lam : ℝ) : Fin k → ℝ :=
  if chores then choreTargets (dataMatrix hk active origin old data L theta labels pi threshold)
    (dataDisagreement active data theta labels) lam (cellCap q theta)
  else cakeTargets (dataMatrix hk active origin old data L theta labels pi threshold)
    (dataDisagreement active data theta labels) lam

/-- Both target orientations depend only on the returned recorded grid,
old cache snapshots and finite fresh randomness; all real coordinates are
Borel, including every optimizing assignment and path tie. -/
theorem dataTargets_measurable {X : Type*} [MeasurableSpace X] {coarse fine : ℕ}
    (hk : 2 ≤ k) (q : ℕ) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (data : X → UpperGridData.Data n coarse fine)
    (L : ℕ) (theta : I) (labels : X → Fin (coarse + 1) → I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1)) (lam : ℝ)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hdata : Measurable data)
    (hlabels : ∀ p, Measurable (fun x => labels x p)) (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (i : Fin k) :
    Measurable (fun x => dataTargets hk q chores active (origin x) (old x) (data x)
      L theta (labels x) (pi x) (threshold x) lam i) := by
  have hV := dataMatrix_measurable hk active origin old data L theta labels pi threshold
    horigin hold hdata hlabels hpi hthreshold
  have hA := dataDisagreement_measurable active data theta labels hdata hlabels
  cases chores
  · exact UpperIdealMeasurable.cakeTargets_measurable _ _ _ hV hA measurable_const i
  · exact UpperIdealMeasurable.choreTargets_measurable _ _ _ _ hV hA measurable_const measurable_const i

/-- The explicit parameter check used by Repair converts the proved target
budget into its required strict total budget. -/
theorem total_targets_small (t : Fin k → ℝ) (budget : ℝ)
    (ht : ∑ i, t i ≤ k * budget) (hbudget : (k : ℝ) * budget < 1 / 16) :
    ∑ i, t i < 1 / 16 := ht.trans_lt hbudget

end EnvyFreeResearch.Full.UpperLogicalIsolation
