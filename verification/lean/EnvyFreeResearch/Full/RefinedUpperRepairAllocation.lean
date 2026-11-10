import EnvyFreeResearch.Full.RefinedUpperPreparationPackages
import EnvyFreeResearch.Full.RefinedUpperRepairFinalCacheValues

/-! The actual assignment permutation joins whole recorded old-plus-seed
packages to the exact corrected payments. No valuation query is added. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairAllocation

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperPreparation UpperRepairJobs UpperComponentAssembly RefinedUpperRepairFinalCache

variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

def assignment (chores : Bool) (V : Fin k → Fin k → ℝ) : Equiv.Perm (Fin k) :=
  if chores then UpperAssignment.minimize V else UpperAssignment.maximize V

def allocation (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (result : RefinedUpperRepairFinalCache.Result n k) (j : Fin k) : State n :=
  join (RefinedUpperPreparation.packages hk active origin old data L pi threshold
    (assignment chores (dataMatrix hk active origin old data L pi threshold) j))
    (paymentState result j) result.2.1.history

theorem allocation_domain (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (result : RefinedUpperRepairFinalCache.Result n k) (j : Fin k) :
    domain (allocation hk chores active origin old data L pi threshold result j).cells =
      domain (RefinedUpperPreparation.packages hk active origin old data L pi threshold
        (assignment chores (dataMatrix hk active origin old data L pi threshold) j)).cells ∪
      domain (result.1 j) := by
  rw [allocation, join_domain, paymentState_domain]

theorem allocation_history (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (result : RefinedUpperRepairFinalCache.Result n k) (j : Fin k) :
    (allocation hk chores active origin old data L pi threshold result j).history = result.2.1.history := rfl

section Measurability
variable {X : Type} [MeasurableSpace X]

theorem assignment_measurable (chores : Bool) (V : X → Fin k → Fin k → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) : Measurable (fun x => assignment chores (V x)) := by
  cases chores
  · exact UpperAssignment.maximize_measurable V hV
  · exact UpperAssignment.minimize_measurable V hV

theorem allocation_measurable (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (data : X → UpperGridData.Data n coarse fine)
    (L : ℕ) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1)) (result : X → RefinedUpperRepairFinalCache.Result n k)
    (horigin : Measurable origin) (hold : ∀ c, Measurable (fun x => old x c)) (hdata : Measurable data)
    (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (hresult : Measurable result) (j : Fin k) :
    Measurable (fun x => allocation hk chores active (origin x) (old x) (data x) L
      (pi x) (threshold x) (result x) j) := by
  have hpack : Measurable (fun p : X × Fin k => RefinedUpperPreparation.packages hk active (origin p.1)
      (old p.1) (data p.1) L (pi p.1) (threshold p.1) p.2) :=
    measurable_from_prod_countable_left (fun c =>
      RefinedUpperPreparation.packages_measurable hk active origin old data L pi threshold
        horigin hold hdata hpi hthreshold c)
  have hassign := assignment_measurable chores _
    (dataMatrix_measurable hk active origin old data L pi threshold horigin hold hdata hpi hthreshold)
  have hindex : Measurable (fun x => assignment chores (dataMatrix hk active (origin x) (old x)
      (data x) L (pi x) (threshold x)) j) :=
    (measurable_of_countable (fun p : Equiv.Perm (Fin k) => p j)).comp hassign
  exact join_measurable _ _ _ (hpack.comp (measurable_id.prodMk hindex))
    (paymentState_measurable result hresult j)
    (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp hresult)))

end Measurability

end EnvyFreeResearch.Full.RefinedUpperRepairAllocation
