import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperRepairAllocation

/-! The actual Repair construction preserves each old bundle as a whole.
The receiving permutation and additional recorded pieces are explicit.
This property holds for every execution data value, before any acceptance
hypothesis; disjointness and truthful caches are supplied by success proofs. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperPreparation UpperRepairJobs UpperComponentAssembly RefinedUpperRepairFinalCache
  RefinedUpperRepairAllocation
variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

/-- The receiver of old label j is the inverse of the actual assignment. -/
def receiver (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) : Equiv.Perm (Fin k) :=
  (assignment chores (dataMatrix hk active origin old data L pi threshold)).symm

/-- Additions associated with an old label, computed from actual recorded
seed states and the correction payments at its actual receiver. -/
def additions (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (result : RefinedUpperRepairFinalCache.Result n k) (j : Fin k) : State n :=
  join (group (dataSeedState hk active origin data L pi threshold)
    (fun a => (jobEquiv hk a).2) j data.2.2.history)
    (paymentState result (receiver hk chores active origin old data L pi threshold j))
    result.2.1.history

theorem whole_label_identity (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (result : RefinedUpperRepairFinalCache.Result n k) (j : Fin k) :
    domain (allocation hk chores active origin old data L pi threshold result
      (receiver hk chores active origin old data L pi threshold j)).cells =
    domain (old j).cells ∪
      domain (additions hk chores active origin old data L pi threshold result j).cells := by
  simp only [allocation, join_domain, RefinedUpperPreparation.packages,
    UpperComponentAssembly.packages, receiver, Equiv.apply_symm_apply, additions]
  exact union_assoc _ _ _

theorem old_subset_output (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (result : RefinedUpperRepairFinalCache.Result n k) (j : Fin k) :
    domain (old j).cells ⊆
    domain (allocation hk chores active origin old data L pi threshold result
      (receiver hk chores active origin old data L pi threshold j)).cells := by
  rw [whole_label_identity]
  exact subset_union_left

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
