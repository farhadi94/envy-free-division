import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunTermination

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperExpectedRuntime
variable {n : ℕ}

def paidCount (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) : ℝ≥0∞ :=
  ∑ kind, attempts (paidEvent policy fallback chores initial kind) omega

theorem allPaid_count_le (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n)) :
    attempts (allPaidEvent policy fallback chores initial) omega ≤
      paidCount policy fallback chores initial omega := by
  unfold attempts paidCount
  calc
    _ ≤ ∑' t, ∑' kind, (paidEvent policy fallback chores initial kind t).indicator (fun _ => (1:ℝ≥0∞)) omega := by
      apply ENNReal.tsum_le_tsum
      intro t
      by_cases h : omega ∈ allPaidEvent policy fallback chores initial t
      · have hh : omega ∈ allPaidEvent policy fallback chores initial t := h
        obtain ⟨kind,hkind⟩ := h
        rw [Set.indicator_of_mem hh]
        have hl := ENNReal.le_tsum (f := fun kind =>
          (paidEvent policy fallback chores initial kind t).indicator (fun _ => (1:ℝ≥0∞)) omega) kind
        simpa only [Set.indicator_of_mem hkind] using hl
      · rw [Set.indicator_of_notMem h]
        exact zero_le
    _ = ∑' kind, ∑' t, (paidEvent policy fallback chores initial kind t).indicator (fun _ => (1:ℝ≥0∞)) omega :=
      ENNReal.tsum_comm
    _ = _ := tsum_fintype _

theorem unfinished_total_count_infinite (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n))
    (hnever : ¬ finishedRun policy fallback chores initial omega) :
    paidCount policy fallback chores initial omega=∞ := by
  apply top_unique
  rw [←unfinished_paid_count_infinite policy fallback chores initial omega hnever]
  exact allPaid_count_le policy fallback chores initial omega

theorem terminates_of_paid_mean (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (law : Measure (Stream (Universal n)))
    (hevent : ∀ kind t, MeasurableSet (paidEvent policy fallback chores initial kind t))
    (bound : ℝ≥0∞) (hfinite : bound ≠ ∞)
    (hmean : (∫⁻ omega, paidCount policy fallback chores initial omega ∂law) ≤ bound) :
    ∀ᵐ omega ∂law, finishedRun policy fallback chores initial omega := by
  apply terminates_of_infinite_paid law (paidCount policy fallback chores initial)
    (Finset.measurable_sum _ (fun kind _ => attempts_measurable _ (hevent kind)))
    (finishedRun policy fallback chores initial) bound hfinite hmean
  exact unfinished_total_count_infinite policy fallback chores initial

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
