import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolEvents
import EnvyFreeResearch.Full.UpperTerminationProgress

/-! A concrete unfinished global run cannot stall in free normalization:
every pair of consecutive unfinished states contains an actual paid phase. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperExpectedRuntime
variable {n : ℕ}

def allPaidEvent (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (t : ℕ) : Set (Stream (Universal n)) :=
  {omega | ∃ kind, omega ∈ paidEvent policy fallback chores initial kind t}

def finishedRun (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) : Prop :=
  ∃ t, (Phase.run policy fallback chores initial t omega).finished=true

theorem normalize_paid_or_finished (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (a : Anchor n) :
    (∃ kind, (RefinedUpperGlobalNormalize.execute policy fallback chores a).paidKind=some kind) ∨
      (RefinedUpperGlobalNormalize.execute policy fallback chores a).finished=true := by
  unfold RefinedUpperGlobalNormalize.execute
  cases RefinedUpperGlobalNormalize.normalize fallback chores n a <;>
    simp [RefinedUpperGlobalNormalize.requestExecute,Phase.paidKind,Phase.finished]

theorem phase_paid_or_next_paid (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) (h : phase.finished=false)
    (hn : (phase.step policy fallback chores draw).finished=false) :
    (∃ kind,phase.paidKind=some kind) ∨
      (∃ kind,(phase.step policy fallback chores draw).paidKind=some kind) := by
  cases phase with
  | normalize a =>
    rcases normalize_paid_or_finished policy fallback chores a with ha | ha
    · exact Or.inr ha
    · have : true=false := ha.symm.trans hn
      cases this
  | snapshot a => exact Or.inl ⟨.snapshot,rfl⟩
  | firstShrink p G => exact Or.inl ⟨.shrink,rfl⟩
  | secondShrink p => exact Or.inl ⟨.shrink,rfl⟩
  | finalRepair p => exact Or.inl ⟨.repair,rfl⟩
  | done a => cases h

theorem unfinished_pair_paid (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n))
    (hnever : ¬ finishedRun policy fallback chores initial omega) (t : ℕ) :
    omega ∈ allPaidEvent policy fallback chores initial t ∨
      omega ∈ allPaidEvent policy fallback chores initial (t+1) := by
  have hfalse : ∀ j, (Phase.run policy fallback chores initial j omega).finished=false := by
    intro j
    exact Bool.eq_false_iff.mpr (fun hj => hnever ⟨j,hj⟩)
  exact phase_paid_or_next_paid policy fallback chores _ (omega t) (hfalse t) (hfalse (t+1))

theorem unfinished_paid_indices_infinite (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n))
    (hnever : ¬ finishedRun policy fallback chores initial omega) :
    {t | omega ∈ allPaidEvent policy fallback chores initial t}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro t
  rcases unfinished_pair_paid policy fallback chores initial omega hnever (t+1) with h | h
  · exact ⟨t+1,h,by omega⟩
  · exact ⟨t+1+1,h,by omega⟩

theorem unfinished_paid_count_infinite (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n))
    (hnever : ¬ finishedRun policy fallback chores initial omega) :
    attempts (allPaidEvent policy fallback chores initial) omega=∞ := by
  by_contra hfin
  have hf := ENNReal.finite_const_le_of_tsum_ne_top hfin (ε := 1) one_ne_zero
  have hs : {t | omega ∈ allPaidEvent policy fallback chores initial t}.Finite := by
    apply hf.subset
    intro t ht
    change omega ∈ allPaidEvent policy fallback chores initial t at ht
    change 1 ≤ (allPaidEvent policy fallback chores initial t).indicator (fun _ => (1:ℝ≥0∞)) omega
    rw [Set.indicator_of_mem ht]
  exact unfinished_paid_indices_infinite policy fallback chores initial omega hnever hs

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
