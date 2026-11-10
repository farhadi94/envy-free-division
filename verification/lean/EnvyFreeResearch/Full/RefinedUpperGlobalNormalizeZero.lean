import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolGiveAll
import EnvyFreeResearch.Full.UpperPopulationIndex
import EnvyFreeResearch.Full.RefinedUpperGlobalSinkProgram

/-! Cached zero-row preprocessing for the actual saved physical anchor. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
variable {n : ℕ}

def direction (chores : Bool) : GlobalCompletion.Direction := if chores then .chore else .cake

def pick (fallback : Fin n) (s : Finset (Fin n)) : Fin n :=
  if h : s.Nonempty then s.min' h else fallback

theorem pick_mem (fallback : Fin n) (s : Finset (Fin n)) (h : s.Nonempty) : pick fallback s ∈ s := by
  simp only [pick,dite_eq_left h]
  exact Finset.min'_mem s h

def positive (a : Anchor n) : Prop := ∀ i ∈ a.active, 0 < total a.residue i

def freezeZero (a : Anchor n) : Anchor n :=
  { a with active := positiveRows a.residue a.active }

theorem freezeZero_history (a : Anchor n) (hh : a.HistoryCompatible) :
    (freezeZero a).HistoryCompatible := hh

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem freezeZero_committed (whole : Set ℝ) (a : Anchor n) (ha : a.Committed μ .cake whole) :
    (freezeZero a).Committed μ .cake whole := by
  refine ⟨⟨ha.1.bundles_wellFormed,ha.1.residue_wellFormed,ha.1.pairwise,ha.1.separate,ha.1.cover⟩,
    ha.2.1,ha.2.2.1,ha.2.2.2.1,?_⟩
  exact cake_freeze_zeros μ a.residue ha.1.residue_wellFormed (a.table μ).value a.active
    ha.2.2.2.1 ha.2.2.2.2

theorem freezeZero_positive (whole : Set ℝ) (a : Anchor n) (ha : a.Physical μ whole) :
    positive (freezeZero a) := by
  intro i hi
  change 0 < total a.residue i
  rw [total_correct μ _ ha.residue_wellFormed]
  exact ((positiveRows_correct μ a.residue ha.residue_wellFormed a.active i).mp hi).2

theorem no_zero_positive (whole : Set ℝ) (a : Anchor n) (ha : a.Physical μ whole)
    (hz : ¬ (zeroRows a.residue a.active).Nonempty) : positive a := by
  intro i hi
  have hn : 0 ≤ total a.residue i := by rw [total_correct μ _ ha.residue_wellFormed]; exact measureReal_nonneg
  have hne : total a.residue i ≠ 0 := by
    intro he
    exact hz ⟨i,Finset.mem_filter.mpr ⟨hi,he⟩⟩
  exact lt_of_le_of_ne hn (Ne.symm hne)

theorem positiveRows_empty_cached (whole : Set ℝ) (a : Anchor n) (ha : a.Physical μ whole)
    (hz : ¬ (positiveRows a.residue a.active).Nonempty) : ∀ i ∈ a.active, total a.residue i = 0 := by
  intro i hi
  rw [total_correct μ _ ha.residue_wellFormed]
  exact positiveRows_empty_all_zero μ a.residue ha.residue_wellFormed a.active
    (Finset.not_nonempty_iff_eq_empty.mp hz) i hi

theorem terminal_history (a : Anchor n) (add : Fin n → State n) (history : UpperCircularStage.History n) :
    (terminal a add history).HistoryCompatible := commit_history _ _ _ _

end EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
