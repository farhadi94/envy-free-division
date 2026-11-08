import EnvyFreeResearch.Full.UpperComponentGroups
import EnvyFreeResearch.Full.UpperQueryPrograms
import EnvyFreeResearch.GlobalCompletion

/-! Literal, query-free terminal allocations for zero rows and singleton
active populations. Every original observer retains its recorded cache. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperZeroRows
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperQueryPrograms
open Chores.QueryProgram
variable {n : ℕ}

def giveAll (origin : State n) (recipient j : Fin n) : State n :=
  if j = recipient then origin else empty origin.history

def program (origin : State n) (recipient : Fin n) : QProgram n (Fin n → State n) :=
  .returned (giveAll origin recipient)

theorem program_executes (policy : AdaptiveOracle.Policy (UpperCircularStage.Query n) ℝ)
    (origin : State n) (recipient : Fin n) :
    Executes policy (program origin recipient) origin.history (giveAll origin recipient) [] :=
  Executes.returned _ _

theorem giveAll_domain (origin : State n) (recipient j : Fin n) :
    domain (giveAll origin recipient j).cells =
      if j = recipient then domain origin.cells else ∅ := by
  unfold giveAll
  split_ifs <;> rfl

theorem giveAll_history (origin : State n) (recipient j : Fin n) :
    (giveAll origin recipient j).history = origin.history := by
  unfold giveAll
  split_ifs <;> rfl

theorem giveAll_pairwise (origin : State n) (recipient : Fin n) :
    Pairwise (fun i j => Disjoint (domain (giveAll origin recipient i).cells)
      (domain (giveAll origin recipient j).cells)) := by
  intro i j hij
  rw [giveAll_domain, giveAll_domain]
  split_ifs with hi hj hj <;> simp_all

theorem giveAll_complete (origin : State n) (recipient : Fin n) :
    (⋃ j, domain (giveAll origin recipient j).cells) = domain origin.cells := by
  ext x
  simp only [mem_iUnion, giveAll_domain]
  constructor
  · rintro ⟨j,hj⟩
    split_ifs at hj with h
    · exact hj
    · exact False.elim hj
  · intro hx
    exact ⟨recipient, by simpa using hx⟩

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem giveAll_wellFormed (origin : State n) (hgood : WellFormed μ origin)
    (recipient j : Fin n) : WellFormed μ (giveAll origin recipient j) := by
  unfold giveAll
  split_ifs
  · exact hgood
  · exact empty_wellFormed μ origin.history hgood.2.2.1

theorem giveAll_value (origin : State n) (recipient i j : Fin n) :
    (μ i).real (domain (giveAll origin recipient j).cells) =
      if j = recipient then (μ i).real (domain origin.cells) else 0 := by
  rw [giveAll_domain]
  split_ifs <;> simp

theorem giveAll_cached (origin : State n) (hgood : WellFormed μ origin)
    (recipient i j : Fin n) :
    total (giveAll origin recipient j) i = if j = recipient then total origin i else 0 := by
  rw [total_correct μ _ (giveAll_wellFormed μ origin hgood recipient j),
    giveAll_value, total_correct μ origin hgood]

theorem giveAll_chore_EF (origin : State n) (recipient : Fin n)
    (hzero : (μ recipient).real (domain origin.cells) = 0) (active : Set (Fin n)) :
    GlobalCompletion.ActiveEF .chore
      (fun i j => (μ i).real (domain (giveAll origin recipient j).cells)) active := by
  intro i hi j hj
  simp only [GlobalCompletion.margin, giveAll_value]
  split_ifs with hjr hir hir
  · subst i
    simp [hzero]
  · simpa using (measureReal_nonneg : 0 ≤ (μ i).real (domain origin.cells))
  · subst i
    simp [hzero]
  · norm_num

theorem giveAll_cake_EF (origin : State n) (recipient : Fin n) (active : Set (Fin n))
    (hzero : ∀ i ∈ active, (μ i).real (domain origin.cells) = 0) :
    GlobalCompletion.ActiveEF .cake
      (fun i j => (μ i).real (domain (giveAll origin recipient j).cells)) active := by
  intro i hi j hj
  simp only [GlobalCompletion.margin, giveAll_value, hzero i hi, ite_self, sub_self, le_refl]

theorem giveAll_singleton_EF (origin : State n) (recipient : Fin n)
    (direction : GlobalCompletion.Direction) :
    GlobalCompletion.ActiveEF direction
      (fun i j => (μ i).real (domain (giveAll origin recipient j).cells)) {recipient} := by
  intro i hi j hj
  have hi' : i = recipient := hi
  have hj' : j = recipient := hj
  subst i
  subst j
  rw [GlobalCompletion.margin_self]

def zeroRows (origin : State n) (active : Finset (Fin n)) : Finset (Fin n) :=
  active.filter (fun i => total origin i = 0)

theorem zeroRows_correct (origin : State n) (hgood : WellFormed μ origin)
    (active : Finset (Fin n)) (i : Fin n) :
    i ∈ zeroRows origin active ↔ i ∈ active ∧ (μ i).real (domain origin.cells) = 0 := by
  simp only [zeroRows, Finset.mem_filter, total_correct μ origin hgood]

theorem no_zeroRows_positive (origin : State n) (hgood : WellFormed μ origin)
    (active : Finset (Fin n)) (hnone : zeroRows origin active = ∅) :
    ∀ i ∈ active, 0 < (μ i).real (domain origin.cells) := by
  intro i hi
  apply lt_of_le_of_ne measureReal_nonneg
  intro heq
  have hm := (zeroRows_correct μ origin hgood active i).mpr ⟨hi,heq.symm⟩
  simpa [hnone] using hm

end EnvyFreeResearch.Full.UpperZeroRows
