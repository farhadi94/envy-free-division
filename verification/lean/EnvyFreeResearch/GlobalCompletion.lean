import Mathlib
import EnvyFreeResearch.R4GlobalPotential

/-! Concrete finite composition of the cake/chore completion transitions.
All value identities and residue budgets below are finite tables. Continuous
Snapshot, Shrink and Repair construction and random termination are separate. -/

namespace EnvyFreeResearch.GlobalCompletion

open scoped BigOperators

inductive Direction where
  | cake
  | chore
  deriving DecidableEq

abbrev Table (Agent : Type*) := Agent → Agent → ℝ

def margin {Agent : Type*} (direction : Direction) (v : Table Agent) (i j : Agent) : ℝ :=
  match direction with
  | .cake => v i i - v i j
  | .chore => v i j - v i i

def EnvyFree {Agent : Type*} (direction : Direction) (v : Table Agent) : Prop :=
  ∀ i j, 0 ≤ margin direction v i j

def ActiveEF {Agent : Type*} (direction : Direction) (v : Table Agent) (active : Set Agent) : Prop :=
  ∀ i ∈ active, ∀ j ∈ active, 0 ≤ margin direction v i j

def Guard {Agent : Type*} (direction : Direction) (v : Table Agent)
    (active : Set Agent) (residue : Agent → ℝ) : Prop :=
  match direction with
  | .cake => R4GlobalPotential.CakeGuard v active residue
  | .chore => R4GlobalPotential.ChoreGuard v active residue

def Nonnegative {Agent : Type*} (v : Table Agent) : Prop := ∀ i j, 0 ≤ v i j

variable {Agent : Type*}

theorem margin_self (direction : Direction) (v : Table Agent) (i : Agent) :
    margin direction v i i = 0 := by cases direction <;> simp [margin]

theorem cake_ef_iff (v : Table Agent) : EnvyFree .cake v ↔ R4GlobalPotential.CakeEF v := by
  constructor <;> intro h i j <;> have hh := h i j <;>
    dsimp [margin] at hh ⊢ <;> linarith

theorem chore_ef_iff (v : Table Agent) : EnvyFree .chore v ↔ R4GlobalPotential.ChoreEF v := by
  constructor <;> intro h i j <;> have hh := h i j <;>
    dsimp [margin] at hh ⊢ <;> linarith

theorem margin_add (direction : Direction) (v w : Table Agent) (i j : Agent) :
    margin direction (fun a b => v a b + w a b) i j =
      margin direction v i j + margin direction w i j := by
  cases direction <;> simp only [margin] <;> ring

section WholeAddition

variable [Fintype Agent]

/-- Exact finite identities supplied by disjoint additions from the old residue.
Global EF, guards, domination and progress are deliberately not fields. -/
structure WholeAddition (old new : Table Agent) (active : Set Agent)
    (residue remaining : Agent → ℝ) where
  permutation : Equiv.Perm Agent
  addition : Table Agent
  addition_nonnegative : Nonnegative addition
  fixed : ∀ j ∉ active, permutation j = j
  frozen_addition : ∀ i j, j ∉ active → addition i j = 0
  value_identity : ∀ i j, new i (permutation j) = old i j + addition i j
  mass_partition : ∀ i, (∑ j, addition i j) + remaining i = residue i
  remaining_nonnegative : ∀ i, 0 ≤ remaining i

variable {old new : Table Agent} {active : Set Agent} {residue remaining : Agent → ℝ}

theorem addition_le_total (T : WholeAddition old new active residue remaining) (i j : Agent) :
    T.addition i j ≤ ∑ h, T.addition i h := by
  exact Finset.single_le_sum (s := Finset.univ) (a := j)
    (fun h _ => T.addition_nonnegative i h) (Finset.mem_univ j)

/-- Individual spending bounds follow from the full mass partition. -/
theorem addition_budget (T : WholeAddition old new active residue remaining) (i j : Agent) :
    T.addition i j + remaining i ≤ residue i := by
  have h := addition_le_total T i j
  have hp := T.mass_partition i
  linarith

theorem residue_decreases (T : WholeAddition old new active residue remaining) (i : Agent) :
    remaining i ≤ residue i := by
  have hs : 0 ≤ ∑ j, T.addition i j :=
    Finset.sum_nonneg (fun j _ => T.addition_nonnegative i j)
  have hp := T.mass_partition i
  linarith

theorem whole_addition_nonnegative (T : WholeAddition old new active residue remaining)
    (hold : Nonnegative old) : Nonnegative new := by
  intro i j
  obtain ⟨h, rfl⟩ := T.permutation.surjective j
  rw [T.value_identity]
  exact add_nonneg (hold i h) (T.addition_nonnegative i h)

/-- Active EF gives cake's own bound; frozen own values are unchanged. -/
theorem cake_own_bound (T : WholeAddition old new active residue remaining)
    (hactive : ActiveEF .cake new active) (i : Agent) :
    old i i + T.addition i i ≤ new i i := by
  by_cases hi : i ∈ active
  · have hf := (R4GlobalPotential.permutation_active_iff T.permutation active T.fixed i).mpr hi
    have h := hactive i hi (T.permutation i) hf
    rw [margin, T.value_identity] at h
    linarith
  · have h := T.value_identity i i
    rw [T.fixed i hi] at h
    exact h.ge

theorem chore_own_bound (T : WholeAddition old new active residue remaining)
    (hactive : ActiveEF .chore new active) (i : Agent) :
    new i i ≤ old i i + T.addition i i := by
  by_cases hi : i ∈ active
  · have hf := (R4GlobalPotential.permutation_active_iff T.permutation active T.fixed i).mpr hi
    have h := hactive i hi (T.permutation i) hf
    rw [margin, T.value_identity] at h
    linarith
  · have h := T.value_identity i i
    rw [T.fixed i hi] at h
    exact h.le

/-- Global EF and directional guards follow from the concrete table identities. -/
theorem whole_addition_preserves_EF_guard (direction : Direction)
    (T : WholeAddition old new active residue remaining)
    (hold : EnvyFree direction old) (hguard : Guard direction old active residue)
    (hactive : ActiveEF direction new active) :
    EnvyFree direction new ∧ Guard direction new active remaining := by
  cases direction with
  | cake =>
      have ha : ∀ i ∈ active, ∀ j ∈ active, new i j ≤ new i i := by
        intro i hi j hj
        have h := hactive i hi j hj
        dsimp [margin] at h
        linarith
      exact ⟨(cake_ef_iff new).mpr
        (R4GlobalPotential.cake_global_EF old new T.addition T.permutation active residue remaining
          ((cake_ef_iff old).mp hold) hguard T.fixed T.value_identity T.frozen_addition
          T.addition_nonnegative (addition_budget T) T.remaining_nonnegative ha),
        R4GlobalPotential.cake_guard_preserved old new T.addition T.permutation active residue remaining
          T.fixed T.value_identity T.frozen_addition (addition_budget T) hguard⟩
  | chore =>
      have ha : ∀ i ∈ active, ∀ j ∈ active, new i i ≤ new i j := by
        intro i hi j hj
        have h := hactive i hi j hj
        dsimp [margin] at h
        linarith
      exact ⟨(chore_ef_iff new).mpr
        (R4GlobalPotential.chore_global_EF old new T.addition T.permutation active residue remaining
          ((chore_ef_iff old).mp hold) hguard T.fixed T.value_identity T.frozen_addition
          T.addition_nonnegative (addition_budget T) T.remaining_nonnegative ha),
        R4GlobalPotential.chore_guard_preserved old new T.addition T.permutation active residue remaining
          T.fixed T.value_identity T.frozen_addition (addition_budget T) ha hguard⟩

/-- Whole-label gap loss is charged to an actual nonnegative addition. -/
theorem whole_addition_gap_transport (direction : Direction)
    (T : WholeAddition old new active residue remaining)
    (hactive : ActiveEF direction new active) (i j : Agent) :
    margin direction old i j -
      (match direction with | .cake => T.addition i j | .chore => T.addition i i) ≤
      margin direction new i (T.permutation j) := by
  cases direction with
  | cake =>
      have ho := cake_own_bound T hactive i
      have hn := T.addition_nonnegative i i
      dsimp [margin]
      rw [T.value_identity]
      linarith
  | chore =>
      have ho := chore_own_bound T hactive i
      have hn := T.addition_nonnegative i j
      dsimp [margin]
      rw [T.value_identity]
      linarith

theorem whole_addition_domination_transport (direction : Direction)
    (T : WholeAddition old new active residue remaining)
    (hactive : ActiveEF direction new active) (i j : Agent)
    (hdom : residue i ≤ margin direction old i j) :
    remaining i ≤ margin direction new i (T.permutation j) := by
  have hg := whole_addition_gap_transport direction T hactive i j
  cases direction with
  | cake => have hb := addition_budget T i j; dsimp at hg; linarith
  | chore => have hb := addition_budget T i i; dsimp at hg; linarith

noncomputable def dominationPotential (direction : Direction) (value : Table Agent)
    (residue : Agent → ℝ) : ℕ :=
  R2OnlinePotential.potential (R4GlobalPotential.targets (margin direction value) residue)

/-- Zero rows use EF saturation at n−1, not improper image inclusion. -/
theorem whole_addition_target_counts (direction : Direction)
    (T : WholeAddition old new active residue remaining)
    (hold : EnvyFree direction old) (hguard : Guard direction old active residue)
    (hactive : ActiveEF direction new active) (i : Agent) :
    (R4GlobalPotential.targets (margin direction old) residue i).card ≤
      (R4GlobalPotential.targets (margin direction new) remaining i).card := by
  have hnew := (whole_addition_preserves_EF_guard direction T hold hguard hactive).1
  apply R4GlobalPotential.row_card_monotone (margin direction old) (margin direction new)
    residue remaining T.permutation hnew (margin_self direction new) T.remaining_nonnegative
  intro h _ j hj
  have hdom : residue h ≤ margin direction old h j := by
    have hm : j ≠ h ∧ residue h ≤ margin direction old h j := by simpa [R4GlobalPotential.targets] using hj
    exact hm.2
  exact whole_addition_domination_transport direction T hactive h j hdom

end WholeAddition

/-- Value table before final Repair: whole old bundles, additive shrinking pieces,
and a permutation of the separately recorded Snapshot pieces. -/
def transferred (old shrink snapshot : Table Agent) (alpha : Equiv.Perm Agent) : Table Agent :=
  fun i j => old i j + shrink i j + snapshot i (alpha j)

theorem transferred_margin_identity (direction : Direction)
    (old shrink snapshot : Table Agent) (alpha : Equiv.Perm Agent) (i j : Agent) :
    margin direction (transferred old shrink snapshot alpha) i j =
      margin direction old i j + margin direction shrink i j +
        margin direction snapshot i (alpha j) - margin direction snapshot i (alpha i) := by
  cases direction <;> simp only [margin, transferred] <;> ring

section ConcreteStep

variable [Fintype Agent]

/-- Finite output certificates of Snapshot, Shrink, and final Repair.
No global EF, guard preservation, transported target, or potential increase is assumed. -/
structure ConcreteStep (direction : Direction) (active : Set Agent)
    (old new : Table Agent) (residue remaining : Agent → ℝ) where
  snapshot : Table Agent
  shrink : Table Agent
  payment : Table Agent
  snapshot_permutation : Equiv.Perm Agent
  final_permutation : Equiv.Perm Agent
  buffer : Agent → ℝ
  tolerance : ℝ
  witness : Agent
  target : Agent
  snapshot_nonnegative : Nonnegative snapshot
  shrink_nonnegative : Nonnegative shrink
  payment_nonnegative : Nonnegative payment
  snapshot_frozen : ∀ i j, j ∉ active → snapshot i j = 0
  shrink_frozen : ∀ i j, j ∉ active → shrink i j = 0
  payment_frozen : ∀ i j, j ∉ active → payment i j = 0
  snapshot_fixed : ∀ j ∉ active, snapshot_permutation j = j
  final_fixed : ∀ j ∉ active, final_permutation j = j
  before_partition : ∀ i, (∑ j, (shrink i j + snapshot i j)) + buffer i = residue i
  repair_partition : ∀ i, (∑ j, payment i j) + remaining i = buffer i
  remaining_nonnegative : ∀ i, 0 ≤ remaining i
  buffer_positive : ∀ i ∈ active, 0 < buffer i
  snapshot_EF : ActiveEF direction snapshot active
  shrink_EF : ActiveEF direction shrink active
  final_EF : ActiveEF direction new active
  small_own_loss : ∀ i ∈ active,
    margin direction snapshot i (snapshot_permutation i) ≤ tolerance * buffer i
  witness_active : witness ∈ active
  target_active : target ∈ active
  target_distinct : target ≠ witness
  anchor_missing : margin direction old witness target < residue witness
  large_snapshot_gap : 2 * buffer witness ≤
    margin direction snapshot witness (snapshot_permutation target)
  tolerance_small : tolerance < 3 / 4
  quarter_spending : ∀ i ∈ active, (∑ j, payment i j) ≤ buffer i / 4
  repaired_identity : ∀ i j, new i (final_permutation j) =
    transferred old shrink snapshot snapshot_permutation i j + payment i (final_permutation j)

variable {direction : Direction} {active : Set Agent} {old new : Table Agent}
  {residue remaining : Agent → ℝ}

/-- Reconstruct the physical whole-old-label transition; conservation uses both permutations. -/
def ConcreteStep.wholeAddition
    (S : ConcreteStep direction active old new residue remaining) :
    WholeAddition old new active residue remaining where
  permutation := S.final_permutation
  addition := fun i j => S.shrink i j + S.snapshot i (S.snapshot_permutation j) +
    S.payment i (S.final_permutation j)
  addition_nonnegative := fun i j => add_nonneg
    (add_nonneg (S.shrink_nonnegative i j) (S.snapshot_nonnegative i _))
    (S.payment_nonnegative i _)
  fixed := S.final_fixed
  frozen_addition := by
    intro i j hj
    rw [S.snapshot_fixed j hj, S.final_fixed j hj,
      S.snapshot_frozen i j hj, S.shrink_frozen i j hj, S.payment_frozen i j hj]
    norm_num
  value_identity := by
    intro i j
    rw [S.repaired_identity]
    simp only [transferred]
    ring
  mass_partition := by
    intro i
    simp only [Finset.sum_add_distrib]
    rw [Equiv.sum_comp S.snapshot_permutation (S.snapshot i),
      Equiv.sum_comp S.final_permutation (S.payment i)]
    have hb := S.before_partition i
    have hr := S.repair_partition i
    rw [Finset.sum_add_distrib] at hb
    linarith
  remaining_nonnegative := S.remaining_nonnegative

/-- The second whole-label transition starts from the transferred, possibly non-EF table. -/
def ConcreteStep.repairAddition
    (S : ConcreteStep direction active old new residue remaining) :
    WholeAddition (transferred old S.shrink S.snapshot S.snapshot_permutation)
      new active S.buffer remaining where
  permutation := S.final_permutation
  addition := fun i j => S.payment i (S.final_permutation j)
  addition_nonnegative := fun i j => S.payment_nonnegative i _
  fixed := S.final_fixed
  frozen_addition := by
    intro i j hj
    rw [S.final_fixed j hj, S.payment_frozen i j hj]
  value_identity := S.repaired_identity
  mass_partition := by
    intro i
    rw [Equiv.sum_comp S.final_permutation (S.payment i)]
    exact S.repair_partition i
  remaining_nonnegative := S.remaining_nonnegative

/-- Both preference directions have the same near-EF transferred-margin calculation. -/
theorem transferred_near_EF
    (S : ConcreteStep direction active old new residue remaining)
    (hold : EnvyFree direction old) (i : Agent) (hi : i ∈ active)
    (j : Agent) (hj : j ∈ active) :
    -S.tolerance * S.buffer i ≤
      margin direction (transferred old S.shrink S.snapshot S.snapshot_permutation) i j := by
  have hw := hold i j
  have hh := S.shrink_EF i hi j hj
  have hxa := (R4GlobalPotential.permutation_active_iff S.snapshot_permutation active
    S.snapshot_fixed j).mpr hj
  have hx := S.snapshot_EF i hi (S.snapshot_permutation j) hxa
  have hl := S.small_own_loss i hi
  rw [transferred_margin_identity]
  linarith

/-- The pre-repair witness is proved from the actual permuted Snapshot margins. -/
theorem transferred_witness_margin
    (S : ConcreteStep direction active old new residue remaining)
    (hold : EnvyFree direction old) :
    (2 - S.tolerance) * S.buffer S.witness ≤
      margin direction (transferred old S.shrink S.snapshot S.snapshot_permutation)
        S.witness S.target := by
  have hw := hold S.witness S.target
  have hh := S.shrink_EF S.witness S.witness_active S.target S.target_active
  have hl := S.small_own_loss S.witness S.witness_active
  have hx := S.large_snapshot_gap
  rw [transferred_margin_identity]
  nlinarith

/-- Final Repair may lose at most its total spending in an observer's row. -/
theorem repair_gap_loss
    (S : ConcreteStep direction active old new residue remaining) (i j : Agent) :
    margin direction (transferred old S.shrink S.snapshot S.snapshot_permutation) i j -
      (∑ h, S.payment i h) ≤ margin direction new i (S.final_permutation j) := by
  have hg := whole_addition_gap_transport direction S.repairAddition S.final_EF i j
  have hpay : ∀ h, S.payment i h ≤ ∑ r, S.payment i r := by
    intro h
    exact Finset.single_le_sum (s := Finset.univ) (a := h)
      (fun r _ => S.payment_nonnegative i r) (Finset.mem_univ h)
  cases direction with
  | cake =>
      dsimp [ConcreteStep.repairAddition] at hg
      linarith [hpay (S.final_permutation j)]
  | chore =>
      dsimp [ConcreteStep.repairAddition] at hg
      linarith [hpay (S.final_permutation i)]

theorem concrete_witness_margin
    (S : ConcreteStep direction active old new residue remaining)
    (hold : EnvyFree direction old) :
    (7 / 4 - S.tolerance) * S.buffer S.witness ≤
      margin direction new S.witness (S.final_permutation S.target) := by
  have hb := transferred_witness_margin S hold
  have hl := repair_gap_loss S S.witness S.target
  have hq := S.quarter_spending S.witness S.witness_active
  nlinarith

/-- Positivity of the witness's final residue is derived from payment conservation. -/
theorem concrete_witness_residue
    (S : ConcreteStep direction active old new residue remaining) :
    3 * S.buffer S.witness / 4 ≤ remaining S.witness ∧
      0 < remaining S.witness ∧ remaining S.witness ≤ S.buffer S.witness := by
  have hquarter := R4GlobalPotential.quarter_leftover_positive
    (S.buffer S.witness) (∑ j, S.payment S.witness j) (remaining S.witness)
    (S.buffer_positive S.witness S.witness_active)
    (S.quarter_spending S.witness S.witness_active) (S.repair_partition S.witness)
  exact ⟨hquarter.1, hquarter.2, residue_decreases S.repairAddition S.witness⟩

theorem concrete_witness_strict
    (S : ConcreteStep direction active old new residue remaining)
    (hold : EnvyFree direction old) :
    remaining S.witness < margin direction new S.witness (S.final_permutation S.target) := by
  exact R4GlobalPotential.repaired_witness_strict (S.buffer S.witness) S.tolerance
    (margin direction new S.witness (S.final_permutation S.target)) (remaining S.witness)
    (S.buffer_positive S.witness S.witness_active) S.tolerance_small
    (concrete_witness_margin S hold) (concrete_witness_residue S).2.2

/-- A concrete successful continuation proves global invariants and strict saved-anchor progress. -/
theorem concrete_step_composition
    (S : ConcreteStep direction active old new residue remaining)
    (hold : EnvyFree direction old) (hguard : Guard direction old active residue) :
    EnvyFree direction new ∧ Guard direction new active remaining ∧
      dominationPotential direction old residue + 1 ≤ dominationPotential direction new remaining := by
  classical
  have hglobal := whole_addition_preserves_EF_guard direction S.wholeAddition hold hguard S.final_EF
  refine ⟨hglobal.1, hglobal.2, ?_⟩
  refine R4GlobalPotential.strict_global_progress (margin direction old) (margin direction new)
    residue remaining S.final_permutation hglobal.1 (margin_self direction new)
    S.remaining_nonnegative ?_ S.witness S.target (concrete_witness_residue S).2.1 ?_
    (concrete_witness_strict S hold).le
  · intro i _ j hj
    have hm : j ≠ i ∧ residue i ≤ margin direction old i j := by
      simpa [R4GlobalPotential.targets] using hj
    exact whole_addition_domination_transport direction S.wholeAddition S.final_EF i j hm.2
  · simp [R4GlobalPotential.targets, not_le.mpr S.anchor_missing]

end ConcreteStep

/-- The cross-boundary comparisons that permit a population reduction. -/
def FreezeSeparation (direction : Direction) (value : Table Agent)
    (active retained : Set Agent) (residue : Agent → ℝ) : Prop :=
  match direction with
  | .cake => ∀ f ∈ active, f ∉ retained → ∀ i ∈ retained,
      residue f ≤ margin .cake value f i
  | .chore => ∀ i ∈ retained, ∀ f ∈ active, f ∉ retained →
      residue i ≤ margin .chore value i f

theorem freeze_preserves_guard (direction : Direction) (value : Table Agent)
    (active retained : Set Agent) (residue : Agent → ℝ)
    (hsub : retained ⊆ active) (hguard : Guard direction value active residue)
    (hsep : FreezeSeparation direction value active retained residue) :
    Guard direction value retained residue := by
  cases direction with
  | cake => exact R4GlobalPotential.cake_guard_after_freeze value active retained residue hsub hguard hsep
  | chore => exact R4GlobalPotential.chore_guard_after_freeze value active retained residue hsub hguard hsep

structure State (Agent : Type*) where
  value : Table Agent
  residue : Agent → ℝ
  active : Set Agent

def Valid (direction : Direction) (state : State Agent) : Prop :=
  Nonnegative state.value ∧ (∀ i, 0 ≤ state.residue i) ∧
    EnvyFree direction state.value ∧ Guard direction state.value state.active state.residue

section FiniteRun

variable [Fintype Agent]

/-- Each event is an actual completed Repair continuation or a guarded freeze.
The freeze includes an actually removed agent; neither event assumes progress. -/
inductive CompletionEvent (direction : Direction) (before after : State Agent) where
  | advance (active_unchanged : after.active = before.active)
      (certificate : ConcreteStep direction before.active before.value after.value
        before.residue after.residue)
  | freeze (value_unchanged : after.value = before.value)
      (residue_unchanged : after.residue = before.residue)
      (retained : after.active ⊆ before.active)
      (removed : ∃ i, i ∈ before.active ∧ i ∉ after.active)
      (separation : FreezeSeparation direction before.value before.active after.active before.residue)

def CompletionEvent.charge {direction : Direction} {before after : State Agent}
    (event : CompletionEvent direction before after) : ℕ :=
  match event with
  | .advance _ _ => 1
  | .freeze _ _ _ _ _ => 0

noncomputable def statePotential (direction : Direction) (state : State Agent) : ℕ :=
  dominationPotential direction state.value state.residue

noncomputable def activeCount (state : State Agent) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => i ∈ state.active)).card

noncomputable def combinedPotential (direction : Direction) (state : State Agent) : ℕ :=
  statePotential direction state + (Fintype.card Agent - activeCount state)

theorem active_count_le (state : State Agent) : activeCount state ≤ Fintype.card Agent := by
  classical
  exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)

theorem strict_active_count (before after : State Agent)
    (hsub : after.active ⊆ before.active) (hremoved : ∃ i, i ∈ before.active ∧ i ∉ after.active) :
    activeCount after < activeCount before := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hsub hi
  · intro heq
    obtain ⟨i, hi, hn⟩ := hremoved
    have hm : i ∈ Finset.univ.filter (fun j => j ∈ before.active) := by simp [hi]
    rw [← heq] at hm
    exact hn (by simpa using hm)

theorem event_preserves_valid {direction : Direction} {before after : State Agent}
    (event : CompletionEvent direction before after) (hvalid : Valid direction before) :
    Valid direction after := by
  rcases hvalid with ⟨hv, hr, he, hg⟩
  cases event with
  | advance ha S =>
      have hnew := concrete_step_composition S he hg
      exact ⟨whole_addition_nonnegative S.wholeAddition hv, S.remaining_nonnegative,
        hnew.1, by simpa only [ha] using hnew.2.1⟩
  | freeze hvEq hrEq hsub _ hsep =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [hvEq] using hv
      · simpa only [hrEq] using hr
      · simpa only [hvEq] using he
      · rw [hvEq, hrEq]
        exact freeze_preserves_guard direction before.value before.active after.active
          before.residue hsub hg hsep

/-- Charged progress is derived from each concrete event, not supplied by the run. -/
theorem event_potential_growth {direction : Direction} {before after : State Agent}
    (event : CompletionEvent direction before after) (hvalid : Valid direction before) :
    statePotential direction before + event.charge ≤ statePotential direction after := by
  cases event with
  | advance _ S =>
      exact (concrete_step_composition S hvalid.2.2.1 hvalid.2.2.2).2.2
  | freeze hv hr _ _ _ =>
      simp only [CompletionEvent.charge, Nat.add_zero, statePotential, hv, hr, le_refl]

/-- Every completed event increases a bounded combination of domination and removed agents. -/
theorem event_combined_growth {direction : Direction} {before after : State Agent}
    (event : CompletionEvent direction before after) (hvalid : Valid direction before) :
    combinedPotential direction before + 1 ≤ combinedPotential direction after := by
  have hp := event_potential_growth event hvalid
  cases event with
  | advance ha S =>
      have hc : activeCount after = activeCount before := by
        classical
        unfold activeCount
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha]
      dsimp [CompletionEvent.charge] at hp
      dsimp [combinedPotential]
      omega
  | freeze hv hr hs hremoved _ =>
      have hc := strict_active_count before after hs hremoved
      have hb := active_count_le before
      have hpEq : statePotential direction after = statePotential direction before := by
        simp only [statePotential, hv, hr]
      dsimp [combinedPotential]
      omega

theorem state_potential_cap (direction : Direction) (state : State Agent) :
    statePotential direction state ≤ Fintype.card Agent * (Fintype.card Agent - 1) :=
  R4GlobalPotential.global_potential_cap (margin direction state.value) state.residue

theorem combined_potential_cap (direction : Direction) (state : State Agent) :
    combinedPotential direction state ≤
      Fintype.card Agent * (Fintype.card Agent - 1) + Fintype.card Agent := by
  have hp := state_potential_cap direction state
  dsimp [combinedPotential]
  omega

noncomputable def runCharge {direction : Direction} (states : ℕ → State Agent) (events : ℕ)
    (run : ∀ t, t < events → CompletionEvent direction (states t) (states (t + 1))) (t : ℕ) : ℕ := by
  classical
  exact if ht : t < events then (run t ht).charge else 0

/-- EF and guards hold at every state of a finite concrete run. -/
theorem finite_run_valid {direction : Direction} (states : ℕ → State Agent) (events : ℕ)
    (run : ∀ t, t < events → CompletionEvent direction (states t) (states (t + 1)))
    (hinitial : Valid direction (states 0)) :
    ∀ t, t ≤ events → Valid direction (states t) := by
  intro t
  induction t with
  | zero => intro _; exact hinitial
  | succ t ih =>
      intro ht
      exact event_preserves_valid (run t (by omega)) (ih (by omega))

/-- At most n(n−1) successful nonterminal iterations, even with interleaved freezes. -/
theorem finite_run_iteration_bound {direction : Direction} (states : ℕ → State Agent) (events : ℕ)
    (run : ∀ t, t < events → CompletionEvent direction (states t) (states (t + 1)))
    (hinitial : Valid direction (states 0)) :
    (∑ t ∈ Finset.range events, runCharge states events run t) ≤
      Fintype.card Agent * (Fintype.card Agent - 1) := by
  apply R4GlobalPotential.interleaved_progress_bound
    (fun t => statePotential direction (states t)) (runCharge states events run) events
  · intro t ht
    simpa only [runCharge, dite_eq_left ht] using
      event_potential_growth (run t ht) (finite_run_valid states events run hinitial t ht.le)
  · exact state_potential_cap direction (states events)

/-- All completed continuation/freeze events have a finite bound, without assuming termination. -/
theorem finite_run_event_bound {direction : Direction} (states : ℕ → State Agent) (events : ℕ)
    (run : ∀ t, t < events → CompletionEvent direction (states t) (states (t + 1)))
    (hinitial : Valid direction (states 0)) :
    events ≤ Fintype.card Agent * (Fintype.card Agent - 1) + Fintype.card Agent := by
  have hg := R2OnlinePotential.accumulated_progress
    (fun t => combinedPotential direction (states t)) events (fun t ht =>
      event_combined_growth (run t ht) (finite_run_valid states events run hinitial t ht.le))
  have hc := combined_potential_cap direction (states events)
  omega

/-- A terminal iteration starts before saturation, so it incurs no erroneous extra +1. -/
theorem finite_run_with_terminal_bound {direction : Direction} (states : ℕ → State Agent) (events : ℕ)
    (run : ∀ t, t < events → CompletionEvent direction (states t) (states (t + 1)))
    (hinitial : Valid direction (states 0))
    (hmissing : ∃ a b, b ≠ a ∧ margin direction (states events).value a b < (states events).residue a) :
    (∑ t ∈ Finset.range events, runCharge states events run t) + 1 ≤
      Fintype.card Agent * (Fintype.card Agent - 1) := by
  classical
  obtain ⟨a, b, hne, hmiss⟩ := hmissing
  have hcap : statePotential direction (states events) <
      Fintype.card Agent * (Fintype.card Agent - 1) := by
    exact R2OnlinePotential.potential_lt_of_missing
      (R4GlobalPotential.targets (margin direction (states events).value) (states events).residue)
      (R4GlobalPotential.targets_proper _ _) a b hne
      (by simp [R4GlobalPotential.targets, not_le.mpr hmiss])
  have hsum := R4GlobalPotential.interleaved_progress_bound
    (fun t => statePotential direction (states t)) (runCharge states events run) events
    (statePotential direction (states events)) (fun t ht => by
      simpa only [runCharge, dite_eq_left ht] using
        event_potential_growth (run t ht) (finite_run_valid states events run hinitial t ht.le))
    (le_refl _)
  omega

/-- Infinitely many returned finite certificates are impossible; this says nothing about a
request that has not returned, whose almost-sure termination remains a probability theorem. -/
theorem no_infinite_completed_events {direction : Direction} (states : ℕ → State Agent)
    (hinitial : Valid direction (states 0)) :
    ¬ (∀ t, Nonempty (CompletionEvent direction (states t) (states (t + 1)))) := by
  classical
  intro hrun
  let cap := Fintype.card Agent * (Fintype.card Agent - 1) + Fintype.card Agent
  have hb := finite_run_event_bound states (cap + 1)
    (fun t _ => Classical.choice (hrun t)) hinitial
  omega

end FiniteRun

section FiniteAtoms

variable [Fintype Agent] {Atom : Type*}

/-- Each recorded atom has at most one recipient; `none` retains it as residue. -/
noncomputable def atomAddition (pool : Finset Atom) (weight : Agent → Atom → ℝ)
    (recipient : Atom → Option Agent) : Table Agent := by
  classical
  exact fun i j => ∑ a ∈ pool, if recipient a = some j then weight i a else 0

noncomputable def atomRemainder (pool : Finset Atom) (weight : Agent → Atom → ℝ)
    (recipient : Atom → Option Agent) : Agent → ℝ := by
  classical
  exact fun i => ∑ a ∈ pool, if recipient a = none then weight i a else 0

/-- Exact conservation is proved from unique ownership of the finite physical atoms. -/
theorem atom_partition_identity (pool : Finset Atom) (weight : Agent → Atom → ℝ)
    (recipient : Atom → Option Agent) (i : Agent) :
    (∑ j, atomAddition pool weight recipient i j) + atomRemainder pool weight recipient i =
      ∑ a ∈ pool, weight i a := by
  classical
  unfold atomAddition atomRemainder
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases recipient a with
  | none => simp
  | some j => simp [eq_comm]

omit [Fintype Agent] in
theorem atom_addition_nonnegative (pool : Finset Atom) (weight : Agent → Atom → ℝ)
    (recipient : Atom → Option Agent) (hweight : ∀ i a, a ∈ pool → 0 ≤ weight i a) :
    Nonnegative (atomAddition pool weight recipient) := by
  classical
  intro i j
  exact Finset.sum_nonneg (fun a ha => by
    split_ifs <;> first | exact hweight i a ha | exact le_refl 0)

omit [Fintype Agent] in
theorem atom_remainder_nonnegative (pool : Finset Atom) (weight : Agent → Atom → ℝ)
    (recipient : Atom → Option Agent) (hweight : ∀ i a, a ∈ pool → 0 ≤ weight i a) :
    ∀ i, 0 ≤ atomRemainder pool weight recipient i := by
  classical
  intro i
  exact Finset.sum_nonneg (fun a ha => by
    split_ifs <;> first | exact hweight i a ha | exact le_refl 0)

/-- Build the whole-label transition from the finite disjoint-ownership model.
Its mass partition is a theorem, not an assumed per-label spending condition. -/
noncomputable def finite_atom_transition (old : Table Agent) (active : Set Agent)
    (pool : Finset Atom) (weight : Agent → Atom → ℝ) (recipient : Atom → Option Agent)
    (permutation : Equiv.Perm Agent)
    (hfixed : ∀ j ∉ active, permutation j = j)
    (hweight : ∀ i a, a ∈ pool → 0 ≤ weight i a)
    (howner : ∀ a ∈ pool, ∀ j, recipient a = some j → j ∈ active) :
    WholeAddition old
      (fun i j => old i (permutation.symm j) + atomAddition pool weight recipient i (permutation.symm j))
      active (fun i => ∑ a ∈ pool, weight i a) (atomRemainder pool weight recipient) where
  permutation := permutation
  addition := atomAddition pool weight recipient
  addition_nonnegative := atom_addition_nonnegative pool weight recipient hweight
  fixed := hfixed
  frozen_addition := by
    classical
    intro i j hj
    apply Finset.sum_eq_zero
    intro a ha
    have hn : recipient a ≠ some j := fun h => hj (howner a ha j h)
    simp only [hn, ite_false]
  value_identity := by intro i j; simp only [Equiv.symm_apply_apply]
  mass_partition := atom_partition_identity pool weight recipient
  remaining_nonnegative := atom_remainder_nonnegative pool weight recipient hweight

end FiniteAtoms

section TerminalAndZeroRows

variable [Fintype Agent]

/-- The explicit zero-residue branch saturates a row after global EF is derived. -/
theorem whole_addition_zero_row [DecidableEq Agent] (direction : Direction)
    {old new : Table Agent} {active : Set Agent} {residue remaining : Agent → ℝ}
    (T : WholeAddition old new active residue remaining)
    (hold : EnvyFree direction old) (hguard : Guard direction old active residue)
    (hactive : ActiveEF direction new active) (i : Agent) (hzero : remaining i = 0) :
    R4GlobalPotential.targets (margin direction new) remaining i = Finset.univ.erase i := by
  classical
  exact R4GlobalPotential.zero_row_saturated (margin direction new) remaining i
    ((whole_addition_preserves_EF_guard direction T hold hguard hactive).1 i) hzero

/-- A positive remaining row has an injective proper-target image. This is not asserted at zero. -/
theorem whole_addition_positive_image [DecidableEq Agent] (direction : Direction)
    {old new : Table Agent} {active : Set Agent} {residue remaining : Agent → ℝ}
    (T : WholeAddition old new active residue remaining)
    (hactive : ActiveEF direction new active) (i : Agent) (hpositive : 0 < remaining i) :
    (R4GlobalPotential.targets (margin direction old) residue i).image T.permutation ⊆
      R4GlobalPotential.targets (margin direction new) remaining i := by
  classical
  apply R4GlobalPotential.positive_row_image_subset (margin direction old) (margin direction new)
    residue remaining T.permutation i hpositive (margin_self direction new i)
  intro j hj
  have hm : j ≠ i ∧ residue i ≤ margin direction old i j := by
    simpa [R4GlobalPotential.targets] using hj
  exact whole_addition_domination_transport direction T hactive i j hm.2

/-- Completing the residue by an additive active EF allocation preserves global EF.
The full sum identity is value-table completeness; physical set coverage is supplied separately. -/
theorem terminal_additive_EF (direction : Direction) (old addition : Table Agent)
    (active : Set Agent) (residue : Agent → ℝ)
    (hold : EnvyFree direction old) (hguard : Guard direction old active residue)
    (hadd : Nonnegative addition) (hfrozen : ∀ i j, j ∉ active → addition i j = 0)
    (hcomplete : ∀ i, ∑ j, addition i j = residue i)
    (hEF : ActiveEF direction addition active) :
    EnvyFree direction (fun i j => old i j + addition i j) ∧
      Guard direction (fun i j => old i j + addition i j) active (fun _ => 0) := by
  let T : WholeAddition old (fun i j => old i j + addition i j) active residue (fun _ => 0) :=
    { permutation := Equiv.refl Agent
      addition := addition
      addition_nonnegative := hadd
      fixed := by intro j _; rfl
      frozen_addition := hfrozen
      value_identity := by intro i j; rfl
      mass_partition := by intro i; simpa using hcomplete i
      remaining_nonnegative := by intro i; exact le_refl 0 }
  apply whole_addition_preserves_EF_guard direction T hold hguard
  intro i hi j hj
  rw [margin_add]
  exact add_nonneg (hold i j) (hEF i hi j hj)

/-- A zero-cost active chore recipient can take the full residue without disturbing guards. -/
theorem zero_chore_recipient_finishes [DecidableEq Agent] (old : Table Agent) (active : Set Agent)
    (residue : Agent → ℝ) (recipient : Agent)
    (hold : EnvyFree .chore old) (hguard : Guard .chore old active residue)
    (hr : ∀ i, 0 ≤ residue i) (ha : recipient ∈ active) (hzero : residue recipient = 0) :
    EnvyFree .chore (fun i j => old i j + if j = recipient then residue i else 0) ∧
      Guard .chore (fun i j => old i j + if j = recipient then residue i else 0)
        active (fun _ => 0) := by
  classical
  let addition : Table Agent := fun i j => if j = recipient then residue i else 0
  have hnon : Nonnegative addition := by
    intro i j
    dsimp [addition]
    split_ifs <;> first | exact hr i | exact le_refl 0
  apply terminal_additive_EF .chore old addition active residue hold hguard hnon
  · intro i j hj
    have hne : j ≠ recipient := by intro heq; subst j; exact hj ha
    simp [addition, hne]
  · intro i
    simp [addition]
  · intro i _ j _
    have hown : addition i i = 0 := by
      by_cases hi : i = recipient
      · subst i; simp [addition, hzero]
      · simp [addition, hi]
    dsimp [margin]
    rw [hown]
    simpa using hnon i j

omit [Fintype Agent] in
/-- A zero-value cake row can be frozen at an EF anchor; no uncorrected snapshot is used. -/
theorem zero_cake_row_can_freeze (old : Table Agent) (active : Set Agent)
    (residue : Agent → ℝ) (agent : Agent)
    (hold : EnvyFree .cake old) (hguard : Guard .cake old active residue)
    (hzero : residue agent = 0) : Guard .cake old (active \ {agent}) residue := by
  apply freeze_preserves_guard .cake old active (active \ {agent}) residue Set.sdiff_subset hguard
  intro f hf hnot i _
  have heq : f = agent := by
    by_contra hn
    exact hnot ⟨hf, by simpa using hn⟩
  subst f
  rw [hzero]
  exact hold agent i

omit [Fintype Agent] in
/-- Empty initial bundles with every agent active satisfy the global invariant. -/
theorem initial_state_valid (direction : Direction) (residue : Agent → ℝ)
    (hr : ∀ i, 0 ≤ residue i) :
    Valid direction (State.mk (fun _ _ => 0) residue Set.univ) := by
  refine ⟨by intro i j; exact le_refl 0, hr, ?_, ?_⟩
  · intro i j
    cases direction <;> simp [margin]
  · cases direction with
    | cake => intro f hf; exact False.elim (hf (Set.mem_univ f))
    | chore => intro i _ f hf; exact False.elim (hf (Set.mem_univ f))

end TerminalAndZeroRows

section TopLevel

variable [Fintype Agent]

/-- Finite composition through a final additive allocation of the remaining value table.
The concrete event certificates imply every intervening invariant and the iteration bound.
The terminal active allocation and its exact full-residue partition are supplied by the
physical caller; no continuous oracle construction or probability claim is hidden here. -/
theorem finite_global_completion {direction : Direction} (states : ℕ → State Agent) (events : ℕ)
    (run : ∀ t, t < events → CompletionEvent direction (states t) (states (t + 1)))
    (hinitial : Valid direction (states 0)) (addition : Table Agent)
    (hadd : Nonnegative addition)
    (hfrozen : ∀ i j, j ∉ (states events).active → addition i j = 0)
    (hcomplete : ∀ i, ∑ j, addition i j = (states events).residue i)
    (hEF : ActiveEF direction addition (states events).active) :
    Valid direction
      (State.mk (fun i j => (states events).value i j + addition i j)
        (fun _ => 0) (states events).active) ∧
      (∑ t ∈ Finset.range events, runCharge states events run t) ≤
        Fintype.card Agent * (Fintype.card Agent - 1) := by
  have hv := finite_run_valid states events run hinitial events (le_refl _)
  have hc := terminal_additive_EF direction (states events).value addition
    (states events).active (states events).residue hv.2.2.1 hv.2.2.2 hadd hfrozen hcomplete hEF
  refine ⟨⟨?_, ?_, hc.1, hc.2⟩, finite_run_iteration_bound states events run hinitial⟩
  · intro i j
    exact add_nonneg (hv.1 i j) (hadd i j)
  · intro i
    exact le_refl 0

end TopLevel

end EnvyFreeResearch.GlobalCompletion
