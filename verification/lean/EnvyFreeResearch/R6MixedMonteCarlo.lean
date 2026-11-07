import EnvyFreeResearch.SubmissionMonteCarlo

/-!
# Finite common-pulse dominance and no-repair certificates

The perturbed utility table is defined from actual positive and negative owner
labels and a common sequence of real pulse masses. The module does not assume
the desired envy conclusion, construct continuous supports, or formalize an
oracle, a random tape law, dominated convergence, or Fubini's theorem.
-/

namespace EnvyFreeResearch.R6MixedMonteCarlo

open scoped BigOperators
open SubmissionMonteCarlo

variable {Agent : Type*} [DecidableEq Agent]

/-- One common pulse adds its positive mass to one owner and subtracts the
same mass from its negative owner; equal labels cancel exactly. -/
def pulse (mass : ℝ) (positive negative recipient : Agent) : ℝ :=
  mass * ((if positive = recipient then 1 else 0) -
    (if negative = recipient then 1 else 0))

def perturbed (base : Agent → Agent → ℝ) (mass : ℕ → ℝ)
    (positive negative : ℕ → Agent) (L : ℕ) (i j : Agent) : ℝ :=
  base i j + ∑ r ∈ Finset.range L, pulse (mass r) (positive r) (negative r) j

def ApproxEF (value : Agent → Agent → ℝ) (ε : ℝ) : Prop :=
  ∀ i j, value i j - value i i ≤ ε

/-- For a finite signed atomic row, the actual value of any owner bundle is
bounded by the row's total absolute mass. -/
theorem owned_mass_abs_le_variation {Atom : Type*} (atoms : Finset Atom)
    (weight : Atom → ℝ) (owner : Atom → Agent) (recipient : Agent) :
    |∑ a ∈ atoms, if owner a = recipient then weight a else 0| ≤
      ∑ a ∈ atoms, |weight a| := by
  calc
    |∑ a ∈ atoms, if owner a = recipient then weight a else 0| ≤
        ∑ a ∈ atoms, |if owner a = recipient then weight a else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ atoms, |weight a| := by
      apply Finset.sum_le_sum
      intro a _
      by_cases h : owner a = recipient <;> simp [h]

theorem coassigned_pulse_zero (mass : ℝ) (owner recipient : Agent) :
    pulse mass owner owner recipient = 0 := by
  simp [pulse]

theorem pulse_value_bounds (mass : ℝ) (positive negative recipient : Agent)
    (hmass : 0 ≤ mass) :
    -mass ≤ pulse mass positive negative recipient ∧
      pulse mass positive negative recipient ≤ mass := by
  unfold pulse
  split_ifs <;> constructor <;> nlinarith

theorem pulse_comparison_lower (mass : ℝ) (positive negative own other : Agent)
    (hmass : 0 ≤ mass) :
    -2 * mass ≤ pulse mass positive negative other - pulse mass positive negative own := by
  have ho := pulse_value_bounds mass positive negative own hmass
  have ht := pulse_value_bounds mass positive negative other hmass
  linarith

/-- Every observer other than the positive owner sees a gain at least mass
toward that owner; a negative-owner observer actually sees gain twice mass. -/
theorem separated_pulse_gain (mass : ℝ) (positive negative observer : Agent)
    (hmass : 0 ≤ mass) (hseparated : positive ≠ negative) (hobserver : observer ≠ positive) :
    mass ≤ pulse mass positive negative positive - pulse mass positive negative observer := by
  by_cases hn : negative = observer
  · subst observer
    simp [pulse, hseparated, hseparated.symm]
    linarith
  · simp [pulse, hseparated.symm, hobserver.symm, hn]

theorem all_coassigned_preserves_values (base : Agent → Agent → ℝ) (mass : ℕ → ℝ)
    (positive negative : ℕ → Agent) (L : ℕ)
    (hagrees : ∀ r < L, positive r = negative r) :
    perturbed base mass positive negative L = base := by
  funext i j
  have hsum : (∑ r ∈ Finset.range L, pulse (mass r) (positive r) (negative r) j) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [hagrees r (Finset.mem_range.mp hr), coassigned_pulse_zero]
  simp [perturbed, hsum]

theorem exists_largest_separated (positive negative : ℕ → Agent) (L : ℕ)
    (hseparated : ∃ r < L, positive r ≠ negative r) :
    ∃ r < L, positive r ≠ negative r ∧
      ∀ s < L, r < s → positive s = negative s := by
  classical
  let separated := (Finset.range L).filter (fun r => positive r ≠ negative r)
  have hnonempty : separated.Nonempty := by
    obtain ⟨r, hr, hn⟩ := hseparated
    exact ⟨r, by simp [separated, hr, hn]⟩
  let r := separated.max' hnonempty
  have hrmem : r ∈ separated := Finset.max'_mem separated hnonempty
  have hrinfo : r < L ∧ positive r ≠ negative r := by
    simpa only [separated, Finset.mem_filter, Finset.mem_range] using hrmem
  refine ⟨r, hrinfo.1, hrinfo.2, ?_⟩
  intro s hs hrs
  by_contra hn
  have hsmem : s ∈ separated := by simp [separated, hs, hn]
  have hsr : s ≤ r := Finset.le_max' separated s hsmem
  omega

/-- Pairs later than the last separated pair vanish as actual value sums. -/
theorem comparison_sum_at_last (mass : ℕ → ℝ) (positive negative : ℕ → Agent)
    (L r : ℕ) (own other : Agent) (hr : r < L)
    (hlater : ∀ s < L, r < s → positive s = negative s) :
    (∑ s ∈ Finset.range L,
      (pulse (mass s) (positive s) (negative s) other -
        pulse (mass s) (positive s) (negative s) own)) =
      (∑ s ∈ Finset.range r,
        (pulse (mass s) (positive s) (negative s) other -
          pulse (mass s) (positive s) (negative s) own)) +
        (pulse (mass r) (positive r) (negative r) other -
          pulse (mass r) (positive r) (negative r) own) := by
  rw [← Finset.sum_range_succ]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hr))
  intro s hs hnot
  have hsL := Finset.mem_range.mp hs
  have hrs : r < s := by simp only [Finset.mem_range] at hnot; omega
  rw [hlater s hsL hrs, coassigned_pulse_zero, coassigned_pulse_zero]
  ring

/-- The table entry bound derives the baseline comparison bound -2T. The
earlier terms are bounded individually, rather than assuming their final sum. -/
theorem last_separated_pulse_forces_envy (base : Agent → Agent → ℝ)
    (mass : ℕ → ℝ) (positive negative : ℕ → Agent) (L r : ℕ)
    (T ε : ℝ) (observer : Agent)
    (hbase : ∀ i j, |base i j| ≤ T)
    (hmass : ∀ s < L, 0 ≤ mass s)
    (hr : r < L) (hseparated : positive r ≠ negative r)
    (hlater : ∀ s < L, r < s → positive s = negative s)
    (hobserver : observer ≠ positive r)
    (hlarge : 2 * T + 2 * (∑ s ∈ Finset.range r, mass s) + ε < mass r) :
    ε < perturbed base mass positive negative L observer (positive r) -
      perturbed base mass positive negative L observer observer := by
  have hbaseLower : -2 * T ≤ base observer (positive r) - base observer observer := by
    have ho := (abs_le.mp (hbase observer observer)).2
    have ht := (abs_le.mp (hbase observer (positive r))).1
    linarith
  have hearly : -2 * (∑ s ∈ Finset.range r, mass s) ≤
      ∑ s ∈ Finset.range r,
        (pulse (mass s) (positive s) (negative s) (positive r) -
          pulse (mass s) (positive s) (negative s) observer) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    exact pulse_comparison_lower (mass s) (positive s) (negative s) observer (positive r)
      (hmass s (lt_trans (Finset.mem_range.mp hs) hr))
  have hlast := separated_pulse_gain (mass r) (positive r) (negative r) observer
    (hmass r hr) hseparated hobserver
  have hidentity :
      perturbed base mass positive negative L observer (positive r) -
        perturbed base mass positive negative L observer observer =
      (base observer (positive r) - base observer observer) +
        ∑ s ∈ Finset.range L,
          (pulse (mass s) (positive s) (negative s) (positive r) -
            pulse (mass s) (positive s) (negative s) observer) := by
    simp only [perturbed, Finset.sum_sub_distrib]
    ring
  rw [hidentity, comparison_sum_at_last mass positive negative L r observer (positive r) hr hlater]
  linarith

theorem any_separated_pulse_forces_envy [Nontrivial Agent]
    (base : Agent → Agent → ℝ) (mass : ℕ → ℝ) (positive negative : ℕ → Agent)
    (L : ℕ) (T ε : ℝ) (hbase : ∀ i j, |base i j| ≤ T)
    (hmass : ∀ r < L, 0 ≤ mass r)
    (hlarge : ∀ r < L, 2 * T + 2 * (∑ s ∈ Finset.range r, mass s) + ε < mass r)
    (hseparated : ∃ r < L, positive r ≠ negative r) :
    ∃ i j, ε < perturbed base mass positive negative L i j -
      perturbed base mass positive negative L i i := by
  obtain ⟨r, hr, hsep, hlater⟩ := exists_largest_separated positive negative L hseparated
  obtain ⟨i, hi⟩ := exists_ne (positive r)
  exact ⟨i, positive r, last_separated_pulse_forces_envy base mass positive negative L r T ε i
    hbase hmass hr hsep hlater hi (hlarge r hr)⟩

/-- A correct perturbed allocation was already correct and every pure pulse
pair was assigned to the same owner. This rules out repairing old errors. -/
theorem perturbed_correct_implies_base_correct_and_agreement [Nontrivial Agent]
    (base : Agent → Agent → ℝ) (mass : ℕ → ℝ) (positive negative : ℕ → Agent)
    (L : ℕ) (T ε : ℝ) (hbase : ∀ i j, |base i j| ≤ T)
    (hmass : ∀ r < L, 0 ≤ mass r)
    (hlarge : ∀ r < L, 2 * T + 2 * (∑ s ∈ Finset.range r, mass s) + ε < mass r)
    (hcorrect : ApproxEF (perturbed base mass positive negative L) ε) :
    ApproxEF base ε ∧ ∀ r < L, positive r = negative r := by
  classical
  have hagrees : ∀ r < L, positive r = negative r := by
    by_contra hn
    push Not at hn
    obtain ⟨i, j, henvy⟩ := any_separated_pulse_forces_envy base mass positive negative
      L T ε hbase hmass hlarge hn
    exact (not_lt_of_ge (hcorrect i j)) henvy
  refine ⟨?_, hagrees⟩
  rwa [all_coassigned_preserves_values base mass positive negative L hagrees] at hcorrect

theorem no_repair_of_incorrect_output [Nontrivial Agent]
    (base : Agent → Agent → ℝ) (mass : ℕ → ℝ) (positive negative : ℕ → Agent)
    (L : ℕ) (T ε : ℝ) (hbase : ∀ i j, |base i j| ≤ T)
    (hmass : ∀ r < L, 0 ≤ mass r)
    (hlarge : ∀ r < L, 2 * T + 2 * (∑ s ∈ Finset.range r, mass s) + ε < mass r)
    (hincorrect : ¬ ApproxEF base ε) :
    ¬ ApproxEF (perturbed base mass positive negative L) ε := by
  intro hcorrect
  exact hincorrect
    (perturbed_correct_implies_base_correct_and_agreement base mass positive negative L T ε
      hbase hmass hlarge hcorrect).1

/-- An explicit finite superincreasing sequence; its surplus over the needed
threshold is exactly two at every index. -/
def commonMass (T ε : ℝ) (r : ℕ) : ℝ := (2 * T + ε + 2) * 3 ^ r

theorem commonMass_step (T ε : ℝ) (r : ℕ) :
    commonMass T ε (r + 1) = 3 * commonMass T ε r := by
  simp only [commonMass, pow_succ]
  ring

theorem commonMass_budget_identity (T ε : ℝ) (r : ℕ) :
    commonMass T ε r = 2 * T + 2 * (∑ s ∈ Finset.range r, commonMass T ε s) + ε + 2 := by
  induction r with
  | zero => simp [commonMass]
  | succ r ih =>
    rw [commonMass_step, Finset.sum_range_succ]
    linarith

theorem commonMass_positive (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 ≤ ε) (r : ℕ) :
    0 < commonMass T ε r := by
  unfold commonMass
  positivity

theorem commonMass_exceeds_strong_budget (T ε : ℝ) (r : ℕ) :
    2 * T + 2 * (∑ s ∈ Finset.range r, commonMass T ε s) + ε + 1 < commonMass T ε r := by
  rw [commonMass_budget_identity]
  linarith

section FiniteEventAccounting

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

omit [Fintype Outcome] in
/-- The pulse theorem gives the actual four-way success implication after the
explicit replay and pure-support table identities are supplied. In particular,
the last event requires correctness of the base output, not just agreement. -/
theorem success_event_cover [Nontrivial Agent]
    (base actual : Outcome → Agent → Agent → ℝ)
    (mass : ℕ → ℝ) (positive negative : Outcome → ℕ → Agent)
    (L : ℕ) (T ε : ℝ) (retained replay returns pure success : Finset Outcome)
    (hbase : ∀ ω i j, |base ω i j| ≤ T)
    (hmass : ∀ r < L, 0 ≤ mass r)
    (hlarge : ∀ r < L, 2 * T + 2 * (∑ s ∈ Finset.range r, mass s) + ε < mass r)
    (hcorrect : ∀ ω ∈ success, ApproxEF (actual ω) ε)
    (hreplay : ∀ ω ∈ retained, ω ∈ replay → ω ∈ success → ω ∈ returns)
    (hrealize : ∀ ω ∈ retained, ω ∈ replay → ω ∈ returns → ω ∈ pure →
      actual ω = perturbed (base ω) mass (positive ω) (negative ω) L) :
    ∀ ω ∈ success,
      ω ∉ retained ∨ (ω ∈ retained ∧ ω ∉ replay) ∨
      (ω ∈ retained ∧ ω ∈ returns ∧ ω ∉ pure) ∨
      (ω ∈ retained ∧ ω ∈ returns ∧ ApproxEF (base ω) ε ∧
        ∀ r < L, positive ω r = negative ω r) := by
  intro ω hs
  by_cases hretained : ω ∈ retained
  · by_cases hr : ω ∈ replay
    · have hreturns := hreplay ω hretained hr hs
      by_cases hp : ω ∈ pure
      · have hc := hcorrect ω hs
        rw [hrealize ω hretained hr hreturns hp] at hc
        have hbaseAndAgreement := perturbed_correct_implies_base_correct_and_agreement
          (base ω) mass (positive ω) (negative ω) L T ε (hbase ω) hmass hlarge hc
        exact Or.inr (Or.inr (Or.inr ⟨hretained, hreturns, hbaseAndAgreement⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hretained, hreturns, hp⟩))
    · exact Or.inr (Or.inl ⟨hretained, hr⟩)
  · exact Or.inl hretained

/-- A finite weighted union bound proved by summing the actual indicators. -/
theorem mass_le_four_event_masses (weight : Outcome → ℝ)
    (success first second third fourth : Finset Outcome)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hcover : ∀ ω ∈ success, ω ∈ first ∨ ω ∈ second ∨ ω ∈ third ∨ ω ∈ fourth) :
    eventMass weight success ≤ eventMass weight first + eventMass weight second +
      eventMass weight third + eventMass weight fourth := by
  classical
  have hnonnegative (event : Finset Outcome) (ω : Outcome) :
      0 ≤ if ω ∈ event then weight ω else 0 := by
    split_ifs
    · exact hweight ω
    · exact le_rfl
  have hpoint (ω : Outcome) :
      (if ω ∈ success then weight ω else 0) ≤
        (if ω ∈ first then weight ω else 0) + (if ω ∈ second then weight ω else 0) +
        (if ω ∈ third then weight ω else 0) + (if ω ∈ fourth then weight ω else 0) := by
    by_cases hs : ω ∈ success
    · rw [ite_eq_left hs]
      rcases hcover ω hs with hfirst | hsecond | hthird | hfourth
      · rw [ite_eq_left hfirst]
        linarith [hnonnegative second ω, hnonnegative third ω, hnonnegative fourth ω]
      · rw [ite_eq_left hsecond]
        linarith [hnonnegative first ω, hnonnegative third ω, hnonnegative fourth ω]
      · rw [ite_eq_left hthird]
        linarith [hnonnegative first ω, hnonnegative second ω, hnonnegative fourth ω]
      · rw [ite_eq_left hfourth]
        linarith [hnonnegative first ω, hnonnegative second ω, hnonnegative third ω]
    · rw [ite_eq_right hs]
      linarith [hnonnegative first ω, hnonnegative second ω,
        hnonnegative third ω, hnonnegative fourth ω]
  simpa only [eventMass, Finset.sum_add_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)

/-- The four actual event estimates give a strict delta bound. No probability
normalization or independence is needed for this finite weighted implication. -/
theorem finite_four_event_budget (weight : Outcome → ℝ)
    (success first second third fourth : Finset Outcome) (δ : ℝ)
    (hδ : 0 < δ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hcover : ∀ ω ∈ success, ω ∈ first ∨ ω ∈ second ∨ ω ∈ third ∨ ω ∈ fourth)
    (hfirst : eventMass weight first ≤ 3 * δ / 8)
    (hsecond : eventMass weight second ≤ δ / 8)
    (hthird : eventMass weight third ≤ δ / 8)
    (hfourth : eventMass weight fourth ≤ δ / 8) :
    eventMass weight success ≤ 3 * δ / 4 ∧ eventMass weight success < δ := by
  have hsum := mass_le_four_event_masses weight success first second third fourth hweight hcover
  constructor <;> linarith

end FiniteEventAccounting

end EnvyFreeResearch.R6MixedMonteCarlo

#print axioms EnvyFreeResearch.R6MixedMonteCarlo.coassigned_pulse_zero
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.owned_mass_abs_le_variation
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.pulse_value_bounds
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.pulse_comparison_lower
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.separated_pulse_gain
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.all_coassigned_preserves_values
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.exists_largest_separated
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.comparison_sum_at_last
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.last_separated_pulse_forces_envy
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.any_separated_pulse_forces_envy
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.perturbed_correct_implies_base_correct_and_agreement
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.no_repair_of_incorrect_output
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.commonMass_step
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.commonMass_budget_identity
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.commonMass_positive
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.commonMass_exceeds_strong_budget
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.success_event_cover
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.mass_le_four_event_masses
#print axioms EnvyFreeResearch.R6MixedMonteCarlo.finite_four_event_budget
