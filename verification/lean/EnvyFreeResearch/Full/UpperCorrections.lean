import EnvyFreeResearch.Full.UpperWholePaymentsPhysical
import EnvyFreeResearch.Full.UpperIdealPayments

/-!
# Physical correction supply and acceptance

Pending whole-cell payments and already accepted corrected payments are
excluded literally. The numerical invariant gives every observer more than
seven eighths of the reserve at every reached correction, including a
correction that rejects. A disjoint correction preserves disjointness and
an exact owner target. The final algebra derives both cake and chore
margins from the concrete ideal-payment constructions.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperCorrections

variable {Agent : Type*} [Fintype Agent]

def blocked (completed : Finset Agent) (pending accepted : Agent → Set ℝ)
    (j : Agent) : Set ℝ := if j ∈ completed then accepted j else pending j

def correctionDomain (reserve : Set ℝ) (completed : Finset Agent)
    (pending accepted : Agent → Set ℝ) : Set ℝ :=
  reserve \ ⋃ j, blocked completed pending accepted j

theorem pending_mass_le (μ : Agent → Measure ℝ) (pending : Agent → Set ℝ)
    (t : Agent → ℝ) (A : Agent → Agent → ℝ) (lam : ℝ)
    (howner : ∀ j, (μ j).real (pending j) ≤ t j)
    (hgap : ∀ i j, |(μ i).real (pending j) - (μ j).real (pending j)| ≤
      (Fintype.card Agent : ℝ)^2 * A i j)
    (hA : ∀ i j, 0 ≤ A i j) (hsize : (Fintype.card Agent : ℝ)^2 ≤ lam)
    (i j : Agent) : (μ i).real (pending j) ≤ t j + lam * A i j := by
  have h := (le_abs_self _).trans (hgap i j)
  have hm := mul_le_mul_of_nonneg_right hsize (hA i j)
  linarith [howner j]

omit [Fintype Agent] in
theorem blocked_mass_le (μ : Agent → Measure ℝ) (completed : Finset Agent)
    (pending accepted : Agent → Set ℝ) (t : Agent → ℝ)
    (A : Agent → Agent → ℝ) (lam eta : ℝ) (hlam : 0 ≤ lam)
    (hA : ∀ i j, A i j ≤ eta)
    (hpending : ∀ i j, (μ i).real (pending j) ≤ t j + lam * A i j)
    (haccepted : ∀ i j, j ∈ completed → |(μ i).real (accepted j) - t j| ≤ lam * A i j)
    (i j : Agent) : (μ i).real (blocked completed pending accepted j) ≤ t j + lam * eta := by
  have hmul := mul_le_mul_of_nonneg_left (hA i j) hlam
  by_cases hj : j ∈ completed
  · have h := (le_abs_self _).trans (haccepted i j hj)
    simp only [blocked, ite_eq_left hj]
    linarith
  · simp only [blocked, ite_eq_right hj]
    linarith [hpending i j]

theorem excluded_mass_le (μ : Agent → Measure ℝ) (completed : Finset Agent)
    (pending accepted : Agent → Set ℝ) (t : Agent → ℝ) (lam eta : ℝ)
    (hblocked : ∀ i j, (μ i).real (blocked completed pending accepted j) ≤ t j + lam * eta)
    (i : Agent) : (μ i).real (⋃ j, blocked completed pending accepted j) ≤
      (∑ j, t j) + Fintype.card Agent * lam * eta := by
  calc
    _ ≤ ∑ j, (μ i).real (blocked completed pending accepted j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ j, (t j + lam * eta) := Finset.sum_le_sum (fun j _ => hblocked i j)
    _ = _ := by simp [Finset.sum_add_distrib]; ring

/-- This bound depends only on previously accepted corrections. The next
fresh correction need not pass its acceptance test. -/
theorem correction_supply (μ : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (reserve : Set ℝ) (hnormal : ∀ i, (μ i).real reserve = 1)
    (completed : Finset Agent) (pending accepted : Agent → Set ℝ)
    (t : Agent → ℝ) (lam eta : ℝ)
    (hblocked : ∀ i j, (μ i).real (blocked completed pending accepted j) ≤ t j + lam * eta)
    (htarget : (∑ j, t j) < 1 / 16) (hbudget : (Fintype.card Agent : ℝ) * lam * eta < 1 / 16)
    (i : Agent) : 7 / 8 < (μ i).real (correctionDomain reserve completed pending accepted) := by
  have hex := excluded_mass_le μ completed pending accepted t lam eta hblocked i
  have hdiff := le_measureReal_sdiff (μ := μ i) (s₁ := reserve)
    (s₂ := ⋃ j, blocked completed pending accepted j)
  rw [hnormal] at hdiff
  change 7 / 8 < (μ i).real (reserve \ ⋃ j, blocked completed pending accepted j)
  linarith

theorem target_lt_one_sixteenth (t : Agent → ℝ) (ht : ∀ j, 0 ≤ t j)
    (htarget : (∑ j, t j) < 1 / 16) (j : Agent) : t j < 1 / 16 :=
  (Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ j)).trans_lt htarget

theorem deficit_fits (μ : Agent → Measure ℝ) (domain : Set ℝ)
    (t eps : Agent → ℝ) (ht : ∀ j, 0 ≤ t j) (htarget : (∑ j, t j) < 1 / 16)
    (heps : ∀ j, 0 ≤ eps j ∧ eps j ≤ t j)
    (hsupply : ∀ j, 7 / 8 < (μ j).real domain) (j : Agent) :
    0 ≤ eps j ∧ eps j < (μ j).real domain := by
  refine ⟨(heps j).1, ?_⟩
  have h := target_lt_one_sixteenth t ht htarget j
  linarith [(heps j).2, hsupply j]

omit [Fintype Agent] in
theorem blocked_measurable (completed : Finset Agent) (pending accepted : Agent → Set ℝ)
    (hpending : ∀ j, MeasurableSet (pending j)) (haccepted : ∀ j, MeasurableSet (accepted j))
    (j : Agent) : MeasurableSet (blocked completed pending accepted j) := by
  dsimp [blocked]
  split_ifs <;> first | exact hpending j | exact haccepted j

theorem correctionDomain_measurable (reserve : Set ℝ) (hreserve : MeasurableSet reserve)
    (completed : Finset Agent) (pending accepted : Agent → Set ℝ)
    (hpending : ∀ j, MeasurableSet (pending j)) (haccepted : ∀ j, MeasurableSet (accepted j)) :
    MeasurableSet (correctionDomain reserve completed pending accepted) :=
  hreserve.diff (MeasurableSet.iUnion (blocked_measurable completed pending accepted hpending haccepted))

omit [Fintype Agent] in
theorem correction_disjoint_blocked (reserve : Set ℝ) (completed : Finset Agent)
    (pending accepted : Agent → Set ℝ) (C : Set ℝ)
    (hC : C ⊆ correctionDomain reserve completed pending accepted) (j : Agent) :
    Disjoint (blocked completed pending accepted j) C := by
  apply Set.disjoint_left.mpr
  intro z hz hzC
  exact (hC hzC).2 (mem_iUnion.mpr ⟨j, hz⟩)

omit [Fintype Agent] in
theorem pending_disjoint_correction (reserve : Set ℝ) (completed : Finset Agent)
    (pending accepted : Agent → Set ℝ) (C : Set ℝ)
    (hC : C ⊆ correctionDomain reserve completed pending accepted)
    (j : Agent) (hj : j ∉ completed) : Disjoint (pending j) C := by
  simpa only [blocked, ite_eq_right hj] using
    correction_disjoint_blocked reserve completed pending accepted C hC j

omit [Fintype Agent] in
theorem correction_union_disjoint_other (reserve : Set ℝ) (completed : Finset Agent)
    (pending accepted : Agent → Set ℝ)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (blocked completed pending accepted i) (blocked completed pending accepted j)))
    (C : Set ℝ) (hC : C ⊆ correctionDomain reserve completed pending accepted)
    (j : Agent) (hj : j ∉ completed) (i : Agent) (hij : i ≠ j) :
    Disjoint (pending j ∪ C) (blocked completed pending accepted i) := by
  apply disjoint_union_left.mpr
  constructor
  · simpa only [blocked, ite_eq_right hj] using (hdisjoint hij).symm
  · exact (correction_disjoint_blocked reserve completed pending accepted C hC i).symm

omit [Fintype Agent] in
theorem exact_corrected_owner (μ : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (pending : Agent → Set ℝ) (C : Set ℝ) (hC : MeasurableSet C) (j : Agent) (t : ℝ)
    (hdisjoint : Disjoint (pending j) C) (hown : (μ j).real C = t - (μ j).real (pending j)) :
    (μ j).real (pending j ∪ C) = t := by
  rw [measureReal_union hdisjoint hC, hown]
  ring

omit [Fintype Agent] in
/-- The physical half/quarter/quarter calculation includes the owner
correction in the foreign difference; it is not a bound on foreign mass
alone. -/
theorem corrected_error (μ : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (pending : Agent → Set ℝ) (C : Set ℝ) (hC : MeasurableSet C) (i j : Agent)
    (hdisjoint : Disjoint (pending j) C) (t lam A estimate : ℝ)
    (hown : (μ j).real C = t - (μ j).real (pending j))
    (hwhole : |(μ i).real (pending j) - (μ j).real (pending j)| ≤ lam * A / 2)
    (hestimate : |estimate| ≤ lam * A / 4)
    (herror : |((μ i).real C - (μ j).real C) - estimate| ≤ lam * A / 4) :
    |(μ i).real (pending j ∪ C) - t| ≤ lam * A := by
  rw [measureReal_union hdisjoint hC]
  have hid : (μ i).real (pending j) + (μ i).real C - t =
      ((μ i).real (pending j) - (μ j).real (pending j)) +
        (estimate + (((μ i).real C - (μ j).real C) - estimate)) := by linarith
  rw [hid]
  calc
    _ ≤ |(μ i).real (pending j) - (μ j).real (pending j)| +
        |estimate + (((μ i).real C - (μ j).real C) - estimate)| := abs_add_le _ _
    _ ≤ |(μ i).real (pending j) - (μ j).real (pending j)| +
        (|estimate| + |((μ i).real C - (μ j).real C) - estimate|) :=
      add_le_add le_rfl (abs_add_le _ _)
    _ ≤ lam * A := by linarith

section AcceptedMargins

variable [DecidableEq Agent]

/-- Once the physical payment tests pass, the actual maximizing assignment
and its constructed longest-path credits have the claimed cake margin. -/
theorem accepted_cake_margin (V A : Agent → Agent → ℝ) (lam : ℝ)
    (hdiag : ∀ i, A i i = 0) (haccept : UpperIdealPayments.findPositive V A lam = none)
    (payment : Agent → Agent → ℝ)
    (hown : ∀ j, payment j j = UpperIdealPayments.cakeTargets V A lam j)
    (herr : ∀ i j, |payment i j - UpperIdealPayments.cakeTargets V A lam j| ≤ lam * A i j)
    (i j : Agent) : lam * A i j ≤
      V i (UpperAssignment.maximize V i) + payment i i -
        (V i (UpperAssignment.maximize V j) + payment i j) := by
  have hideal := UpperIdealPayments.cake_ideal_inequalities V A lam hdiag haccept i j
  have herror := (le_abs_self _).trans (herr i j)
  rw [hown]
  linarith

/-- The minimizing assignment uses the constructed chore taxes; its margin
has the reversed cost orientation. -/
theorem accepted_chore_margin (V A : Agent → Agent → ℝ) (lam eta : ℝ)
    (hdiag : ∀ i, A i i = 0)
    (haccept : UpperIdealPayments.findPositive (fun r c => -V r c) A lam = none)
    (payment : Agent → Agent → ℝ)
    (hown : ∀ j, payment j j = UpperIdealPayments.choreTargets V A lam eta j)
    (herr : ∀ i j, |payment i j - UpperIdealPayments.choreTargets V A lam eta j| ≤ lam * A i j)
    (i j : Agent) : lam * A i j ≤
      V i (UpperAssignment.minimize V j) + payment i j -
        (V i (UpperAssignment.minimize V i) + payment i i) := by
  have hideal := UpperIdealPayments.chore_ideal_inequalities V A lam eta hdiag haccept i j
  have herror := (abs_le.mp (herr i j)).1
  rw [hown]
  linarith

end AcceptedMargins

end EnvyFreeResearch.Full.UpperCorrections
