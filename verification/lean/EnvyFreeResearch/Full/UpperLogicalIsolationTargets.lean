import EnvyFreeResearch.Full.UpperLogicalIsolationPhysical
import EnvyFreeResearch.Full.UpperLogicalIsolationBudget
import EnvyFreeResearch.Full.UpperLogicalIsolationProbability

/-! Actual ideal targets from raw near-EF old snapshots and a passing preparation. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperLogicalPreparation UpperLogicalPreparationGuard UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable UpperRepairJobs UpperIdealPayments UpperSeedMatrix Chores
variable {n k : ℕ}

def cellCap (q : ℕ) (theta : I) : ℝ := 2 / ((theta : ℝ) * (q + 1 : ℝ))
def nearBudget (k q L : ℕ) (theta : I) (tau : ℝ) : ℝ :=
  2 * tau / (theta : ℝ) + k.choose 2 * L * cellCap q theta

def targetBudget (k q L : ℕ) (theta : I) (tau lam : ℝ) : ℝ :=
  k * nearBudget k q L theta tau + (k - 1 : ℕ) * (2 * lam * cellCap q theta)

section Correctness
variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem weights_bounds (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (labels : Parent k q → I)
    (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true)
    (j : Job k) (a : Fin L) (i : Fin k) :
    0 ≤ weights policy active origin q m L draw theta labels j a i ∧
      weights policy active origin q m L draw theta labels j a i ≤ cellCap q theta := by
  rw [weights_physical μ policy hpolicy active origin hgood hpositive]
  constructor
  · exact div_nonneg measureReal_nonneg measureReal_nonneg
  · have h := renormalized_small _ _ _ (1 / (q + 1 : ℝ)) (theta : ℝ) (hpositive i) htheta (by positivity)
      (UpperGridMerge.logical_cells_small μ policy hpolicy active origin hgood hpositive q m draw i (chosenCell policy active origin q m L draw theta labels j a))
      (passing_lower_mass μ policy hpolicy active origin hgood hpositive q m (requests k L) theta cap draw labels hpass i)
    simpa only [cellCap, div_eq_mul_inv, mul_inv_rev, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem disagreement_bound (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (labels : Parent k q → I)
    (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true) (i j : Fin k) :
    disagreement policy active origin q m draw theta labels i j ≤ cellCap q theta := by
  apply UpperPayments.cellGap_le _ _ (by positivity) _
    (passing_table_small μ policy hpolicy active origin hgood hpositive q m (requests k L) theta htheta cap draw labels hpass) i j
  intro r e
  change 0 ≤ UpperCorrectionSetup.table active (reserveState policy active origin q m draw theta labels)
    (UpperGridMerge.cuts policy active origin q m draw) r e
  rw [reserve_table_eq_scaled μ policy hpolicy active origin hgood hpositive]
  split_ifs
  · apply mul_nonneg
    · unfold multipliers
      rw [total_correct μ origin hgood,
        total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels)]
      exact div_nonneg measureReal_nonneg measureReal_nonneg
    · exact UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw r e
  · exact le_rfl

/-- Raw old near-EF inequalities normalize using the measured reserve lower
check, not an assumption about its conditional distribution. -/
theorem old_normalized_near (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ)
    (labels : Parent k q → I) (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true)
    (tau : ℝ) (htau : 0 ≤ tau) (i j d : Fin k)
    (hnear : (μ (active i)).real (domain (old j).cells) - (μ (active i)).real (domain (old d).cells) ≤
      tau * (μ (active i)).real (domain origin.cells)) :
    oldMatrix active old (reserveState policy active origin q m draw theta labels) i j -
      oldMatrix active old (reserveState policy active origin q m draw theta labels) i d ≤ 2 * tau / (theta : ℝ) := by
  rw [oldMatrix_physical μ policy hpolicy active origin hgood hpositive old hold,
    oldMatrix_physical μ policy hpolicy active origin hgood hpositive old hold, ← sub_div]
  exact renormalized_small _ _ _ tau (theta : ℝ) (hpositive i) htheta htau
    ((div_le_iff₀ (hpositive i)).mpr hnear)
    (passing_lower_mass μ policy hpolicy active origin hgood hpositive q m (requests k L) theta cap draw labels hpass i)

theorem actual_cake_targets (hk : 2 ≤ k) (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ)
    (labels : Parent k q → I) (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hnear : ∀ i j, (μ (active i)).real (domain (old j).cells) - (μ (active i)).real (domain (old i).cells) ≤
      tau * (μ (active i)).real (domain origin.cells))
    (lam : ℝ) (hlam : 0 ≤ lam) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    let V := cachedMatrix hk policy active origin old q m L draw theta labels pi threshold
    let A := disagreement policy active origin q m draw theta labels
    (∀ i, 0 ≤ cakeTargets V A lam i ∧ cakeTargets V A lam i ≤ targetBudget k q L theta tau lam) ∧
    (∑ i, cakeTargets V A lam i) ≤ k * targetBudget k q L theta tau lam := by
  dsimp only
  have hb := weights_bounds μ policy hpolicy active origin hgood hpositive q m L draw theta htheta cap labels hpass
  have hn := matrix_cake_near hk _ (fun j a i => (hb j a i).1) (cellCap q theta)
    (by unfold cellCap; positivity) (fun j a i => (hb j a i).2)
    (oldMatrix active old (reserveState policy active origin q m draw theta labels)) (2 * tau / (theta : ℝ))
    (fun i j => old_normalized_near μ policy hpolicy active origin hgood hpositive old hold q m L draw theta htheta cap labels hpass tau htau i j i (hnear i j)) pi threshold
  have ha := allowance_le _ (nearBudget k q L theta tau) (2 * lam * cellCap q theta) hn
  simp only [Fintype.card_fin] at ha
  have htargets := cakeTargets_bound (cachedMatrix hk policy active origin old q m L draw theta labels pi threshold)
    _ lam (cellCap q theta) hlam (by unfold cellCap; positivity)
    (disagreement_bound μ policy hpolicy active origin hgood hpositive q m L draw theta htheta cap labels hpass)
  constructor
  · exact fun i => ⟨(htargets i).1, (htargets i).2.trans ha⟩
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (htargets i).2.trans ha)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, targetBudget] using hs

theorem actual_chore_targets (hk : 2 ≤ k) (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ)
    (labels : Parent k q → I) (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hnear : ∀ i j, (μ (active i)).real (domain (old i).cells) - (μ (active i)).real (domain (old j).cells) ≤
      tau * (μ (active i)).real (domain origin.cells))
    (lam : ℝ) (hlam : 0 ≤ lam) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    let V := cachedMatrix hk policy active origin old q m L draw theta labels pi threshold
    let A := disagreement policy active origin q m draw theta labels
    (∀ i, 0 ≤ choreTargets V A lam (cellCap q theta) i ∧
      choreTargets V A lam (cellCap q theta) i ≤ targetBudget k q L theta tau lam) ∧
    (∑ i, choreTargets V A lam (cellCap q theta) i) ≤ k * targetBudget k q L theta tau lam := by
  dsimp only
  have hb := weights_bounds μ policy hpolicy active origin hgood hpositive q m L draw theta htheta cap labels hpass
  have hn := matrix_chore_near hk _ (fun j a i => (hb j a i).1) (cellCap q theta)
    (by unfold cellCap; positivity) (fun j a i => (hb j a i).2)
    (oldMatrix active old (reserveState policy active origin q m draw theta labels)) (2 * tau / (theta : ℝ))
    (fun i j => old_normalized_near μ policy hpolicy active origin hgood hpositive old hold q m L draw theta htheta cap labels hpass tau htau i i j (hnear i j)) pi threshold
  have ha := allowance_le (fun i j => -cachedMatrix hk policy active origin old q m L draw theta labels pi threshold i j)
    (nearBudget k q L theta tau) (2 * lam * cellCap q theta) (by simpa only [sub_neg_eq_add, cachedMatrix, seedSystem, nearBudget] using hn)
  simp only [Fintype.card_fin] at ha
  have htargets := choreTargets_bound (cachedMatrix hk policy active origin old q m L draw theta labels pi threshold)
    _ lam (cellCap q theta) hlam (by unfold cellCap; positivity)
    (disagreement_bound μ policy hpolicy active origin hgood hpositive q m L draw theta htheta cap labels hpass)
  constructor
  · exact fun i => ⟨(htargets i).1, (htargets i).2.trans ha⟩
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (htargets i).2.trans ha)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, targetBudget] using hs

end Correctness
end EnvyFreeResearch.Full.UpperLogicalIsolation
