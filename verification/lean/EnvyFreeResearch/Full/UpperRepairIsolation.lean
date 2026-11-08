import EnvyFreeResearch.Full.UpperSeedMatrix
import EnvyFreeResearch.Full.UpperAssignmentIsolation

/-!
# Whole-matrix assignment isolation

The seed jobs cover every unordered row pair and column. A positive
augmented transfer selects distinct jobs because its transferred columns are
distinct, including in a two-cycle. Summing the proved product expectations
and applying Markov yields a whole-trial bound, with no conditioning on the
winning assignment.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperRepairIsolation

open UpperAssignment UpperAssignmentIsolation UpperSeedProbability
  UpperSeedMatrix UpperThresholdProduct

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent] {M L : ℕ}

/-- A structural indexing condition, independent of all real entries and
threshold outcomes. Both orientations use the same unordered pair job. -/
def Covers (S : SeedSystem Agent M L) : Prop :=
  ∀ i h : Agent, i ≠ h → ∀ column : Agent, ∃ job,
    S.column job = column ∧
      ((S.left job = i ∧ S.right job = h) ∨ (S.left job = h ∧ S.right job = i))

def jobCharge (S : SeedSystem Agent M L) (old A : Agent → Agent → ℝ) (lam a : ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) : ℝ :=
  max (charge (A (S.left job) (S.right job)) lam (forcedDifference S old job draw) - a) 0

def totalCharge (S : SeedSystem Agent M L) (old A : Agent → Agent → ℝ) (lam a : ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) : ℝ :=
  ∑ job, jobCharge S old A lam a draw job

theorem charge_neg (A lam value : ℝ) : charge A lam (-value) = charge A lam value := by
  simp [charge]

theorem charge_sub_symm (A lam x y : ℝ) : charge A lam (x - y) = charge A lam (y - x) := by
  rw [← neg_sub x y, charge_neg]

/-- The moving rows use distinct pair-column jobs because a permutation
cannot transfer the same column twice. -/
theorem cycle_charge_le_total (S : SeedSystem Agent M L) (hcover : Covers S)
    (old A : Agent → Agent → ℝ) (hsym : ∀ i h, A i h = A h i) (lam a : ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) (transfer : Equiv.Perm Agent) :
    (∑ i ∈ transfer.support,
      max (charge (A i (transfer i)) lam (gap (matrix S old draw) i (transfer i)) - a) 0) ≤
        totalCharge S old A lam a draw := by
  let V := matrix S old draw
  have hex (i : Agent) : ∃ job : Fin (M + 1), i ∈ transfer.support →
      S.column job = maximize V (transfer i) ∧
        ((S.left job = i ∧ S.right job = transfer i) ∨
          (S.left job = transfer i ∧ S.right job = i)) := by
    by_cases hi : i ∈ transfer.support
    · obtain ⟨job, hj⟩ := hcover i (transfer i) (Ne.symm (Equiv.Perm.mem_support.mp hi))
        (maximize V (transfer i))
      exact ⟨job, fun _ => hj⟩
    · exact ⟨0, fun h => False.elim (hi h)⟩
  choose pick hpick using hex
  have hinj : Set.InjOn pick (transfer.support : Set Agent) := by
    intro i hi h hh heq
    apply transfer.injective
    apply (maximize V).injective
    exact ((hpick i hi).1.symm.trans (congrArg S.column heq)).trans (hpick h hh).1
  have heq (i : Agent) (hi : i ∈ transfer.support) :
      jobCharge S old A lam a draw (pick i) =
        max (charge (A i (transfer i)) lam (gap V i (transfer i)) - a) 0 := by
    obtain ⟨hcolumn, hpair⟩ := hpick i hi
    rcases hpair with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · simp only [jobCharge, forcedDifference, hleft, hright, hcolumn, gap, V]
    · simp only [jobCharge, forcedDifference, hleft, hright, hcolumn, gap, V]
      rw [hsym (transfer i) i, charge_sub_symm]
  have hsubset : transfer.support.image pick ⊆ (Finset.univ : Finset (Fin (M + 1))) :=
    Finset.subset_univ _
  calc
    _ = ∑ job ∈ transfer.support.image pick, jobCharge S old A lam a draw job := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun i hi => (heq i hi).symm)
    _ ≤ ∑ job, jobCharge S old A lam a draw job :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => le_max_right _ _)
    _ = _ := rfl

/-- Every positive augmented transfer forces a large value of the fixed
sum over all pair-column jobs; its choice may depend on every threshold. -/
theorem positive_margin_total_charge (S : SeedSystem Agent M L) (hcover : Covers S)
    (old A : Agent → Agent → ℝ) (hA : ∀ i h, 0 ≤ A i h) (hsym : ∀ i h, A i h = A h i)
    (lam a : ℝ) (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (draw : Fin (M + 1) → Fin (L + 1)) (transfer : Equiv.Perm Agent)
    (hpositive : 0 < margin (matrix S old draw) A lam transfer) :
    1 - Fintype.card Agent * a ≤ totalCharge S old A lam a draw :=
  (positive_margin_truncated_charge (matrix S old draw) A lam a transfer hA hlam ha hpositive).trans
    (cycle_charge_le_total S hcover old A hsym lam a draw transfer)

theorem mean_bound_nonnegative (lam a : ℝ) (hlam : 0 ≤ lam) (ha : 0 < a) (haone : a ≤ 1) :
    0 ≤ (12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ) := by
  have hlog := Real.log_nonneg ((le_div_iff₀ ha).mpr (by simpa using haone))
  have hprod : 0 ≤ 12 * lam * Real.log (1 / a) := by positivity
  exact div_nonneg (by linarith) (by positivity)

theorem jobCharge_expectation (S : SeedSystem Agent M L) (old A : Agent → Agent → ℝ)
    (job : Fin (M + 1)) (lam a : ℝ) (hA : ∀ i h, 0 ≤ A i h)
    (hlam : 0 ≤ lam) (ha : 0 < a) (haone : a ≤ 1)
    (hgap : ∀ r, A (S.left job) (S.right job) / 3 ≤ |difference S job r|) :
    (∫ draw, jobCharge S old A lam a draw job ∂tapeLaw (M + 1) L) ≤
      (12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ) := by
  by_cases hzero : A (S.left job) (S.right job) = 0
  · simpa [jobCharge, charge, hzero, ha.le] using mean_bound_nonnegative (L := L) lam a hlam ha haone
  · exact matrix_charge_expectation S old job _ lam a
      (lt_of_le_of_ne (hA _ _) (Ne.symm hzero)) hlam ha haone hgap

theorem totalCharge_expectation (S : SeedSystem Agent M L) (old A : Agent → Agent → ℝ)
    (lam a : ℝ) (hA : ∀ i h, 0 ≤ A i h) (hlam : 0 ≤ lam) (ha : 0 < a) (haone : a ≤ 1)
    (hgap : ∀ job r, A (S.left job) (S.right job) / 3 ≤ |difference S job r|) :
    (∫ draw, totalCharge S old A lam a draw ∂tapeLaw (M + 1) L) ≤
      (M + 1 : ℕ) * ((12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ)) := by
  simp only [totalCharge]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have h := Finset.sum_le_sum (fun job (_ : job ∈ (Finset.univ : Finset (Fin (M + 1)))) =>
    jobCharge_expectation S old A job lam a hA hlam ha haone (hgap job))
  simpa using h

/-- Actual whole-trial failure probability on the independent threshold law.
The event ranges over all positive augmented permutations of the optimizing
assignment, rather than fixing that assignment before sampling. -/
theorem positive_margin_probability (S : SeedSystem Agent M L) (hcover : Covers S)
    (old A : Agent → Agent → ℝ) (hA : ∀ i h, 0 ≤ A i h) (hsym : ∀ i h, A i h = A h i)
    (lam a : ℝ) (hlam : 0 ≤ lam) (ha : 0 < a) (haone : a ≤ 1)
    (hcap : 0 < 1 - Fintype.card Agent * a)
    (hgap : ∀ job r, A (S.left job) (S.right job) / 3 ≤ |difference S job r|) :
    tapeLaw (M + 1) L {draw | ∃ transfer : Equiv.Perm Agent,
      0 < margin (matrix S old draw) A lam transfer} ≤
      ENNReal.ofReal (((M + 1 : ℕ) *
        ((12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ))) /
          (1 - Fintype.card Agent * a)) := by
  let cap : ℝ := 1 - Fintype.card Agent * a
  have hnonneg : ∀ draw, 0 ≤ totalCharge S old A lam a draw :=
    fun _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hnonneg)
    (show Integrable (totalCharge S old A lam a) (tapeLaw (M + 1) L) from Integrable.of_finite) cap
  have hmean := totalCharge_expectation S old A lam a hA hlam ha haone hgap
  have hbound : (tapeLaw (M + 1) L).real {draw | cap ≤ totalCharge S old A lam a draw} ≤
      ((M + 1 : ℕ) * ((12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ))) / cap := by
    apply (le_div_iff₀ hcap).mpr
    simpa only [cap, mul_comm] using hm.trans hmean
  calc
    _ ≤ tapeLaw (M + 1) L {draw | cap ≤ totalCharge S old A lam a draw} := by
      apply measure_mono
      rintro draw ⟨transfer, hpositive⟩
      exact positive_margin_total_charge S hcover old A hA hsym lam a hlam ha.le draw transfer hpositive
    _ = ENNReal.ofReal ((tapeLaw (M + 1) L).real
        {draw | cap ≤ totalCharge S old A lam a draw}) := (ofReal_measureReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end EnvyFreeResearch.Full.UpperRepairIsolation
