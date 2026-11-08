import EnvyFreeResearch.Full.UpperRepairJobs
import Mathlib.Data.Fin.Rev

/-!
# Minimum-assignment isolation for chores

Reversing witness order, negating its cached values, and reversing each
uniform threshold transforms the actual chore table into its negative.
The tape transformation preserves its law, so the maximizing proof applies
to the actual minimizing assignment without a new probabilistic premise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperChoreIsolation

open UpperSeeds UpperSeedProbability UpperAssignment UpperSeedMatrix
  UpperRepairIsolation UpperRepairJobs UpperAssignmentIsolation UpperThresholdProduct

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent] {M L : ℕ}

def reverseSystem (S : SeedSystem Agent M L) : SeedSystem Agent M L where
  left := S.left
  right := S.right
  column := S.column
  weight job a row := -S.weight job a.rev row

def reverseDraw (draw : Fin M → Fin (L + 1)) : Fin M → Fin (L + 1) :=
  fun job => (draw job).rev

omit [Fintype Agent] [DecidableEq Agent] in
theorem reverse_difference (S : SeedSystem Agent M L) (job : Fin (M + 1)) (a : Fin L) :
    difference (reverseSystem S) job a = -difference S job a.rev := by
  dsimp [difference, reverseSystem]
  ring

theorem kept_reverse (gamma : Fin L → ℝ) (t : Fin (L + 1)) (a : Fin L) :
    kept (fun b => -gamma b.rev) t.rev a ↔ kept gamma t a.rev := by
  have hlt : a.val < t.rev.val ↔ ¬a.rev.val < t.val := by
    simp only [Fin.val_rev]
    have ha := a.isLt
    have ht := t.isLt
    omega
  by_cases h : a.rev.val < t.val
  · simp only [kept, hlt, h, not_true_eq_false, ite_false, ite_true, neg_lt_zero]
  · simp only [kept, hlt, h, not_false_eq_true, ite_false, ite_true, neg_pos]

omit [Fintype Agent] [DecidableEq Agent] in
theorem rowSeed_reverse (S : SeedSystem Agent M L) (job : Fin (M + 1)) (row : Agent)
    (t : Fin (L + 1)) :
    rowSeed (reverseSystem S) job row t.rev = -rowSeed S job row t := by
  have hkept (a : Fin L) : kept (difference (reverseSystem S) job) t.rev a ↔
      kept (difference S job) t a.rev := by
    have hfun : difference (reverseSystem S) job = fun b => -difference S job b.rev :=
      funext (reverse_difference S job)
    rw [hfun]
    exact kept_reverse _ _ _
  have hsum := Equiv.sum_comp Fin.revPerm
    (fun a : Fin L => if kept (difference S job) t a then S.weight job a row else 0)
  dsimp only [rowSeed]
  simp only [hkept]
  change (∑ a : Fin L, if kept (difference S job) t a.rev then -S.weight job a.rev row else 0) = _
  calc
    _ = ∑ a : Fin L, -(if kept (difference S job) t a.rev then S.weight job a.rev row else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = -(∑ a : Fin L, if kept (difference S job) t a.rev then S.weight job a.rev row else 0) := by
      rw [Finset.sum_neg_distrib]
    _ = _ := congrArg Neg.neg hsum

omit [Fintype Agent] in
/-- The reversed seed data on the reversed tape gives exactly the negative
of the original cached matrix. -/
theorem matrix_reverse (S : SeedSystem Agent M L) (old : Agent → Agent → ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) :
    matrix (reverseSystem S) (fun i j => -old i j) (reverseDraw draw) =
      fun i j => -matrix S old draw i j := by
  funext row column
  have hterm (job : Fin (M + 1)) :
      contribution (reverseSystem S) (reverseDraw draw) row column job =
        -contribution S draw row column job := by
    dsimp only [contribution, reverseDraw]
    rw [rowSeed_reverse]
    change (if S.column job = column then -rowSeed S job row (draw job) else 0) = _
    split_ifs <;> simp
  simp only [UpperSeedMatrix.matrix, hterm, Finset.sum_neg_distrib]
  ring

theorem reverse_threshold_preserves :
    MeasurePreserving (Fin.rev : Fin (L + 1) → Fin (L + 1)) thresholdLaw thresholdLaw := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_of_countable _) hs, thresholdLaw, uniformOn_univ, uniformOn_univ]
  have heq : Fin.rev ⁻¹' s = Fin.rev '' s := by
    ext t
    constructor
    · intro h
      exact ⟨t.rev, h, Fin.rev_rev t⟩
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
  rw [heq, Measure.count_injective_image Fin.rev_injective]

theorem reverse_tape_preserves :
    MeasurePreserving (reverseDraw : (Fin M → Fin (L + 1)) → _) (tapeLaw M L) (tapeLaw M L) :=
  measurePreserving_pi _ _ (fun _ => reverse_threshold_preserves)

omit [Fintype Agent] [DecidableEq Agent] in
theorem reverse_covers (S : SeedSystem Agent M L) (hcover : Covers S) :
    Covers (reverseSystem S) := hcover

/-- The general complete seed-system bound for the actual minimum
assignment. Its edge sum is expressed through maximization of the negative
table, definitionally the `minimize` assignment. -/
theorem chore_positive_margin_probability (S : SeedSystem Agent M L) (hcover : Covers S)
    (old A : Agent → Agent → ℝ) (hA : ∀ i h, 0 ≤ A i h) (hsym : ∀ i h, A i h = A h i)
    (lam a : ℝ) (hlam : 0 ≤ lam) (ha : 0 < a) (haone : a ≤ 1)
    (hcap : 0 < 1 - Fintype.card Agent * a)
    (hgap : ∀ job r, A (S.left job) (S.right job) / 3 ≤ |difference S job r|) :
    tapeLaw (M + 1) L {draw | ∃ transfer : Equiv.Perm Agent,
      0 < margin (fun i j => -matrix S old draw i j) A lam transfer} ≤
      ENNReal.ofReal (((M + 1 : ℕ) *
        ((12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ))) /
          (1 - Fintype.card Agent * a)) := by
  have h := positive_margin_probability (reverseSystem S) (reverse_covers S hcover)
    (fun i j => -old i j) A hA hsym lam a hlam ha haone hcap
    (fun job r => by
      change A (S.left job) (S.right job) / 3 ≤ |difference (reverseSystem S) job r|
      rw [reverse_difference, abs_neg]
      exact hgap job r.rev)
  let bad : Set (Fin (M + 1) → Fin (L + 1)) := {draw | ∃ transfer : Equiv.Perm Agent,
    0 < margin (matrix (reverseSystem S) (fun i j => -old i j) draw) A lam transfer}
  have heq : {draw | ∃ transfer : Equiv.Perm Agent,
      0 < margin (fun i j => -matrix S old draw i j) A lam transfer} = reverseDraw ⁻¹' bad := by
    ext draw
    simp only [Set.mem_preimage, bad, Set.mem_ofPred_eq, matrix_reverse]
  rw [heq, reverse_tape_preserves.measure_preimage (Set.to_countable bad).measurableSet.nullMeasurableSet]
  exact h

/-- With all unordered-pair/column jobs explicitly enumerated, chores have
the same exact isolation bound as cake on the original physical seed tape. -/
theorem chore_isolation_probability {k L : ℕ} (hk : 2 ≤ k)
    (weights : Job k → Fin L → Fin k → ℝ) (old A : Fin k → Fin k → ℝ)
    (hA : ∀ i h, 0 ≤ A i h) (hsym : ∀ i h, A i h = A h i)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : ∀ job : Job k, ∀ r,
      A job.1.1.1 job.1.1.2 / 3 ≤ |weights job r job.1.1.1 - weights job r job.1.1.2|) :
    tapeLaw (jobCount k - 1 + 1) L {draw | ∃ transfer : Equiv.Perm (Fin k),
      0 < margin (fun i j => -matrix (system hk weights) old draw i j) A lam transfer} ≤
        ENNReal.ofReal ((k : ℝ)^2 * (k - 1 : ℝ) * (12 * lam * Real.log (2 * k) + 1) /
          (L + 1 : ℕ)) := by
  let S := system hk weights
  have h := isolation_probability hk (fun job r row => -weights job r.rev row)
    (fun i j => -old i j) A hA hsym lam hlam (fun job r => by
      have heq : -weights job r.rev job.1.1.1 - -weights job r.rev job.1.1.2 =
          -(weights job r.rev job.1.1.1 - weights job r.rev job.1.1.2) := by ring
      rw [heq, abs_neg]
      exact hgap job r.rev)
  change tapeLaw (jobCount k - 1 + 1) L {draw | ∃ transfer,
    0 < margin (matrix (reverseSystem S) (fun i j => -old i j) draw) A lam transfer} ≤ _ at h
  let bad : Set (Fin (jobCount k - 1 + 1) → Fin (L + 1)) := {draw | ∃ transfer,
    0 < margin (matrix (reverseSystem S) (fun i j => -old i j) draw) A lam transfer}
  have heq : {draw | ∃ transfer : Equiv.Perm (Fin k),
      0 < margin (fun i j => -matrix S old draw i j) A lam transfer} = reverseDraw ⁻¹' bad := by
    ext draw
    simp only [Set.mem_preimage, bad, Set.mem_ofPred_eq, matrix_reverse]
  change tapeLaw (jobCount k - 1 + 1) L {draw | ∃ transfer,
    0 < margin (fun i j => -matrix S old draw i j) A lam transfer} ≤ _
  rw [heq, reverse_tape_preserves.measure_preimage (Set.to_countable bad).measurableSet.nullMeasurableSet]
  exact h

/-- Chore edge weights use the actual minimum-sum assignment and the
manuscript's direction: each row compares its own package with the package
specified by the transfer. -/
theorem chore_margin_eq (V A : Agent → Agent → ℝ) (lam : ℝ) (transfer : Equiv.Perm Agent) :
    margin (fun i j => -V i j) A lam transfer = ∑ i ∈ transfer.support,
      (V i (minimize V i) - V i (minimize V (transfer i)) + 2 * lam * A i (transfer i)) := by
  unfold margin minimize
  apply Finset.sum_congr rfl
  intro i _
  ring

end EnvyFreeResearch.Full.UpperChoreIsolation
