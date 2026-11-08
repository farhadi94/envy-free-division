import EnvyFreeResearch.Full.UpperLogicalIsolationCore
import EnvyFreeResearch.Full.UpperIdealMeasurable

/-! Target budgets from actual finite seed contributions. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperSeedMatrix UpperRepairJobs UpperBatchPermutation UpperIdealPayments
variable {k L M : ℕ}

theorem rowSeed_nonnegative (S : SeedSystem (Fin k) M L)
    (hweight : ∀ j a i, 0 ≤ S.weight j a i) (j : Fin (M + 1)) (i : Fin k) (t : Fin (L + 1)) :
    0 ≤ rowSeed S j i t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hweight j a i
  · exact le_rfl

theorem rowSeed_le (S : SeedSystem (Fin k) M L) (eta : ℝ) (heta : 0 ≤ eta)
    (hweight : ∀ j a i, S.weight j a i ≤ eta) (j : Fin (M + 1)) (i : Fin k) (t : Fin (L + 1)) :
    rowSeed S j i t ≤ L * eta := by
  calc
    _ ≤ ∑ _a : Fin L, eta := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · exact hweight j a i
      · exact heta
    _ = _ := by simp

theorem column_job_count (hk : 2 ≤ k) (c : Fin k) (z : ℝ) :
    (∑ j : Fin (jobCount k - 1 + 1), if (jobEquiv hk j).2 = c then z else 0) = k.choose 2 * z := by
  rw [Equiv.sum_comp (jobEquiv hk) (fun j : Job k => if j.2 = c then z else 0)]
  simp only [Fintype.sum_prod_type, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Fintype.card_subtype]
  exact_mod_cast (by simpa only [Fintype.card_fin] using (Fintype.card_product_filter_lt (α := Fin k)))

theorem jobCount_le_cube (k : ℕ) : (jobCount k : ℝ) ≤ (k : ℝ)^3 := by
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
  have h := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) k)
  simpa only [jobCount, Nat.cast_mul, pow_succ] using h

theorem matrix_increment_bound (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (hzero : ∀ j a i, 0 ≤ w j a i) (eta : ℝ) (heta : 0 ≤ eta)
    (hsmall : ∀ j a i, w j a i ≤ eta) (old : Fin k → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (draw : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (i c : Fin k) :
    0 ≤ matrix (system hk (permutedWeights w pi)) old draw i c - old i c ∧
      matrix (system hk (permutedWeights w pi)) old draw i c - old i c ≤ k.choose 2 * L * eta := by
  have hn : ∀ j, 0 ≤ contribution (system hk (permutedWeights w pi)) draw i c j := by
    intro j
    unfold contribution
    split_ifs
    · exact rowSeed_nonnegative _ (fun j a i => hzero _ a i) j i _
    · exact le_rfl
  have hs : ∀ j, contribution (system hk (permutedWeights w pi)) draw i c j ≤
      if (jobEquiv hk j).2 = c then (L : ℝ) * eta else 0 := by
    intro j
    unfold contribution
    change (if (jobEquiv hk j).2 = c then _ else 0) ≤ _
    split_ifs
    · exact rowSeed_le _ eta heta (fun j a i => hsmall _ a i) j i _
    · exact le_rfl
  constructor
  · simpa only [matrix, add_sub_cancel_left] using Finset.sum_nonneg (fun j _ => hn j)
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hs j)
    rw [column_job_count] at h
    simpa only [matrix, add_sub_cancel_left, mul_assoc] using h

/-- A one-sided old cake near-EF hypothesis suffices. -/
theorem matrix_cake_near (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (hzero : ∀ j a i, 0 ≤ w j a i) (eta : ℝ) (heta : 0 ≤ eta)
    (hsmall : ∀ j a i, w j a i ≤ eta) (old : Fin k → Fin k → ℝ) (eps : ℝ)
    (hnear : ∀ i j, old i j - old i i ≤ eps)
    (pi : Equiv.Perm (Fin k)) (draw : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (i : Fin k) :
    let V := matrix (system hk (permutedWeights w pi)) old draw
    rowMaximum V i - V i i ≤ eps + k.choose 2 * L * eta := by
  dsimp only
  have h1 := matrix_increment_bound hk w hzero eta heta hsmall old pi draw i
    (rowChoice (matrix (system hk (permutedWeights w pi)) old draw) i)
  have h2 := matrix_increment_bound hk w hzero eta heta hsmall old pi draw i i
  have h3 := hnear i (rowChoice (matrix (system hk (permutedWeights w pi)) old draw) i)
  dsimp only [rowMaximum]
  linarith

/-- The opposite one-sided old near-EF hypothesis suffices for chores. -/
theorem matrix_chore_near (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (hzero : ∀ j a i, 0 ≤ w j a i) (eta : ℝ) (heta : 0 ≤ eta)
    (hsmall : ∀ j a i, w j a i ≤ eta) (old : Fin k → Fin k → ℝ) (eps : ℝ)
    (hnear : ∀ i j, old i i - old i j ≤ eps)
    (pi : Equiv.Perm (Fin k)) (draw : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (i : Fin k) :
    let V := matrix (system hk (permutedWeights w pi)) old draw
    rowMaximum (fun r c => -V r c) i + V i i ≤ eps + k.choose 2 * L * eta := by
  dsimp only
  have h1 := matrix_increment_bound hk w hzero eta heta hsmall old pi draw i
    (rowChoice (fun r c => -matrix (system hk (permutedWeights w pi)) old draw r c) i)
  have h2 := matrix_increment_bound hk w hzero eta heta hsmall old pi draw i i
  have h3 := hnear i (rowChoice (fun r c => -matrix (system hk (permutedWeights w pi)) old draw r c) i)
  dsimp only [rowMaximum]
  linarith

theorem targets_budget (V A : Fin k → Fin k → ℝ) (lam eta eps : ℝ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (hA : ∀ i j, A i j ≤ eta)
    (hcake : ∀ i, rowMaximum V i - V i i ≤ eps)
    (hchore : ∀ i, rowMaximum (fun r c => -V r c) i + V i i ≤ eps) :
    let bound := (k : ℝ) * eps + (k - 1 : ℕ) * (2 * lam * eta)
    (∀ i, 0 ≤ cakeTargets V A lam i ∧ cakeTargets V A lam i ≤ bound) ∧
    (∀ i, 0 ≤ choreTargets V A lam eta i ∧ choreTargets V A lam eta i ≤ bound) ∧
    (∑ i, cakeTargets V A lam i) ≤ k * bound ∧
    (∑ i, choreTargets V A lam eta i) ≤ k * bound := by
  dsimp only
  have hc := allowance_le V eps (2 * lam * eta) hcake
  have hh := allowance_le (fun r c => -V r c) eps (2 * lam * eta) (by simpa only [sub_neg_eq_add] using hchore)
  simp only [Fintype.card_fin] at hc hh
  refine ⟨fun i => ⟨(cakeTargets_bound V A lam eta hlam heta hA i).1,
    (cakeTargets_bound V A lam eta hlam heta hA i).2.trans hc⟩,
    fun i => ⟨(choreTargets_bound V A lam eta hlam heta hA i).1,
    (choreTargets_bound V A lam eta hlam heta hA i).2.trans hh⟩, ?_, ?_⟩
  · have hs := cakeTargets_sum_bound V A lam eta hlam heta hA
    simp only [Fintype.card_fin] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ k))
  · have hs := choreTargets_sum_bound V A lam eta hlam heta hA
    simp only [Fintype.card_fin] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ k))

end EnvyFreeResearch.Full.UpperLogicalIsolation
