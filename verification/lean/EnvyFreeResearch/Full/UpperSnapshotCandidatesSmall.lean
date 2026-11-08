import EnvyFreeResearch.Full.UpperSnapshotCandidatesSelect

/-! Finite zero/small-disagreement scalar estimates. These do not identify
cell agreement with agreement inside cells, or assume a physical candidate. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
variable {Cell : Type*} [Fintype Cell]

theorem positive_mass (score : Cell → ℝ) (hsum : ∑ c, score c = 0) :
    ∑ c, max (score c) 0 = (∑ c, |score c|) / 2 := by
  have habs (c : Cell) : |score c| = 2 * max (score c) 0 - score c := by
    by_cases hc : 0 ≤ score c
    · rw [abs_of_nonneg hc, max_eq_left hc]
      ring
    · rw [abs_of_nonpos (le_of_not_ge hc), max_eq_right (le_of_not_ge hc)]
      ring
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset Cell)) rfl (fun c _ => habs c)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, sub_zero] at h
  linarith

theorem weighted_sum_le_positive (score rho : Cell → ℝ) (hrho : ∀ c, 0 ≤ rho c ∧ rho c ≤ 1) :
    (∑ c, score c * rho c) ≤ ∑ c, max (score c) 0 := by
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : 0 ≤ score c
  · rw [max_eq_left hc]
    nlinarith [(hrho c).2]
  · rw [max_eq_right (le_of_not_ge hc)]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (hrho c).1

/-- Every convex within-cell interpolation assigns any set at most half
the zero-total row's absolute cell discrepancy. -/
theorem convex_signed_bound (score rho : Cell → ℝ) (hsum : ∑ c, score c = 0)
    (hrho : ∀ c, 0 ≤ rho c ∧ rho c ≤ 1) :
    |∑ c, score c * rho c| ≤ (∑ c, |score c|) / 2 := by
  have hp := weighted_sum_le_positive score rho hrho
  rw [positive_mass score hsum] at hp
  have hn := weighted_sum_le_positive (fun c => -score c) rho hrho
  rw [positive_mass (fun c => -score c) (by simp only [Finset.sum_neg_distrib, hsum, neg_zero])] at hn
  simp only [neg_mul, Finset.sum_neg_distrib, abs_neg] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

theorem zero_signed_cells (score : Cell → ℝ) (hzero : ∑ c, |score c| = 0) (c : Cell) : score c = 0 := by
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun c (_ : c ∈ (Finset.univ : Finset Cell)) => abs_nonneg (score c))).mp hzero
  exact abs_eq_zero.mp (h c (Finset.mem_univ c))

theorem zero_table {k m : ℕ} (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hzero : selectedDistance hk values cutter = 0) (i : Fin k) (e : Fin (m + 1)) :
    values i e = values cutter e := by
  have hr : rowDistance values cutter i = 0 :=
    le_antisymm (by simpa only [hzero] using selectedRow_spec hk values cutter i)
      (rowDistance_nonnegative values cutter i)
  exact sub_eq_zero.mp (zero_signed_cells (fun c => values i c - values cutter c) hr e)

/-- The two first-piece expectation formulas used by the small branch. -/
def firstMean (D t u : ℝ) : ℝ :=
  if t ≤ u then t * D / (2 * u) else D * (1 - t) / (2 * (1 - u))

theorem firstMean_lower (D t u : ℝ) (hD : 0 ≤ D) (ht : 0 < t) (hhalf : t ≤ 1 / 2)
    (hu : 0 ≤ u) (huone : u ≤ 1) : t * D / 2 ≤ firstMean D t u := by
  unfold firstMean
  split_ifs with htu
  · have hup : 0 < u := ht.trans_le htu
    apply (le_div_iff₀ (by positivity : 0 < 2 * u)).mpr
    nlinarith [mul_nonneg (mul_nonneg ht.le hD) (sub_nonneg.mpr huone)]
  · have hun : 0 < 1 - u := by linarith
    apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - u))).mpr
    nlinarith [mul_nonneg hD (show 0 ≤ 1 - 2 * t by linarith), mul_nonneg hD (mul_nonneg ht.le hu)]

/-- The second independent circular group contributes the stated complement
mean, so the resulting contrast mean has the required scalar lower bound. -/
theorem contrastMean_lower (D t u agents : ℝ) (hD : 0 ≤ D) (ht : 0 < t) (hhalf : t ≤ 1 / 2)
    (hu : 0 ≤ u) (huone : u ≤ 1) (hk : 0 < agents) (htlower : 1 / (2 * agents) ≤ t) :
    D / (4 * agents) ≤ firstMean D t u - (-(t / (1 - t)) * firstMean D t u) := by
  have hf := firstMean_lower D t u hD ht hhalf hu huone
  have htD : D / (4 * agents) ≤ t * D / 2 := by
    have h := mul_le_mul_of_nonneg_right htlower hD
    field_simp at h ⊢
    nlinarith
  have hmean : 0 ≤ firstMean D t u := (div_nonneg (mul_nonneg ht.le hD) (by norm_num)).trans hf
  have hcoefficient : 0 ≤ t / (1 - t) := div_nonneg ht.le (by linarith)
  have hgain := mul_nonneg hcoefficient hmean
  linarith

end EnvyFreeResearch.Full.UpperSnapshotCandidates
