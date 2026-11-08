import EnvyFreeResearch.Full.UpperRepairParametersCounts

/-! Exact displayed scales imply the deterministic large-candidate checks
and the prescribed Snapshot margin. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperRepairParameters
variable {s ell : ℕ}

theorem coarse_cap_small (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) :
    1 / ((coarseCount s ell : ℝ) + 1) ≤ oldError s ell / 2 ∧
      1 / ((coarseCount s ell : ℝ) + 1) ≤ 1 / 4 := by
  have hs2 := s_two hs
  have hspos := s_positive hs
  have hellpos := ell_positive hell
  have h8 : (8 : ℝ) ≤ (s : ℝ)^7 * ell := by
    have hpow : (2 : ℝ)^7 ≤ (s : ℝ)^7 := pow_le_pow_left₀ (by norm_num) hs2 7
    have hmul : (s : ℝ)^7 ≤ (s : ℝ)^7 * ell := by nlinarith [pow_nonneg hspos.le 7]
    exact (show (8 : ℝ) ≤ 2^7 by norm_num).trans (hpow.trans hmul)
  have hden : 8 * (s : ℝ)^10 * ell ≤ (s : ℝ)^17 * (ell : ℝ)^2 := by
    calc
      _ ≤ ((s : ℝ)^7 * ell) * ((s : ℝ)^10 * ell) := by
        have h := mul_le_mul_of_nonneg_right h8 (by positivity : 0 ≤ (s : ℝ)^10 * ell)
        nlinarith
      _ = _ := by ring
  have hcoarse : coarseCap s ell ≤ oldError s ell / 2 := by
    change 1 / ((s : ℝ)^17 * (ell : ℝ)^2) ≤ (1 / (4 * (s : ℝ)^10 * ell)) / 2
    calc
      _ ≤ 1 / (8 * (s : ℝ)^10 * ell) := one_div_le_one_div_of_le (by positivity) hden
      _ = _ := by ring
  have htau : oldError s ell ≤ 1 / 4 := by
    have hone := denominator_ge_one hs hell 10 1
    simp only [pow_one] at hone
    change 1 / (4 * (s : ℝ)^10 * ell) ≤ 1 / 4
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hsmall := (coarse_denominator_bound hs hell).trans hcoarse
  exact ⟨hsmall, hsmall.trans (by linarith)⟩

/-- The padded logical-cell index count is at most twice the original sample
count at the actual manuscript scales. -/
theorem original_scale_cell_count {k : ℕ} (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
    (hk : (2^40 : ℝ) * k ≤ s) (hkpos : 0 < k) :
    UpperRecordedQuantiles.count (Agent := Fin k) (coarseCount s ell) + samples s ell + 1 ≤ 2 * samples s ell := by
  have h := (grid_fits hs hell hk hkpos).1
  simp only [UpperRecordedQuantiles.count, Fintype.card_prod, Fintype.card_fin]
  omega

/-- The concrete signed-cell contrast supplies Lambda=D/(3M); after the
contrast lemma the original prescribed theta=tau/(768m) is attained. -/
theorem large_margin_scale (D tau M samples : ℝ) (hD : tau / 16 ≤ D) (htau : 0 ≤ tau)
    (hM : 0 < M) (hsamples : 0 < samples) (hcount : M ≤ 2 * samples) :
    tau / (768 * samples) ≤ (D / (3 * M)) / 8 := by
  have hDnonnegative : 0 ≤ D := (div_nonneg htau (by norm_num)).trans hD
  calc
    _ = (tau / 16) / (24 * (2 * samples)) := by ring
    _ ≤ D / (24 * (2 * samples)) := div_le_div_of_nonneg_right hD (by positivity)
    _ ≤ D / (24 * M) := div_le_div_of_nonneg_left hDnonnegative (by positivity) (by nlinarith)
    _ = _ := by ring

end EnvyFreeResearch.Full.UpperSnapshotCandidates
