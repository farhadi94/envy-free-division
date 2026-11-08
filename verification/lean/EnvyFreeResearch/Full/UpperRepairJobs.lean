import EnvyFreeResearch.Full.UpperRepairIsolation
import Mathlib.Data.Nat.Choose.Cast

/-! Concrete indexing of every unordered row pair in every column, with the
manuscript's exact number of charges and whole-trial isolation constant. -/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperRepairJobs

open UpperSeedMatrix UpperRepairIsolation UpperAssignmentIsolation UpperThresholdProduct

abbrev Job (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2} × Fin k

def jobCount (k : ℕ) : ℕ := k.choose 2 * k

theorem job_card (k : ℕ) : Fintype.card (Job k) = jobCount k := by
  simp only [Job, Fintype.card_prod, jobCount, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin k))

theorem jobCount_positive {k : ℕ} (hk : 2 ≤ k) : 0 < jobCount k :=
  Nat.mul_pos (Nat.choose_pos hk) (by omega)

def jobEquiv {k : ℕ} (hk : 2 ≤ k) : Fin (jobCount k - 1 + 1) ≃ Job k :=
  (Fintype.equivFinOfCardEq (by
    have hpos := jobCount_positive hk
    rw [job_card]
    omega)).symm

def system {k L : ℕ} (hk : 2 ≤ k) (weights : Job k → Fin L → Fin k → ℝ) :
    SeedSystem (Fin k) (jobCount k - 1) L where
  left j := (jobEquiv hk j).1.1.1
  right j := (jobEquiv hk j).1.1.2
  column j := (jobEquiv hk j).2
  weight j := weights (jobEquiv hk j)

/-- Coverage follows from the explicit unordered-pair/column enumeration. -/
theorem system_covers {k L : ℕ} (hk : 2 ≤ k) (weights : Job k → Fin L → Fin k → ℝ) :
    Covers (system hk weights) := by
  intro i h hne column
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨(jobEquiv hk).symm (⟨(i, h), hlt⟩, column), ?_⟩
    simp [system]
  · refine ⟨(jobEquiv hk).symm (⟨(h, i), hgt⟩, column), ?_⟩
    simp [system]

theorem system_difference {k L : ℕ} (hk : 2 ≤ k) (weights : Job k → Fin L → Fin k → ℝ)
    (job : Fin (jobCount k - 1 + 1)) (r : Fin L) :
    difference (system hk weights) job r =
      weights (jobEquiv hk job) r (jobEquiv hk job).1.1.1 -
        weights (jobEquiv hk job) r (jobEquiv hk job).1.1.2 := rfl

/-- The complete seed matrix satisfies the manuscript's whole-trial
isolation probability. All optimizing assignments remain inside the event. -/
theorem isolation_probability {k L : ℕ} (hk : 2 ≤ k)
    (weights : Job k → Fin L → Fin k → ℝ) (old A : Fin k → Fin k → ℝ)
    (hA : ∀ i h, 0 ≤ A i h) (hsym : ∀ i h, A i h = A h i)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : ∀ job : Job k, ∀ r,
      A job.1.1.1 job.1.1.2 / 3 ≤ |weights job r job.1.1.1 - weights job r job.1.1.2|) :
    tapeLaw (jobCount k - 1 + 1) L {draw | ∃ transfer : Equiv.Perm (Fin k),
      0 < margin (matrix (system hk weights) old draw) A lam transfer} ≤
        ENNReal.ofReal ((k : ℝ)^2 * (k - 1 : ℝ) * (12 * lam * Real.log (2 * k) + 1) /
          (L + 1 : ℕ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have ha : (0 : ℝ) < 1 / (2 * k) := by positivity
  have haone : (1 : ℝ) / (2 * k) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hcap : (1 : ℝ) - k * (1 / (2 * k)) = 1 / 2 := by field_simp; ring
  have h := positive_margin_probability (system hk weights) (system_covers hk weights)
    old A hA hsym lam (1 / (2 * k)) hlam ha haone
    (by simpa only [Fintype.card_fin, hcap] using (show (0 : ℝ) < 1 / 2 by norm_num))
    (fun job r => hgap (jobEquiv hk job) r)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hcount : jobCount k - 1 + 1 = jobCount k := by have := jobCount_positive hk; omega
  have hcountReal : (jobCount k : ℝ) = (k : ℝ) * (k - 1) / 2 * k := by
    simp [jobCount, Nat.cast_choose_two]
  simp only [Fintype.card_fin, hcount, hcap, one_div_one_div, hcountReal]
  have hden : (0 : ℝ) < (L + 1 : ℕ) := by positivity
  have hfactor : 0 ≤ (k : ℝ)^2 * (k - 1) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hkone)
  have hdrop := mul_le_mul_of_nonneg_left
    (show 12 * lam * Real.log (2 * k) + 1 - 1 / (2 * k) ≤
      12 * lam * Real.log (2 * k) + 1 by linarith [ha]) hfactor
  have hd := (div_le_div_iff_of_pos_right hden).mpr hdrop
  convert hd using 1
  ring

end EnvyFreeResearch.Full.UpperRepairJobs
