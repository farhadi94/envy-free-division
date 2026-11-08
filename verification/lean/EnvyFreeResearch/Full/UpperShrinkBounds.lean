import EnvyFreeResearch.Full.UpperRepair

/-! Raw-unit bounds for the deterministic carving used by prescribed Shrink.
These lemmas do not assert that the still-unfinished carving executor exists.
They retain a separate domain mass for each observer. -/

noncomputable section
open scoped BigOperators

namespace EnvyFreeResearch.Full.UpperShrink

def fraction (k : ℕ) (G : ℝ) : ℝ := (1 - 1 / (2 * G)) / k
def error (tau G : ℝ) : ℝ := tau / (4 * G)

theorem carving_buffer_bounds {k : ℕ} (hk : 0 < k)
    {G tau M B : ℝ} (hG : 0 < G) (htau : 0 ≤ tau) (hM : 0 ≤ M)
    (hktau : (k : ℝ) * tau ≤ 2) (w : Fin k → ℝ)
    (hlower : ∀ j, (fraction k G - error tau G) * M ≤ w j)
    (hupper : ∀ j, w j ≤ fraction k G * M)
    (hpartition : B + ∑ j, w j = M) :
    M / (2 * G) ≤ B ∧ B ≤ M / G := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsumL := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hlower j)
  have hsumU := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hupper j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumL hsumU
  have hf : (k : ℝ) * fraction k G = 1 - 1 / (2 * G) := by
    unfold fraction
    field_simp
  have he : (k : ℝ) * error tau G ≤ 1 / (2 * G) := by
    unfold error
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 4 * G)).mpr
    have hid : 1 / (2 * G) * (4 * G) = (2 : ℝ) := by field_simp <;> ring
    rw [hid]
    exact hktau
  have hm : (k : ℝ) * error tau G * M ≤ (1 / (2 * G)) * M :=
    mul_le_mul_of_nonneg_right he hM
  constructor
  · have hU : (∑ j, w j) ≤ (1 - 1 / (2 * G)) * M := by
      nlinarith [hsumU]
    simp only [div_eq_mul_inv] at *
    nlinarith
  · have hidentity : M / G = 2 * ((1 / (2 * G)) * M) := by field_simp <;> ring
    rw [hidentity]
    nlinarith [hsumL]

theorem carving_positive {M B G : ℝ} (hM : 0 < M) (hG : 0 < G)
    (hlower : M / (2 * G) ≤ B) : 0 < B :=
  (div_pos hM (by positivity)).trans_le hlower

theorem carving_range {G tau M B x y f : ℝ}
    (hG : 0 < G) (htau : 0 ≤ tau) (hM : 0 ≤ M)
    (hB : M / (2 * G) ≤ B)
    (hx : x ≤ f * M) (hy : (f - error tau G) * M ≤ y) :
    x - y ≤ tau * B := by
  have hb := mul_le_mul_of_nonneg_left hB htau
  have hid : error tau G * M = tau / 2 * (M / (2 * G)) := by
    unfold error
    field_simp
    ring
  have hnonneg : 0 ≤ tau * B :=
    mul_nonneg htau ((div_nonneg hM (by positivity)).trans hB)
  nlinarith

theorem repaired_residue_bounds {M B R G : ℝ} (hG : 0 < G)
    (hB : M / (2 * G) ≤ B ∧ B ≤ M / G)
    (hR : (3 / 4 : ℝ) * B < R ∧ R ≤ B) :
    3 * M / (8 * G) ≤ R ∧ R ≤ M / G := by
  constructor
  · have hid : 3 * M / (8 * G) = (3 / 4 : ℝ) * (M / (2 * G)) := by
      field_simp
      ring
    rw [hid]
    linarith [hB.1, hR.1]
  · exact hR.2.trans hB.2

end EnvyFreeResearch.Full.UpperShrink
