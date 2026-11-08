import EnvyFreeResearch.Full.UpperShrinkPrecision

noncomputable section
namespace EnvyFreeResearch.Full.UpperShrinkPrecision
open UpperRepairParameters

theorem scale_le_binary_logarithm {s : ℕ} (hs : (2^42 : ℝ) ≤ s) :
    (s : ℝ) ≤ (2 : ℝ)^(logarithm s) := by
  apply (Real.log_le_log_iff (s_positive hs) (by positivity)).mp
  rw [Real.log_pow]
  have hc : Real.log (2 * (s : ℝ)) / Real.log 2 ≤ logarithm s := Nat.le_ceil _
  have hb := (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hc
  exact (Real.log_le_log (s_positive hs) (by linarith [s_positive hs])).trans hb

theorem cell_precision_scale {s ell k : ℕ} (hs : (2^42 : ℝ) ≤ s)
    (hell : (1 : ℝ) ≤ ell) (hells : ell ≤ s) (hks : k ≤ s) :
    4 * (k : ℝ)^2 / oldError s ell ≤ (s : ℝ)^14 := by
  have hsp := s_positive hs
  have hep := ell_positive hell
  have hk : (k : ℝ) ≤ s := by exact_mod_cast hks
  have he : (ell : ℝ) ≤ s := by exact_mod_cast hells
  have h16 : (16 : ℝ) ≤ s := by norm_num at hs ⊢; linarith
  have hid : 4 * (k : ℝ)^2 / oldError s ell = 16 * (k : ℝ)^2 * (s : ℝ)^10 * ell := by
    unfold oldError
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ (s : ℝ) * (s : ℝ)^2 * (s : ℝ)^10 * s := by gcongr
    _ = _ := by ring

theorem geometric_precision {s ell k : ℕ} (hs : (2^42 : ℝ) ≤ s)
    (hell : (1 : ℝ) ≤ ell) (hells : ell ≤ s) (hks : k ≤ s) (hk : 3 ≤ k)
    (hbinary : (s : ℝ) ≤ (2 : ℝ)^ell) (G : ℝ)
    (hG : 0 < G)
    (hmax : G ≤ (2 / (oldError s ell / (768 * samples s ell))) *
      (8 / oldError s ell)^(k-1)) :
    (k : ℝ)^2 / (2 : ℝ)^(32*k*ell) ≤ oldError s ell / (4*G) := by
  have ht := oldError_positive hs hell
  have hb := reciprocal_scales hs hell hells
  have hc := cell_precision_scale hs hell hells hks
  have hm : (4 * (k : ℝ)^2 / oldError s ell) * G ≤ (s : ℝ)^(12*k+34) := by
    calc
      _ ≤ (s : ℝ)^14 * ((s : ℝ)^32 * ((s : ℝ)^12)^(k-1)) := by
        apply mul_le_mul hc ?_ hG.le (by positivity)
        exact hmax.trans (mul_le_mul hb.2 (pow_le_pow_left₀ (by positivity) hb.1 _)
          (by positivity) (by positivity))
      _ = _ := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
  have hp : (s : ℝ)^(12*k+34) ≤ (2 : ℝ)^(32*k*ell) := by
    calc
      _ ≤ ((2 : ℝ)^ell)^(12*k+34) := pow_le_pow_left₀ (by positivity) hbinary _
      _ ≤ ((2 : ℝ)^ell)^(32*k) := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hprod := hm.trans hp
  rw [div_mul_eq_mul_div] at hprod
  have hclear := (div_le_iff₀ ht).mp hprod
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2^(32*k*ell)) (by positivity : 0 < 4*G)).mpr
  nlinarith only [hclear]

end EnvyFreeResearch.Full.UpperShrinkPrecision
