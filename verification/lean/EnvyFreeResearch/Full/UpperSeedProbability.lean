import EnvyFreeResearch.Full.UpperSeeds

/-! Anti-concentration of the actual finite seed threshold. The fixed offset
may contain every other column contribution; no maximizing-assignment event
is conditioned on in these estimates. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperSeedProbability

open UpperSeeds

variable {L : ℕ}

def thresholdLaw : Measure (Fin (L + 1)) := uniformOn Set.univ

instance thresholdLaw_probability : IsProbabilityMeasure (thresholdLaw (L := L)) := by
  unfold thresholdLaw
  infer_instance

def intervalHits (gamma : Fin L → ℝ) (a b : ℝ) : Finset (Fin (L + 1)) :=
  Finset.univ.filter (fun t => value gamma t ∈ Icc a b)

/-- A spaced seed sequence has at most `width/gap + 1` values in any closed
interval, including both endpoint values of the threshold. -/
theorem interval_card_bound (gamma : Fin L → ℝ) (gap : ℝ) (hpositive : 0 < gap)
    (hgap : ∀ a, gap ≤ |gamma a|) (a b : ℝ) (hab : a ≤ b) :
    ((intervalHits gamma a b).card : ℝ) ≤ (b - a) / gap + 1 := by
  classical
  let hits := intervalHits gamma a b
  by_cases hnonempty : hits.Nonempty
  · let lo := hits.min' hnonempty
    let hi := hits.max' hnonempty
    have hlo : lo ∈ hits := Finset.min'_mem hits hnonempty
    have hhi : hi ∈ hits := Finset.max'_mem hits hnonempty
    have hlohi : lo ≤ hi := Finset.min'_le_max' hits hnonempty
    have hbetween : hits ⊆ Finset.Icc lo hi := by
      intro t ht
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le hits t ht, Finset.le_max' hits t ht⟩
    have hcard := Finset.card_le_card hbetween
    rw [Fin.card_Icc] at hcard
    have hcardReal : (hits.card : ℝ) ≤ (hi.val : ℝ) + 1 - (lo.val : ℝ) := by
      have hnat : lo.val ≤ hi.val + 1 := by exact Nat.le_succ_of_le hlohi
      have hh : (hits.card : ℝ) ≤ ((hi.val + 1 - lo.val : ℕ) : ℝ) := by exact_mod_cast hcard
      simpa only [Nat.cast_sub hnat, Nat.cast_add, Nat.cast_one] using hh
    have hvlo : a ≤ value gamma lo := (Finset.mem_filter.mp hlo).2.1
    have hvhi : value gamma hi ≤ b := (Finset.mem_filter.mp hhi).2.2
    have hspacing := value_spacing gamma gap hgap lo hi hlohi
    have hdelta : (hi.val : ℝ) - (lo.val : ℝ) ≤ (b - a) / gap := by
      apply (le_div_iff₀ hpositive).mpr
      nlinarith
    change (hits.card : ℝ) ≤ _
    linarith
  · have hempty : hits = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hwidth : 0 ≤ (b - a) / gap := div_nonneg (sub_nonneg.mpr hab) hpositive.le
    change (hits.card : ℝ) ≤ _
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    linarith

theorem interval_probability (gamma : Fin L → ℝ) (gap : ℝ) (hpositive : 0 < gap)
    (hgap : ∀ a, gap ≤ |gamma a|) (a b : ℝ) (hab : a ≤ b) :
    thresholdLaw {t | value gamma t ∈ Icc a b} ≤
      ENNReal.ofReal (((b - a) / gap + 1) / (L + 1 : ℕ)) := by
  have heq : {t | value gamma t ∈ Icc a b} = (intervalHits gamma a b : Set (Fin (L + 1))) := by
    ext t
    simp [intervalHits]
  rw [heq, thresholdLaw, uniformOn_univ, Measure.count_apply_finset, Fintype.card_fin]
  have hden : (0 : ℝ) < (L + 1 : ℕ) := by positivity
  rw [ENNReal.ofReal_div_of_pos hden]
  have hbound := ENNReal.ofReal_le_ofReal (interval_card_bound gamma gap hpositive hgap a b hab)
  simpa only [ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul] using
    (mul_le_mul_of_nonneg_left hbound
      (show 0 ≤ (ENNReal.ofReal (L + 1 : ℕ))⁻¹ from bot_le))

/-- Uniform thresholds prevent any fixed offset from placing too many seed
scores inside a short symmetric window. -/
theorem absolute_window_probability (gamma : Fin L → ℝ) (gap : ℝ) (hpositive : 0 < gap)
    (hgap : ∀ a, gap ≤ |gamma a|) (offset radius : ℝ) (hradius : 0 ≤ radius) :
    thresholdLaw {t | |offset + value gamma t| ≤ radius} ≤
      ENNReal.ofReal ((2 * radius / gap + 1) / (L + 1 : ℕ)) := by
  have heq : {t | |offset + value gamma t| ≤ radius} =
      {t | value gamma t ∈ Icc (-offset - radius) (-offset + radius)} := by
    ext t
    simp only [mem_ofPred_eq, abs_le, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [heq]
  convert interval_probability gamma gap hpositive hgap (-offset - radius) (-offset + radius)
    (by linarith) using 1
  congr 1
  ring

/-- The conditional one-threshold estimate used in Repair isolation, after
substitution of the proved `A/3` witness separation. -/
theorem isolation_window_probability (gamma : Fin L → ℝ) (A lam u offset : ℝ)
    (hA : 0 < A) (hlam : 0 ≤ lam) (hu : 0 < u)
    (hgap : ∀ a, A / 3 ≤ |gamma a|) :
    thresholdLaw {t | |offset + value gamma t| ≤ 2 * lam * A / u} ≤
      ENNReal.ofReal ((12 * lam / u + 1) / (L + 1 : ℕ)) := by
  have h := absolute_window_probability gamma (A / 3) (by positivity) hgap
    offset (2 * lam * A / u) (by positivity)
  convert h using 1
  congr 1
  field_simp
  ring

/-- The zero-gap convention from the manuscript is part of this actual score. -/
def charge (A lam score : ℝ) : ℝ :=
  if A = 0 then 0 else if score = 0 then 1 else min 1 (2 * lam * A / |score|)

theorem charge_nonneg (A lam score : ℝ) (hA : 0 ≤ A) (hlam : 0 ≤ lam) :
    0 ≤ charge A lam score := by
  unfold charge
  split_ifs
  · exact le_rfl
  · norm_num
  · exact le_min zero_le_one (div_nonneg (by positivity) (abs_nonneg _))

theorem charge_le_one (A lam score : ℝ) : charge A lam score ≤ 1 := by
  unfold charge
  split_ifs
  · norm_num
  · exact le_rfl
  · exact min_le_left _ _

theorem charge_ge_iff (A lam score u : ℝ) (hA : 0 < A) (hlam : 0 ≤ lam)
    (hu : 0 < u) (huone : u ≤ 1) :
    u ≤ charge A lam score ↔ |score| ≤ 2 * lam * A / u := by
  by_cases hzero : score = 0
  · simp [charge, hA.ne', hzero, huone, div_nonneg (by positivity : 0 ≤ 2 * lam * A) hu.le]
  · have habs : 0 < |score| := abs_pos.mpr hzero
    simp only [charge, hA.ne', ite_false, hzero, le_min_iff]
    rw [le_div_iff₀ habs, le_div_iff₀ hu]
    constructor
    · intro h
      simpa only [mul_comm] using h.2
    · intro h
      exact ⟨huone, by simpa only [mul_comm] using h⟩

/-- The actual reciprocal-gap charge has the conditional tail bound used in
the logarithmic isolation estimate. -/
theorem charge_tail_probability (gamma : Fin L → ℝ) (A lam u offset : ℝ)
    (hA : 0 < A) (hlam : 0 ≤ lam) (hu : 0 < u) (huone : u ≤ 1)
    (hgap : ∀ a, A / 3 ≤ |gamma a|) :
    thresholdLaw {t | u ≤ charge A lam (offset + value gamma t)} ≤
      ENNReal.ofReal ((12 * lam / u + 1) / (L + 1 : ℕ)) := by
  simp_rw [charge_ge_iff A lam _ u hA hlam hu huone]
  exact isolation_window_probability gamma A lam u offset hA hlam hu hgap

end EnvyFreeResearch.Full.UpperSeedProbability
