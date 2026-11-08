import EnvyFreeResearch.Full.NonnegativeCircle

namespace EnvyFreeResearch.Full.NonnegativeGeometry

open MeasureTheory Set Metric
open scoped ENNReal symmDiff
abbrev Circle := NonnegativeCircle.Circle

/-- The quotient image of an ordinary closed interval. Endpoint conventions
are null for all center laws used in the lower bound. -/
def arc (a b : ℝ) : Set Circle := ((↑) : ℝ → Circle) '' Icc a b

theorem measurable_arc (a b : ℝ) : MeasurableSet (arc a b) :=
  (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed.measurableSet

/-- Quotienting cannot increase the mass of a real interval. This proof uses
its midpoint and the exact Haar mass of a circular ball. -/
theorem arc_mass_le (a b : ℝ) : volume (arc a b) ≤ ENNReal.ofReal (b - a) := by
  by_cases hab : a ≤ b
  · have hsubset : arc a b ⊆ closedBall ((↑((a + b) / 2)) : Circle) ((b - a) / 2) := by
      rintro x ⟨t, ht, rfl⟩
      rw [mem_closedBall, dist_eq_norm, ← AddCircle.coe_sub]
      apply (QuotientAddGroup.norm_mk_le_norm).trans
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    calc
      volume (arc a b) ≤ volume (closedBall ((↑((a + b) / 2)) : Circle) ((b - a) / 2)) :=
        measure_mono hsubset
      _ = ENNReal.ofReal (min 1 (b - a)) := by rw [AddCircle.volume_closedBall]; congr 2 <;> ring
      _ ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
  · simp [arc, Icc_eq_empty_of_lt (lt_of_not_ge hab), ENNReal.ofReal_eq_zero.mpr (show b - a ≤ 0 by linarith)]

theorem image_symmDiff_subset {α β : Type*} (f : α → β) (A B : Set α) :
    (f '' A) ∆ (f '' B) ⊆ f '' (A ∆ B) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨a, ha, rfl⟩ := hx.1
    exact ⟨a, Or.inl ⟨ha, fun hb => hx.2 ⟨a, hb, rfl⟩⟩, rfl⟩
  · obtain ⟨b, hb, rfl⟩ := hx.1
    exact ⟨b, Or.inr ⟨hb, fun ha => hx.2 ⟨b, ha, rfl⟩⟩, rfl⟩

theorem real_interval_shift_cover (a b u : ℝ) (hu : 0 ≤ u) :
    (Icc a b) ∆ (Icc (a - u) (b - u)) ⊆ Icc (a - u) a ∪ Icc (b - u) b := by
  intro x hx
  rcases hx with hx | hx
  · right
    have hnot : ¬ (a - u ≤ x ∧ x ≤ b - u) := hx.2
    have hleft : a - u ≤ x := by linarith [hx.1.1]
    exact ⟨by by_contra h; exact hnot ⟨hleft, le_of_lt (lt_of_not_ge h)⟩, hx.1.2⟩
  · left
    have hnot : ¬ (a ≤ x ∧ x ≤ b) := hx.2
    have hright : x ≤ b := by linarith [hx.1.2]
    exact ⟨hx.1.1, by by_contra h; exact hnot ⟨le_of_lt (lt_of_not_ge h), hright⟩⟩

theorem arc_shift_mass_le_nonneg (a b u : ℝ) (hu : 0 ≤ u) :
    volume ((arc a b) ∆ (arc (a - u) (b - u))) ≤ ENNReal.ofReal (2 * u) := by
  have hsubset : (arc a b) ∆ (arc (a - u) (b - u)) ⊆
      arc (a - u) a ∪ arc (b - u) b := by
    apply (image_symmDiff_subset ((↑) : ℝ → Circle) (Icc a b) (Icc (a - u) (b - u))).trans
    exact (Set.image_mono (real_interval_shift_cover a b u hu)).trans_eq (image_union ..)
  calc
    volume ((arc a b) ∆ (arc (a - u) (b - u))) ≤
        volume (arc (a - u) a ∪ arc (b - u) b) := measure_mono hsubset
    _ ≤ volume (arc (a - u) a) + volume (arc (b - u) b) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (a - (a - u)) + ENNReal.ofReal (b - (b - u)) :=
      add_le_add (arc_mass_le _ _) (arc_mass_le _ _)
    _ = ENNReal.ofReal (2 * u) := by
      rw [sub_sub_cancel, sub_sub_cancel, ← ENNReal.ofReal_add hu hu]
      congr 1
      ring

theorem arc_shift_mass_le (a b u : ℝ) :
    volume ((arc a b) ∆ (arc (a - u) (b - u))) ≤ ENNReal.ofReal (2 * |u|) := by
  by_cases hu : 0 ≤ u
  · simpa only [abs_of_nonneg hu] using arc_shift_mass_le_nonneg a b u hu
  · have hneg : 0 ≤ -u := by linarith
    have h := arc_shift_mass_le_nonneg (a - u) (b - u) (-u) hneg
    have ha : a - u - -u = a := by ring
    have hb : b - u - -u = b := by ring
    simpa only [ha, hb, abs_of_neg (lt_of_not_ge hu), symmDiff_comm] using h

theorem translate_preimage_arc (a b u : ℝ) :
    (fun x : Circle => x + (u : Circle)) ⁻¹' arc a b = arc (a - u) (b - u) := by
  ext x
  constructor
  · rintro ⟨t, ht, heq⟩
    refine ⟨t - u, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [AddCircle.coe_sub, heq]
    simp
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t + u, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [AddCircle.coe_add]

/-- The sharp fixed-shift interval-separation bound. It applies to every
ordinary query interval, including intervals that wrap after translation. -/
theorem fixed_shift_separation_le (a b u : ℝ) :
    volume {x : Circle | (x ∈ arc a b) ≠ (x + (u : Circle) ∈ arc a b)} ≤
      ENNReal.ofReal (2 * |u|) := by
  have heq : {x : Circle | (x ∈ arc a b) ≠ (x + (u : Circle) ∈ arc a b)} =
      (arc a b) ∆ ((fun x : Circle => x + (u : Circle)) ⁻¹' arc a b) := by
    ext x
    simp only [mem_ofPred_eq, mem_symmDiff, mem_preimage]
    tauto
  rw [heq, translate_preimage_arc]
  exact arc_shift_mass_le a b u

end EnvyFreeResearch.Full.NonnegativeGeometry

#print axioms EnvyFreeResearch.Full.NonnegativeGeometry.arc_mass_le
#print axioms EnvyFreeResearch.Full.NonnegativeGeometry.fixed_shift_separation_le
