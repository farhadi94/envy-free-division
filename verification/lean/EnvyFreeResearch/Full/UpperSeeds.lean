import EnvyFreeResearch.Full.UpperRepresentativeSupply

/-!
# Physical seed thresholds

The threshold rule keeps positive witnesses before the threshold and negative
witnesses after it. Its physical signed value is an increasing finite sequence
with exactly the absolute witness values as successive increments.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperSeeds

open UpperRecordedDomain

variable {L : ℕ}

def kept (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) (a : Fin L) : Prop :=
  if a.val < threshold.val then 0 < gamma a else gamma a < 0

def value (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) : ℝ :=
  ∑ a, if kept gamma threshold a then gamma a else 0

def base (gamma : Fin L → ℝ) : ℝ := ∑ a, min (gamma a) 0

theorem kept_identity (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) (a : Fin L) :
    (if kept gamma threshold a then gamma a else 0) =
      min (gamma a) 0 + if a.val < threshold.val then |gamma a| else 0 := by
  unfold kept
  by_cases hbefore : a.val < threshold.val
  · by_cases hneg : gamma a < 0
    · simp [hbefore, not_lt_of_gt hneg, min_eq_left hneg.le, abs_of_neg hneg]
    · have hnonneg := le_of_not_gt hneg
      by_cases hzero : gamma a = 0
      · simp [hbefore, hzero]
      · have hpos : 0 < gamma a := lt_of_le_of_ne hnonneg (Ne.symm hzero)
        simp [hbefore, hpos, min_eq_right hnonneg, abs_of_nonneg hnonneg]
  · by_cases hneg : gamma a < 0
    · simp [hbefore, hneg, min_eq_left hneg.le]
    · simp [hbefore, hneg, min_eq_right (le_of_not_gt hneg)]

theorem value_formula (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) :
    value gamma threshold = base gamma + ∑ a, if a.val < threshold.val then |gamma a| else 0 := by
  simp only [value, kept_identity, Finset.sum_add_distrib, base]

theorem value_increment (gamma : Fin L → ℝ) (a : Fin L) :
    value gamma a.succ - value gamma a.castSucc = |gamma a| := by
  have hterm (b : Fin L) :
      (if b.val < a.val + 1 then |gamma b| else 0) =
        (if b.val < a.val then |gamma b| else 0) + if b = a then |gamma b| else 0 := by
    by_cases heq : b = a
    · subst b
      simp
    · have hne : b.val ≠ a.val := fun h => heq (Fin.ext h)
      by_cases hlt : b.val < a.val
      · simp [heq, hlt, show b.val < a.val + 1 by omega]
      · simp [heq, hlt, show ¬ b.val < a.val + 1 by omega]
  rw [value_formula, value_formula]
  simp only [Fin.val_succ, Fin.val_castSucc, hterm, Finset.sum_add_distrib]
  simp

/-- The exact threshold sequence has the quantitative spacing used by the
assignment-isolation argument. -/
theorem value_spacing (gamma : Fin L → ℝ) (gap : ℝ)
    (hgap : ∀ a, gap ≤ |gamma a|) (s t : Fin (L + 1)) (hst : s ≤ t) :
    gap * ((t.val : ℝ) - (s.val : ℝ)) ≤ value gamma t - value gamma s := by
  have hmono : Monotone (fun threshold : Fin (L + 1) =>
      value gamma threshold - gap * threshold.val) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro a
    have hstep := value_increment gamma a
    have hbound := hgap a
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    nlinarith
  have h := hmono hst
  linarith

theorem value_strictMono (gamma : Fin L → ℝ) (gap : ℝ) (hpositive : 0 < gap)
    (hgap : ∀ a, gap ≤ |gamma a|) : StrictMono (value gamma) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro a
  have hstep := value_increment gamma a
  have := hgap a
  linarith

def physicalSeed (cells : Fin L → Component) (gamma : Fin L → ℝ)
    (threshold : Fin (L + 1)) : Set ℝ :=
  ⋃ a, if kept gamma threshold a then (cells a).carrier else ∅

theorem physicalSeed_subset (cells : Fin L → Component) (gamma : Fin L → ℝ)
    (threshold : Fin (L + 1)) : physicalSeed cells gamma threshold ⊆ ⋃ a, (cells a).carrier := by
  intro x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨a, ?_⟩
  by_cases h : kept gamma threshold a
  · simpa only [h, ite_true] using ha
  · simp only [h, ite_false, mem_empty_iff_false] at ha

theorem physicalSeed_measurable (cells : Fin L → Component) (gamma : Fin L → ℝ)
    (threshold : Fin (L + 1)) : MeasurableSet (physicalSeed cells gamma threshold) := by
  apply MeasurableSet.iUnion
  intro a
  by_cases h : kept gamma threshold a
  · simpa only [h, ite_true] using (cells a).measurable_carrier
  · simp only [h, ite_false]
    exact MeasurableSet.empty

theorem physicalSeed_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (cells : Fin L → Component) (gamma : Fin L → ℝ) (threshold : Fin (L + 1))
    (hdisjoint : Pairwise (fun a b => Disjoint (cells a).carrier (cells b).carrier)) :
    μ.real (physicalSeed cells gamma threshold) =
      ∑ a, if kept gamma threshold a then μ.real (cells a).carrier else 0 := by
  unfold physicalSeed
  rw [measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · intro a b hab
    dsimp only [Function.onFun]
    split_ifs <;> simp [hdisjoint hab]
  · intro a
    split_ifs
    · exact (cells a).measurable_carrier
    · exact MeasurableSet.empty

/-- The literal union has exactly the seed score used in isolation, for the
actual two normalized observer measures. No physical realization is assumed. -/
theorem physicalSeed_signed_value (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (cells : Fin L → Component) (u v : ℝ) (threshold : Fin (L + 1))
    (hdisjoint : Pairwise (fun a b => Disjoint (cells a).carrier (cells b).carrier)) :
    let gamma := fun a => u * μ.real (cells a).carrier - v * ν.real (cells a).carrier
    u * μ.real (physicalSeed cells gamma threshold) -
      v * ν.real (physicalSeed cells gamma threshold) = value gamma threshold := by
  dsimp only
  rw [physicalSeed_mass μ _ _ _ hdisjoint, physicalSeed_mass ν _ _ _ hdisjoint]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, value]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

end EnvyFreeResearch.Full.UpperSeeds
