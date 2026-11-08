import EnvyFreeResearch.Full.NonnegativeProfile
import EnvyFreeResearch.Full.NonnegativeRandomOutput
import EnvyFreeResearch.Full.NonnegativeAllocationDecoder

namespace EnvyFreeResearch.Full.NonnegativeFailure

open Set MeasureTheory IntervalAllocation MixedDensity NonnegativeProfile
open NonnegativeAllocation NonnegativePulse NonnegativePulseGeometry NonnegativeRandomOutput
open scoped Classical

variable {Agent : Type*}
abbrev Circle := NonnegativeCircle.Circle

def CakeEF (rows : Agent → Row) (A : Allocation Agent) : Prop :=
  ∀ i j, (rows i).signedMeasure (A.share j) ≤ (rows i).signedMeasure (A.share i)

def ChoreEF (rows : Agent → Row) (A : Allocation Agent) : Prop :=
  ∀ i j, (rows i).signedMeasure (A.share i) ≤ (rows i).signedMeasure (A.share j)

theorem uniform_share_value (A : Allocation Agent) (i : Agent) :
    uniformRow.signedMeasure (A.share i) = volume.real (A.share i) := by
  rw [Row.signedMeasure_apply _ _ (A.share_measurable i)]
  change (∫ t in A.share i, (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t) = _
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  apply measureReal_congr
  filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with t ht
  apply propext
  constructor
  · exact fun hm => hm.1
  · intro hm
    have hb := share_subset A i hm
    exact ⟨hm, ⟨lt_of_le_of_ne hb.1 (Ne.symm ht), hb.2⟩⟩

theorem uniform_cake_iff (A : Allocation Agent) :
    CakeEF (fun _ => uniformRow) A ↔ UniformEF A := by
  simp only [CakeEF, UniformEF, uniform_share_value]

theorem uniform_chore_iff (A : Allocation Agent) :
    ChoreEF (fun _ => uniformRow) A ↔ UniformEF A := by
  simp only [ChoreEF, UniformEF, uniform_share_value]
  constructor <;> intro h i j <;> exact h j i

theorem exists_gap_pair [Fintype Agent] [Nonempty Agent]
    (A : Allocation Agent) (h : ℝ) (hgap : h < uniformGap A) :
    ∃ i j, volume.real (A.share i) + h < volume.real (A.share j) := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun k => volume.real (A.share k))
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun k => volume.real (A.share k))
  refine ⟨i, j, ?_⟩
  unfold uniformGap at hgap
  rw [← hi, ← hj] at hgap
  linarith

/-- An actually incorrect complete uniform cake output remains incorrect
under every one-row pulse perturbation once its measurable strict gap exceeds
the width. This covers all old wrong outputs, not only successful decoders. -/
theorem old_cake_failure_preserved [Fintype Agent] [Nonempty Agent]
    (A : Allocation Agent) (observer : Agent) (h c d : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (hgap : h < uniformGap A) :
    ¬ CakeEF (perturbedRows observer h (c : Circle) (d : Circle)) A := by
  obtain ⟨i, j, hij⟩ := exists_gap_pair A h hgap
  intro hef
  have hcompare := hef i j
  by_cases hi : i = observer
  · simp only [perturbedRows, ite_eq_left hi] at hcompare
    exact (not_lt_of_ge hcompare) (old_strict_gap_preserved h c d hh hc0 hc1 hd0 hd1
      (A.share i) (A.share j) (A.share_measurable i) (A.share_measurable j)
      (share_subset A i) (share_subset A j) hij)
  · simp only [perturbedRows, ite_eq_right hi, uniform_share_value] at hcompare
    linarith

/-- The identical positive gap also preserves every old chore failure. The
observer witnessing the inequality is the owner of the larger bundle. -/
theorem old_chore_failure_preserved [Fintype Agent] [Nonempty Agent]
    (A : Allocation Agent) (observer : Agent) (h c d : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (hgap : h < uniformGap A) :
    ¬ ChoreEF (perturbedRows observer h (c : Circle) (d : Circle)) A := by
  obtain ⟨i, j, hij⟩ := exists_gap_pair A h hgap
  intro hef
  have hcompare := hef j i
  by_cases hj : j = observer
  · simp only [perturbedRows, ite_eq_left hj] at hcompare
    exact (not_lt_of_ge hcompare) (old_strict_gap_preserved h c d hh hc0 hc1 hd0 hd1
      (A.share i) (A.share j) (A.share_measurable i) (A.share_measurable j)
      (share_subset A i) (share_subset A j) hij)
  · simp only [perturbedRows, ite_eq_right hj, uniform_share_value] at hcompare
    linarith

end EnvyFreeResearch.Full.NonnegativeFailure

#print axioms EnvyFreeResearch.Full.NonnegativeFailure.uniform_share_value
#print axioms EnvyFreeResearch.Full.NonnegativeFailure.old_cake_failure_preserved
#print axioms EnvyFreeResearch.Full.NonnegativeFailure.old_chore_failure_preserved
