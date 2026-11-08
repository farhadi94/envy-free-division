import EnvyFreeResearch.Full.UpperLogicalCells
import EnvyFreeResearch.Full.UpperRecordedDomain

/-!
# Degenerate logical cells have no atomless row mass

This uses the finite interval-union geometry, not absolute continuity of the
agents with respect to Lebesgue measure. Singular atomless rows are allowed.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalCellNull

open UpperRecordedDomain UpperLogicalCells

theorem component_interval_null (μ : Measure ℝ) [NullSingletonClass μ]
    (c : Component) (a b : ℝ) (hnull : volume (c.carrier ∩ Ioc a b) = 0) :
    μ (c.carrier ∩ Ioc a b) = 0 := by
  have hsub : Ioo (max c.left a) (min c.right b) ⊆ c.carrier ∩ Ioc a b := by
    intro x hx
    exact ⟨c.interior_subset ⟨lt_of_le_of_lt (le_max_left _ _) hx.1,
      lt_of_lt_of_le hx.2 (min_le_left _ _)⟩,
      lt_of_le_of_lt (le_max_right _ _) hx.1, le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))⟩
  have hzero : volume (Ioo (max c.left a) (min c.right b)) = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hnull) zero_le
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hzero
  have hbound : min c.right b ≤ max c.left a := by linarith
  have hae : c.carrier ∩ Ioc a b =ᵐ[μ] (∅ : Set ℝ) := by
    filter_upwards [μ.ae_ne c.left, μ.ae_ne c.right, μ.ae_ne b] with x hl hr hb
    apply propext
    simp only [mem_empty_iff_false, iff_false, mem_inter_iff, mem_Ioc]
    rintro ⟨hx, hax, hxb⟩
    have hc := c.subset_closed hx
    have hleft : max c.left a < x := max_lt (lt_of_le_of_ne hc.1 hl.symm) hax
    have hright : x < min c.right b := lt_min (lt_of_le_of_ne hc.2 hr) (lt_of_le_of_ne hxb hb)
    exact (not_lt_of_ge hbound) (hleft.trans hright)
  rw [measure_congr hae, measure_empty]

theorem domain_interval_null (μ : Measure ℝ) [NullSingletonClass μ]
    (cs : List Component) (a b : ℝ) (hnull : volume (domain cs ∩ Ioc a b) = 0) :
    μ (domain cs ∩ Ioc a b) = 0 := by
  induction cs with
  | nil => simp [domain]
  | cons c cs ih =>
    have hc : volume (c.carrier ∩ Ioc a b) = 0 :=
      le_antisymm ((measure_mono (inter_subset_inter_left _ subset_union_left)).trans_eq hnull) zero_le
    have ht : volume (domain cs ∩ Ioc a b) = 0 :=
      le_antisymm ((measure_mono (inter_subset_inter_left _ subset_union_right)).trans_eq hnull) zero_le
    rw [domain, union_inter_distrib_right]
    exact measure_union_null (component_interval_null μ c a b hc) (ih ht)

/-- Logical cells of a finite recorded union inherit the zero-volume
property for every atomless row, even when that row is singular. -/
theorem cell_null {m : ℕ} (μ : Measure ℝ) [NullSingletonClass μ]
    (cs : List Component) (cuts : Fin (m + 2) → ℝ) (i : Fin (m + 1))
    (hnull : volume (cell (domain cs) cuts i) = 0) : μ (cell (domain cs) cuts i) = 0 := by
  have hinterval : volume (domain cs ∩ Ioc (cuts i.castSucc) (cuts i.succ)) = 0 :=
    le_antisymm ((measure_mono (show domain cs ∩ Ioc (cuts i.castSucc) (cuts i.succ) ⊆
      cell (domain cs) cuts i from subset_union_left)).trans_eq hnull) zero_le
  rw [measure_congr (cell_ae_eq μ (domain cs) cuts i)]
  exact domain_interval_null μ cs _ _ hinterval

theorem cell_volume_ne_top {m : ℕ} (cs : List Component) (cuts : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) : volume (cell (domain cs) cuts i) ≠ ∞ :=
  measure_ne_top_of_subset ((cell_subset (domain cs) cuts i).trans (domain_subset_unit cs))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem cell_real_null {m : ℕ} (μ : Measure ℝ) [NullSingletonClass μ]
    (cs : List Component) (cuts : Fin (m + 2) → ℝ) (i : Fin (m + 1))
    (hnull : volume.real (cell (domain cs) cuts i) = 0) :
    μ.real (cell (domain cs) cuts i) = 0 := by
  have hz := (measureReal_eq_zero_iff (cell_volume_ne_top cs cuts i)).mp hnull
  simp only [measureReal_def, cell_null μ cs cuts i hz, ENNReal.toReal_zero]

end EnvyFreeResearch.Full.UpperLogicalCellNull
