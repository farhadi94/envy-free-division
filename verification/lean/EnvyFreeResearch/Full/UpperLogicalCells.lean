import EnvyFreeResearch.Full.UpperPayments
import Mathlib.Order.Interval.Set.Union

/-!
# Logical grid cells on a disconnected physical buffer

New grid endpoints delimit logical cells by intersection with the buffer.
A logical cell may cross arbitrarily many previously recorded physical
joins. Its count therefore depends on the new grid, not on the number of
physical buffer components. The original left endpoint is retained literally
in the first logical cell. Atomless masses are exact prefix differences.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperLogicalCells

def cutAt {m : ℕ} (cuts : Fin (m + 1) → ℝ) (i : ℕ) : ℝ :=
  cuts ⟨min i m, (Nat.min_le_right i m).trans_lt (Nat.lt_succ_self m)⟩

theorem cutAt_index {m : ℕ} (cuts : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    cutAt cuts i.val = cuts i := by
  unfold cutAt
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)

theorem consecutive_cover {m : ℕ} (cuts : Fin (m + 1) → ℝ) (hmono : Monotone cuts) :
    (⋃ i : Fin m, Ioc (cuts i.castSucc) (cuts i.succ)) = Ioc (cuts 0) (cuts (Fin.last m)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨(hmono (Fin.zero_le i.castSucc)).trans_lt hi.1,
      hi.2.trans (hmono (Fin.le_last i.succ))⟩
  · intro x hx
    have hx' : x ∈ Ioc (cutAt cuts 0) (cutAt cuts m) := by
      simpa only [← cutAt_index cuts 0, ← cutAt_index cuts (Fin.last m), Fin.val_zero, Fin.val_last] using hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc m (cutAt cuts) hx')
    have hjlt : j < m := Finset.mem_range.mp hj
    let i : Fin m := ⟨j, hjlt⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    have hleft : cutAt cuts j = cuts i.castSucc := cutAt_index cuts i.castSucc
    have hright : cutAt cuts (j + 1) = cuts i.succ := cutAt_index cuts i.succ
    simpa only [hleft, hright] using hxj

theorem consecutive_disjoint {m : ℕ} (cuts : Fin (m + 1) → ℝ) (hmono : Monotone cuts) :
    Pairwise (fun i j : Fin m => Disjoint (Ioc (cuts i.castSucc) (cuts i.succ))
      (Ioc (cuts j.castSucc) (cuts j.succ))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hord : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
    exact (not_lt_of_ge (hxi.2.trans (hmono hord))) hxj.1
  · have hord : j.succ ≤ i.castSucc := by change j.val + 1 ≤ i.val; omega
    exact (not_lt_of_ge (hxj.2.trans (hmono hord))) hxi.1

def cell {m : ℕ} (buffer : Set ℝ) (cuts : Fin (m + 2) → ℝ) (i : Fin (m + 1)) : Set ℝ :=
  (buffer ∩ Ioc (cuts i.castSucc) (cuts i.succ)) ∪
    if i = 0 then buffer ∩ {cuts 0} else ∅

theorem cell_measurable {m : ℕ} (buffer : Set ℝ) (hbuffer : MeasurableSet buffer)
    (cuts : Fin (m + 2) → ℝ) (i : Fin (m + 1)) : MeasurableSet (cell buffer cuts i) := by
  apply (hbuffer.inter measurableSet_Ioc).union
  split_ifs
  · exact hbuffer.inter (measurableSet_singleton _)
  · exact MeasurableSet.empty

theorem cell_subset {m : ℕ} (buffer : Set ℝ) (cuts : Fin (m + 2) → ℝ) (i : Fin (m + 1)) :
    cell buffer cuts i ⊆ buffer := by
  apply union_subset inter_subset_left
  split_ifs
  · exact inter_subset_left
  · exact empty_subset _

theorem cells_disjoint {m : ℕ} (buffer : Set ℝ) (cuts : Fin (m + 2) → ℝ)
    (hmono : Monotone cuts) : Pairwise (fun i j => Disjoint (cell buffer cuts i) (cell buffer cuts j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hzero (k : Fin (m + 1)) : cuts 0 ≤ cuts k.castSucc := hmono (Fin.zero_le _)
  rcases hxi with hxi | hxi
  · rcases hxj with hxj | hxj
    · exact Set.disjoint_left.mp (consecutive_disjoint cuts hmono hij) hxi.2 hxj.2
    · by_cases hj : j = 0
      · simp only [hj, ite_true, mem_inter_iff, mem_singleton_iff] at hxj
        rw [hxj.2] at hxi
        exact (not_lt_of_ge (hzero i)) hxi.2.1
      · simp only [hj, ite_false, mem_empty_iff_false] at hxj
  · by_cases hi : i = 0
    · simp only [hi, ite_true, mem_inter_iff, mem_singleton_iff] at hxi
      rcases hxj with hxj | hxj
      · rw [hxi.2] at hxj
        exact (not_lt_of_ge (hzero j)) hxj.2.1
      · have hj : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
        simp only [hj, ite_false, mem_empty_iff_false] at hxj
    · simp only [hi, ite_false, mem_empty_iff_false] at hxi

theorem cells_cover {m : ℕ} (buffer : Set ℝ) (cuts : Fin (m + 2) → ℝ)
    (hmono : Monotone cuts) (hwithin : buffer ⊆ Icc (cuts 0) (cuts (Fin.last (m + 1)))) :
    (⋃ i, cell buffer cuts i) = buffer := by
  apply Set.Subset.antisymm
  · exact iUnion_subset (cell_subset buffer cuts)
  · intro x hx
    by_cases hzero : x = cuts 0
    · exact mem_iUnion.mpr ⟨0, Or.inr (by simpa only [ite_true, mem_inter_iff, mem_singleton_iff] using ⟨hx, hzero⟩)⟩
    · have hI : x ∈ Ioc (cuts 0) (cuts (Fin.last (m + 1))) :=
        ⟨lt_of_le_of_ne (hwithin hx).1 (Ne.symm hzero), (hwithin hx).2⟩
      rw [← consecutive_cover cuts hmono] at hI
      obtain ⟨i, hi⟩ := mem_iUnion.mp hI
      exact mem_iUnion.mpr ⟨i, Or.inl ⟨hx, hi⟩⟩

theorem cell_ae_eq {m : ℕ} (μ : Measure ℝ) [NullSingletonClass μ]
    (buffer : Set ℝ) (cuts : Fin (m + 2) → ℝ) (i : Fin (m + 1)) :
    cell buffer cuts i =ᵐ[μ] buffer ∩ Ioc (cuts i.castSucc) (cuts i.succ) := by
  filter_upwards [μ.ae_ne (cuts 0)] with x hx
  apply propext
  by_cases hi : i = 0 <;> simp [cell, hi, hx]

theorem cell_mass_prefix {m : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (buffer : Set ℝ) (hbuffer : MeasurableSet buffer)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts) (i : Fin (m + 1)) :
    μ.real (cell buffer cuts i) = μ.real (buffer ∩ Iic (cuts i.succ)) -
      μ.real (buffer ∩ Iic (cuts i.castSucc)) := by
  rw [measureReal_congr (cell_ae_eq μ buffer cuts i)]
  have hsub : buffer ∩ Iic (cuts i.castSucc) ⊆ buffer ∩ Iic (cuts i.succ) :=
    inter_subset_inter_right _ (Iic_subset_Iic.mpr (hmono (by change i.val ≤ i.val + 1; omega)))
  have hset : (buffer ∩ Iic (cuts i.succ)) \ (buffer ∩ Iic (cuts i.castSucc)) =
      buffer ∩ Ioc (cuts i.castSucc) (cuts i.succ) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨⟨hb, hr⟩, hn⟩
      exact ⟨hb, lt_of_not_ge (fun hl => hn ⟨hb, hl⟩), hr⟩
    · rintro ⟨hb, hl, hr⟩
      exact ⟨⟨hb, hr⟩, fun h => (not_lt_of_ge h.2) hl⟩
  rw [← hset, measureReal_sdiff hsub (hbuffer.inter measurableSet_Iic)]

/-- Normalized physical buffer rows give a normalized finite logical-cell
cache, regardless of how many old physical joins each cell crosses. -/
theorem cell_mass_sum {m : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (buffer : Set ℝ) (hbuffer : MeasurableSet buffer)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts)
    (hwithin : buffer ⊆ Icc (cuts 0) (cuts (Fin.last (m + 1)))) :
    (∑ i, μ.real (cell buffer cuts i)) = μ.real buffer := by
  calc
    _ = μ.real (⋃ i, cell buffer cuts i) :=
      (measureReal_iUnion_fintype (cells_disjoint buffer cuts hmono)
        (cell_measurable buffer hbuffer cuts)).symm
    _ = _ := congrArg μ.real (cells_cover buffer cuts hmono hwithin)

end EnvyFreeResearch.Full.UpperLogicalCells
