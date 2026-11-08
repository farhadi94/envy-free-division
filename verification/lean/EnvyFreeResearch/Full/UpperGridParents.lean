import EnvyFreeResearch.Full.UpperGridInterior

/-!
# Deterministic coarse parents of the actual refined logical cells

Parents are selected by finite comparisons of recorded grid coordinates.
Literal containment includes the first cell's owned left endpoint, and the
selection is Borel. No old physical join enters either finite index set.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperGridParents

open UpperLogicalCells UpperQuantileBounds UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperRecordedQuantiles UpperCommonGrid Chores

variable {a b : ℕ}

def Fits (coarse : Fin (a + 2) → ℝ) (fine : Fin (b + 2) → ℝ)
    (i : Fin (b + 1)) (j : Fin (a + 1)) : Prop :=
  coarse j.castSucc ≤ fine i.castSucc ∧ fine i.succ ≤ coarse j.succ ∧ (i = 0 → j = 0)

/-- Inclusion of every coarse boundary prevents a fine interval from crossing
one. Uniqueness of the zero boundary also handles literal endpoint ownership. -/
theorem exists_parent (coarse : Fin (a + 2) → ℝ) (fine : Fin (b + 2) → ℝ)
    (hc : Monotone coarse) (hf : Monotone fine)
    (hc0 : coarse 0 = 0) (hf0 : fine 0 = 0)
    (hc1 : coarse (Fin.last (a + 1)) = 1) (hf1 : fine (Fin.last (b + 1)) = 1)
    (hcz : ∀ j, coarse j = 0 → j = 0)
    (hcontains : ∀ c, ∃ f, fine f = coarse c) (i : Fin (b + 1)) :
    ∃ j, Fits coarse fine i j := by
  have hleft0 : 0 ≤ fine i.castSucc := by rw [← hf0]; exact hf (Fin.zero_le _)
  have hright0 : 0 ≤ fine i.succ := by rw [← hf0]; exact hf (Fin.zero_le _)
  have hright1 : fine i.succ ≤ 1 := by rw [← hf1]; exact hf (Fin.le_last _)
  by_cases hp : 0 < fine i.succ
  · have hmem : fine i.succ ∈ Ioc (coarse 0) (coarse (Fin.last (a + 1))) := by
      rw [hc0, hc1]
      exact ⟨hp, hright1⟩
    rw [← consecutive_cover coarse hc] at hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    have hl : coarse j.castSucc ≤ fine i.castSucc := by
      by_contra hn
      obtain ⟨f, heq⟩ := hcontains j.castSucc
      exact no_grid_point_between fine hf i f (by rw [heq]; exact ⟨lt_of_not_ge hn, hj.1⟩)
    refine ⟨j, hl, hj.2, ?_⟩
    intro hi
    have hz : coarse j.castSucc = 0 := by
      have hz0 : 0 ≤ coarse j.castSucc := by rw [← hc0]; exact hc (Fin.zero_le _)
      rw [hi, Fin.castSucc_zero, hf0] at hl
      exact le_antisymm hl hz0
    exact Fin.ext (congrArg (fun x : Fin (a + 2) => x.val) (hcz j.castSucc hz))
  · have hr : fine i.succ = 0 := le_antisymm (le_of_not_gt hp) hright0
    have hc01 : 0 ≤ coarse (0 : Fin (a + 1)).succ := by rw [← hc0]; exact hc (Fin.zero_le _)
    refine ⟨0, ?_, ?_, fun _ => rfl⟩
    · simpa only [Fin.castSucc_zero, hc0] using hleft0
    · simpa only [hr] using hc01

def firstParent (coarse : Fin (a + 2) → ℝ) (fine : Fin (b + 2) → ℝ) (i : Fin (b + 1)) :
    List (Fin (a + 1)) → Fin (a + 1)
  | [] => 0
  | j :: rest => if Fits coarse fine i j then j else firstParent coarse fine i rest

theorem firstParent_spec (coarse : Fin (a + 2) → ℝ) (fine : Fin (b + 2) → ℝ)
    (i : Fin (b + 1)) (candidates : List (Fin (a + 1)))
    (h : ∃ j ∈ candidates, Fits coarse fine i j) : Fits coarse fine i (firstParent coarse fine i candidates) := by
  induction candidates with
  | nil => simp at h
  | cons j rest ih =>
    by_cases hj : Fits coarse fine i j
    · simp only [firstParent, hj, ite_true]
    · simp only [firstParent, hj, ite_false]
      apply ih
      obtain ⟨k, hk, hf⟩ := h
      rcases List.mem_cons.mp hk with rfl | hk
      · exact (hj hf).elim
      · exact ⟨k, hk, hf⟩

def parent (coarse : Fin (a + 2) → ℝ) (fine : Fin (b + 2) → ℝ) (i : Fin (b + 1)) : Fin (a + 1) :=
  firstParent coarse fine i Finset.univ.toList

theorem parent_fits (coarse : Fin (a + 2) → ℝ) (fine : Fin (b + 2) → ℝ)
    (hc : Monotone coarse) (hf : Monotone fine)
    (hc0 : coarse 0 = 0) (hf0 : fine 0 = 0)
    (hc1 : coarse (Fin.last (a + 1)) = 1) (hf1 : fine (Fin.last (b + 1)) = 1)
    (hcz : ∀ j, coarse j = 0 → j = 0) (hcontains : ∀ c, ∃ f, fine f = coarse c)
    (i : Fin (b + 1)) : Fits coarse fine i (parent coarse fine i) := by
  obtain ⟨j, hj⟩ := exists_parent coarse fine hc hf hc0 hf0 hc1 hf1 hcz hcontains i
  exact firstParent_spec coarse fine i _ ⟨j, by simp, hj⟩

theorem cell_subset_parent (buffer : Set ℝ) (coarse : Fin (a + 2) → ℝ)
    (fine : Fin (b + 2) → ℝ) (hc0 : coarse 0 = 0) (hf0 : fine 0 = 0)
    (i : Fin (b + 1)) (j : Fin (a + 1)) (h : Fits coarse fine i j) :
    cell buffer fine i ⊆ cell buffer coarse j := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl ⟨hx.1, lt_of_le_of_lt h.1 hx.2.1, hx.2.2.trans h.2.1⟩
  · by_cases hi : i = 0
    · have hj := h.2.2 hi
      subst i
      subst j
      right
      simpa only [ite_true, hc0, hf0] using hx
    · simp only [hi, ite_false, mem_empty_iff_false] at hx

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem fits_measurableSet (coarse : X → Fin (a + 2) → ℝ) (fine : X → Fin (b + 2) → ℝ)
    (hc : ∀ j, Measurable (fun z => coarse z j)) (hf : ∀ j, Measurable (fun z => fine z j))
    (i : Fin (b + 1)) (j : Fin (a + 1)) : MeasurableSet {z | Fits (coarse z) (fine z) i j} := by
  have hconst : MeasurableSet {z : X | i = 0 → j = 0} := by
    by_cases h : i = 0 → j = 0 <;> simp [h]
  exact (measurableSet_le (hc j.castSucc) (hf i.castSucc)).inter
    ((measurableSet_le (hf i.succ) (hc j.succ)).inter hconst)

theorem firstParent_measurable (coarse : X → Fin (a + 2) → ℝ) (fine : X → Fin (b + 2) → ℝ)
    (hc : ∀ j, Measurable (fun z => coarse z j)) (hf : ∀ j, Measurable (fun z => fine z j))
    (i : Fin (b + 1)) (candidates : List (Fin (a + 1))) :
    Measurable (fun z => firstParent (coarse z) (fine z) i candidates) := by
  induction candidates with
  | nil => exact measurable_const
  | cons j rest ih => exact measurable_const.ite (fits_measurableSet coarse fine hc hf i j) ih

theorem parent_measurable (coarse : X → Fin (a + 2) → ℝ) (fine : X → Fin (b + 2) → ℝ)
    (hc : ∀ j, Measurable (fun z => coarse z j)) (hf : ∀ j, Measurable (fun z => fine z j))
    (i : Fin (b + 1)) : Measurable (fun z => parent (coarse z) (fine z) i) :=
  firstParent_measurable coarse fine hc hf i _

end Measurability

end EnvyFreeResearch.Full.UpperGridParents
