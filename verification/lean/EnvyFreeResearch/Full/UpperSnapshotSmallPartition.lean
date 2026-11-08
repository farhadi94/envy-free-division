import EnvyFreeResearch.Full.UpperSnapshotSmallExecution
import EnvyFreeResearch.Full.UpperSnapshotSmallPrefixes

/-! Consecutive literal prefixes give a shared-circle physical partition.
The endpoint at cumulative mass one is the already recorded initial root. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution

variable {J : ℕ}

def boundary (hJ : 0 < J) (points : Fin J → ℝ) (j : Fin (J + 1)) : ℝ :=
  if hj : j.val < J then points ⟨j.val, hj⟩ else points ⟨0, hJ⟩

def shifts (q : Fin (J + 1) → I) (j : Fin J) : Circle := project (q j.castSucc)

def circularPrefix (hJ : 0 < J) (domain : Set ℝ) (q : Fin (J + 1) → I)
    (start : Circle) (points : Fin J → ℝ) (j : Fin (J + 1)) : Set ℝ :=
  physicalPiece domain (q j) start (points ⟨0, hJ⟩) (boundary hJ points j)

def part (hJ : 0 < J) (domain : Set ℝ) (q : Fin (J + 1) → I)
    (start : Circle) (points : Fin J → ℝ) (j : Fin J) : Set ℝ :=
  circularPrefix hJ domain q start points j.succ \ circularPrefix hJ domain q start points j.castSucc

theorem boundary_castSucc (hJ : 0 < J) (points : Fin J → ℝ) (j : Fin J) :
    boundary hJ points j.castSucc = points j := by simp [boundary, j.isLt]

theorem boundary_last (hJ : 0 < J) (points : Fin J → ℝ) :
    boundary hJ points (Fin.last J) = points ⟨0, hJ⟩ := by simp [boundary]

theorem prefix_zero (hJ : 0 < J) (domain : Set ℝ) (q : Fin (J + 1) → I)
    (hq0 : q 0 = 0) (start : Circle) (points : Fin J → ℝ) :
    circularPrefix hJ domain q start points 0 = ∅ := by simp [circularPrefix, hq0, physicalPiece_zero]

theorem prefix_last (hJ : 0 < J) (domain : Set ℝ) (q : Fin (J + 1) → I)
    (hq1 : q (Fin.last J) = 1) (start : Circle) (points : Fin J → ℝ) :
    circularPrefix hJ domain q start points (Fin.last J) = domain := by simp [circularPrefix, hq1, physicalPiece_one]

theorem prefix_subset (hJ : 0 < J) (domain : Set ℝ) (q : Fin (J + 1) → I)
    (start : Circle) (points : Fin J → ℝ) (j : Fin (J + 1)) :
    circularPrefix hJ domain q start points j ⊆ domain := physicalPiece_subset _ _ _ _ _

theorem prefix_measurable (hJ : 0 < J) (domain : Set ℝ) (hdomain : MeasurableSet domain)
    (q : Fin (J + 1) → I) (start : Circle) (points : Fin J → ℝ) (j : Fin (J + 1)) :
    MeasurableSet (circularPrefix hJ domain q start points j) := by
  unfold circularPrefix physicalPiece
  split_ifs <;> first | exact MeasurableSet.empty | exact hdomain |
    exact hdomain.inter measurableSet_Ioc | exact hdomain.diff measurableSet_Ioc

theorem prefix_mono (hJ : 0 < J) (domain : Set ℝ) (q : Fin (J + 1) → I)
    (hq : StrictMono q) (start : Circle) (points : Fin J → ℝ) (F : ℝ → ℝ) (hF : Monotone F)
    (hlegal : ∀ j, F (boundary hJ points j) = (value (start + project (q j)) : ℝ)) :
    Monotone (circularPrefix hJ domain q start points) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact Subset.rfl
  · exact physical_prefix_mono domain start (q i) (q j) (hq hij) _ _ _ F hF (hlegal i) (hlegal j)

/-- A finite increasing sequence of sets starting empty is the disjoint
union of its consecutive differences. This is literal set equality. -/
theorem nested_parts_cover {α : Type*} (P : Fin (J + 1) → Set α)
    (hmono : Monotone P) (hzero : P 0 = ∅) :
    (⋃ j : Fin J, P j.succ \ P j.castSucc) = P (Fin.last J) := by
  apply Subset.antisymm
  · exact iUnion_subset (fun j => sdiff_subset.trans (hmono (Fin.le_last j.succ)))
  · intro x hx
    let s : Finset (Fin (J + 1)) := Finset.univ.filter (fun j => x ∈ P j)
    have hs : s.Nonempty := ⟨Fin.last J, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    let j := s.min' hs
    have hj : x ∈ P j := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
    have hj0 : j.val ≠ 0 := by
      intro hz
      have he : j = 0 := Fin.ext hz
      rw [he, hzero] at hj
      exact hj
    let i : Fin J := ⟨j.val - 1, by have hb := j.isLt; omega⟩
    have hsucc : i.succ = j := by apply Fin.ext; simp only [Fin.val_succ]; dsimp [i]; omega
    refine mem_iUnion.mpr ⟨i, ?_⟩
    refine ⟨hsucc ▸ hj, ?_⟩
    intro hi
    have hi' : i.castSucc ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hmin := Finset.min'_le s i.castSucc hi'
    change j.val ≤ i.val at hmin
    dsimp [i] at hmin
    omega

theorem nested_parts_disjoint {α : Type*} (P : Fin (J + 1) → Set α) (hmono : Monotone P) :
    Pairwise (fun i j : Fin J => Disjoint (P i.succ \ P i.castSucc) (P j.succ \ P j.castSucc)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hord : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
    exact hxj.2 (hmono hord hxi.1)
  · have hord : j.succ ≤ i.castSucc := by change j.val + 1 ≤ i.val; omega
    exact hxi.2 (hmono hord hxj.1)

theorem parts_partition (hJ : 0 < J) (domain : Set ℝ) (q : Fin (J + 1) → I)
    (hq : StrictMono q) (hq0 : q 0 = 0) (hq1 : q (Fin.last J) = 1)
    (start : Circle) (points : Fin J → ℝ) (F : ℝ → ℝ) (hF : Monotone F)
    (hlegal : ∀ j, F (boundary hJ points j) = (value (start + project (q j)) : ℝ)) :
    (⋃ j, part hJ domain q start points j) = domain ∧
      Pairwise (fun i j => Disjoint (part hJ domain q start points i) (part hJ domain q start points j)) := by
  have hm := prefix_mono hJ domain q hq start points F hF hlegal
  constructor
  · exact (nested_parts_cover _ hm (prefix_zero hJ domain q hq0 start points)).trans
      (prefix_last hJ domain q hq1 start points)
  · exact nested_parts_disjoint _ hm

end EnvyFreeResearch.Full.UpperSnapshotSmall
