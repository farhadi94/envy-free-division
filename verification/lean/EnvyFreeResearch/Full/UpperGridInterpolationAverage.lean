import EnvyFreeResearch.Full.UpperGridInterpolationCoarsen
import EnvyFreeResearch.Full.UpperSortedGrid

/-!
# Symmetric finite scores on an augmented grid

Equal grid coordinates share their deletion score by averaging over their
finite fiber. Thus permutation covariance and the total bound hold even on
collision tuples. At a unique inserted coordinate this is exactly its usual
point-deletion interpolation error.
-/

noncomputable section

open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity UpperSortedGrid

variable {Index Value : Type*} [Fintype Index]

def fiberCount (f : Index → Value) (z : Value) : ℝ :=
  ∑ i, if f i = z then 1 else 0

def fiberMean (f : Index → Value) (h : Index → ℝ) (z : Value) : ℝ :=
  ∑ i, if f i = z then h i / fiberCount f z else 0

theorem fiberCount_nonneg (f : Index → Value) (z : Value) : 0 ≤ fiberCount f z := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

theorem fiberCount_pos (f : Index → Value) (i : Index) : 0 < fiberCount f (f i) := by
  have h : (1 : ℝ) ≤ fiberCount f (f i) := by
    calc
      1 = (if f i = f i then (1 : ℝ) else 0) := by simp
      _ ≤ ∑ j, if f j = f i then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if f j = f i then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  linarith

theorem fiberMean_nonneg (f : Index → Value) (h : Index → ℝ)
    (hh : ∀ i, 0 ≤ h i) (z : Value) : 0 ≤ fiberMean f h z := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact div_nonneg (hh i) (fiberCount_nonneg f z)
  · exact le_rfl

theorem fiberMean_eq_div (f : Index → Value) (h : Index → ℝ) (z : Value) :
    fiberMean f h z = (∑ i, if f i = z then h i else 0) / fiberCount f z := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp at *

theorem fiberMean_le_one (f : Index → Value) (h : Index → ℝ)
    (hh : ∀ i, h i ≤ 1) (z : Value) : fiberMean f h z ≤ 1 := by
  rw [fiberMean_eq_div]
  by_cases hz : fiberCount f z = 0
  · simp [hz]
  · have hp : 0 < fiberCount f z :=
      lt_of_le_of_ne (fiberCount_nonneg f z) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    simp only [one_mul]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact hh i
    · exact le_rfl

/-- Finite double counting: each value fiber contributes its original total. -/
theorem sum_fiberMean (f : Index → Value) (h : Index → ℝ) :
    ∑ i, fiberMean f h (f i) = ∑ i, h i := by
  unfold fiberMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have heq : (∑ i, if f j = f i then h j / fiberCount f (f i) else 0) =
      fiberCount f (f j) * (h j / fiberCount f (f j)) := by
    change _ = (∑ i, if f i = f j then (1 : ℝ) else 0) * (h j / fiberCount f (f j))
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he : f i = f j
    · simp [he]
    · simp [he, Ne.symm he]
  rw [heq]
  field_simp [ne_of_gt (fiberCount_pos f j)]

theorem fiberMean_unique (f : Index → Value) (h : Index → ℝ) (i : Index)
    (hunique : ∀ j, f j = f i → j = i) : fiberMean f h (f i) = h i := by
  have hiff (j : Index) : f j = f i ↔ j = i := ⟨hunique j, fun h => h ▸ rfl⟩
  simp [fiberMean, fiberCount, hiff]

/-- Extend the interior-point scores by zero at the two outer coordinates. -/
def nodeScores {m : ℕ} (d : Fin m → ℝ) : Fin (m + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc d 0)

@[simp] theorem nodeScores_interior {m : ℕ} (d : Fin m → ℝ) (p : Fin m) :
    nodeScores d p.succ.castSucc = d p := by simp [nodeScores, Fin.castSucc_succ]

theorem nodeScores_nonneg {m : ℕ} (d : Fin m → ℝ) (hd : ∀ p, 0 ≤ d p) :
    ∀ i, 0 ≤ nodeScores d i := by
  intro i
  refine Fin.cases (by simp [nodeScores]) (fun j => ?_) i
  refine Fin.lastCases (by simp [nodeScores]) (fun p => ?_) j
  simpa [nodeScores] using hd p

theorem nodeScores_le_one {m : ℕ} (d : Fin m → ℝ) (hd : ∀ p, d p ≤ 1) :
    ∀ i, nodeScores d i ≤ 1 := by
  intro i
  refine Fin.cases (by simp [nodeScores]) (fun j => ?_) i
  refine Fin.lastCases (by simp [nodeScores]) (fun p => ?_) j
  simpa [nodeScores] using hd p

theorem sum_nodeScores {m : ℕ} (d : Fin m → ℝ) : ∑ i, nodeScores d i = ∑ p, d p := by
  rw [Fin.sum_univ_succ]
  simp only [nodeScores, Fin.cons_zero, Fin.cons_succ, zero_add]
  rw [Fin.sum_univ_castSucc]
  simp

variable {Row : Type*} [Fintype Row] [Nonempty Row]

def gridRows {m : ℕ} (F : Row → ℝ → ℝ) (values : Fin (m + 2) → ℝ) :
    Row → Fin (m + 1) → ℝ := increments (fun i e => F i (sorted values e))

def gridTheta {m : ℕ} (L : ℝ → ℝ) (values : Fin (m + 2) → ℝ) (p : Fin m) : ℝ :=
  (L (sorted values p.succ.castSucc) - L (sorted values p.castSucc.castSucc)) /
    (L (sorted values p.succ.succ) - L (sorted values p.castSucc.castSucc))

theorem gridTheta_mem {m : ℕ} (L : ℝ → ℝ) (hL : Monotone L)
    (values : Fin (m + 2) → ℝ) (p : Fin m) :
    0 ≤ gridTheta L values p ∧ gridTheta L values p ≤ 1 := by
  have hmono := hL.comp (sorted_monotone values)
  have hl : L (sorted values p.castSucc.castSucc) ≤ L (sorted values p.succ.castSucc) :=
    hmono (by simp [Fin.le_def])
  have hr : L (sorted values p.succ.castSucc) ≤ L (sorted values p.succ.succ) :=
    hmono (by simp [Fin.le_def])
  have hden := sub_nonneg.mpr (hl.trans hr)
  refine ⟨div_nonneg (sub_nonneg.mpr hl) hden, ?_⟩
  by_cases hz : L (sorted values p.succ.succ) - L (sorted values p.castSucc.castSucc) = 0
  · simp [gridTheta, hz]
  · apply (div_le_iff₀ (lt_of_le_of_ne hden (Ne.symm hz))).mpr
    simp only [one_mul]
    linarith

def gridDeletions {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (values : Fin (m + 2) → ℝ) (p : Fin m) : ℝ :=
  maxDeletion (gridRows F values) p.castSucc p.succ (gridTheta L values p)

def gridScore {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (values : Fin (m + 2) → ℝ) (z : ℝ) : ℝ :=
  fiberMean (sorted values) (nodeScores (gridDeletions F L values)) z

theorem gridScore_nonneg {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (values : Fin (m + 2) → ℝ) (z : ℝ) : 0 ≤ gridScore F L values z :=
  fiberMean_nonneg _ _ (nodeScores_nonneg _ (fun _ => maxDeletion_nonneg _ _ _ _)) _

theorem sorted_perm {m : ℕ} (values : Fin m → ℝ) (perm : Equiv.Perm (Fin m)) :
    sorted (values ∘ perm) = sorted values := by
  have h := Tuple.unique_monotone (f := values)
    (σ := perm * select (values ∘ perm)) (τ := select values)
    (by simpa [sorted, Function.comp_def] using sorted_monotone (values ∘ perm))
    (sorted_monotone values)
  simpa [sorted, Function.comp_def] using h

theorem gridScore_perm {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (values : Fin (m + 2) → ℝ) (perm : Equiv.Perm (Fin (m + 2))) (z : ℝ) :
    gridScore F L (values ∘ perm) z = gridScore F L values z := by
  have hd : gridDeletions F L (values ∘ perm) = gridDeletions F L values := by
    funext p
    simp only [gridDeletions, gridRows, gridTheta, sorted_perm]
  simp only [gridScore, sorted_perm, hd]

theorem sum_gridScore {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (hL : Monotone L)
    (values : Fin (m + 2) → ℝ) :
    ∑ i, gridScore F L values (values i) ≤ 2 * ((Fintype.card Row : ℝ) - 1) := by
  have heq : (∑ i, gridScore F L values (values i)) =
      ∑ i, gridScore F L values (sorted values i) := by
    exact (Equiv.sum_comp (select values) (fun i => gridScore F L values (values i))).symm
  rw [heq]
  simp only [gridScore]
  rw [sum_fiberMean, sum_nodeScores]
  exact sum_deletion_le (gridRows F values) (gridTheta L values)
    (gridTheta_mem L hL values) Finset.univ

/-- Any distinct raw labels, in particular the sample labels among permanent
boundaries, obey the same total deletion bound. -/
theorem sum_selected_gridScore {m : ℕ} {Sample : Type*} [Fintype Sample]
    (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (hL : Monotone L)
    (values : Fin (m + 2) → ℝ) (labels : Sample → Fin (m + 2))
    (hinj : Function.Injective labels) :
    ∑ j, gridScore F L values (values (labels j)) ≤ 2 * ((Fintype.card Row : ℝ) - 1) := by
  calc
    (∑ j, gridScore F L values (values (labels j))) =
        ∑ i ∈ Finset.univ.image labels, gridScore F L values (values i) := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    _ ≤ ∑ i, gridScore F L values (values i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => gridScore_nonneg F L values _)
    _ ≤ _ := sum_gridScore F L hL values

end EnvyFreeResearch.Full.UpperGridInterpolation
