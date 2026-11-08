import EnvyFreeResearch.Full.UpperAggregateInterpolationCharge

/-!
# Cancellation at selected interval boundaries

Summation by parts derives the actual signs. Adjacent selected cells cancel
their shared boundary, and each remaining boundary coefficient has absolute
value at most one. Distinct boundary coordinates are charged to distinct
original occurrences in the generated endpoint list.
-/

noncomputable section

open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

/-- Incoming minus outgoing selection at a boundary. -/
def boundaryCoefficient {m : ℕ} (selected : Fin m → ℝ) (p : Fin (m + 1)) : ℝ :=
  Fin.cons (α := fun _ : Fin (m + 1) => ℝ) 0 selected p - Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) selected 0 p

theorem summation_by_parts {m : ℕ} (selected : Fin m → ℝ) (H : Fin (m + 1) → ℝ) :
    (∑ i, selected i * (H i.succ - H i.castSucc)) =
      ∑ p, boundaryCoefficient selected p * H p := by
  have hin : (∑ p : Fin (m + 1), Fin.cons (α := fun _ : Fin (m + 1) => ℝ) 0 selected p * H p) =
      ∑ i : Fin m, selected i * H i.succ := by
    rw [Fin.sum_univ_succ]
    simp
  have hout : (∑ p : Fin (m + 1), Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) selected 0 p * H p) =
      ∑ i : Fin m, selected i * H i.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp
  simp_rw [boundaryCoefficient, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hin, hout]

theorem boundaryCoefficient_abs_le {m : ℕ} (selected : Fin m → ℝ)
    (hselected : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1) (p : Fin (m + 1)) :
    |boundaryCoefficient selected p| ≤ 1 := by
  have hin : 0 ≤ Fin.cons (α := fun _ : Fin (m + 1) => ℝ) 0 selected p ∧ Fin.cons (α := fun _ : Fin (m + 1) => ℝ) 0 selected p ≤ 1 := by
    refine Fin.cases ?_ (fun i => ?_) p
    · simp
    · simpa using hselected i
  have hout : 0 ≤ Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) selected 0 p ∧ Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) selected 0 p ≤ 1 := by
    refine Fin.lastCases ?_ (fun i => ?_) p
    · simp
    · simpa using hselected i
  apply abs_le.mpr
  dsimp [boundaryCoefficient]
  constructor <;> linarith

/-- A chosen union has only unit boundary charges, despite arbitrarily many
adjacent cells. The selection may even take any values in `[0,1]`. -/
theorem selected_increment_error_le {m : ℕ} (selected : Fin m → ℝ)
    (hselected : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1) (H : Fin (m + 1) → ℝ) :
    |∑ i, selected i * (H i.succ - H i.castSucc)| ≤ ∑ p, |H p| := by
  rw [summation_by_parts]
  calc
    _ ≤ ∑ p, |boundaryCoefficient selected p * H p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun p _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (boundaryCoefficient_abs_le selected hselected p)
        (abs_nonneg (H p))).trans_eq (one_mul _))

/-- Every nonzero boundary error is assigned to one occurrence of the same
coordinate in the generated list. Injectivity of boundary coordinates makes
these assignments injective, even if the generated list itself repeats points. -/
theorem boundary_sum_le_generated {Boundary Generated : Type*} [Fintype Boundary] [Fintype Generated]
    (cuts : Boundary → ℝ) (hcuts : Function.Injective cuts) (points : Generated → ℝ)
    (H : ℝ → ℝ) (hcover : ∀ p, H (cuts p) = 0 ∨ ∃ j, points j = cuts p) :
    ∑ p, |H (cuts p)| ≤ ∑ j, |H (points j)| := by
  let Active := {p : Boundary // H (cuts p) ≠ 0}
  have hex (p : Active) : ∃ j, points j = cuts p := (hcover p).resolve_left p.property
  let assign (p : Active) : Generated := Classical.choose (hex p)
  have hassign (p : Active) : points (assign p) = cuts p := Classical.choose_spec (hex p)
  have hinj : Function.Injective assign := by
    intro p q hpq
    apply Subtype.ext
    apply hcuts
    rw [← hassign p, ← hassign q, hpq]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun p => H (cuts p) ≠ 0) (fun p => |H (cuts p)|)
  have hzero : (∑ p : {p : Boundary // ¬ H (cuts p) ≠ 0}, |H (cuts p)|) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    simp [not_not.mp p.property]
  rw [hzero, add_zero] at hsplit
  rw [← hsplit]
  exact Finset.sum_le_sum_of_injOn assign hinj.injOn (Finset.subset_univ _)
    (fun p _ => le_of_eq (by rw [hassign p])) (fun j _ _ => abs_nonneg _)

/-- Pointwise telescoping for an arbitrary selection made after all endpoint
values are observed. Original grid boundaries are admitted by the zero-error
branch, and reused generated coordinates need no new charge. -/
theorem selected_union_error_le_generated {m : ℕ} {Generated : Type*} [Fintype Generated]
    (cuts : Fin (m + 1) → ℝ) (hcuts : Function.Injective cuts) (points : Generated → ℝ)
    (H : ℝ → ℝ) (hcover : ∀ p, H (cuts p) = 0 ∨ ∃ j, points j = cuts p)
    (selected : Fin m → ℝ) (hselected : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1) :
    |∑ i, selected i * (H (cuts i.succ) - H (cuts i.castSucc))| ≤ ∑ j, |H (points j)| :=
  (selected_increment_error_le selected hselected (H ∘ cuts)).trans
    (boundary_sum_le_generated cuts hcuts points H hcover)

end EnvyFreeResearch.Full.UpperAggregateInterpolation
