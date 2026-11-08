import EnvyFreeResearch.Full.UpperSnapshotContrastMatrix

/-! Finite algebra behind the Snapshot margin for both cake and chores.
The row-range bound is derived from actual values and payment errors. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
variable {k : ℕ}

def signedGap (chores : Bool) (Z : Fin k → Fin k → ℝ) (i j : Fin k) : ℝ :=
  if chores then Z i j - Z i i else Z i i - Z i j

def paid (V : Fin k → Fin k → ℝ) (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ) (i j : Fin k) : ℝ :=
  V i (pi j) + t j

theorem signedGap_self (chores : Bool) (Z : Fin k → Fin k → ℝ) (i : Fin k) :
    signedGap chores Z i i = 0 := by cases chores <;> simp [signedGap]

theorem gap_nonnegative (chores : Bool) (Z e : Fin k → Fin k → ℝ)
    (herr : ∀ i j, |e i j| ≤ signedGap chores Z i j) (i j : Fin k) :
    0 ≤ signedGap chores Z i j := (abs_nonneg (e i j)).trans (herr i j)

theorem paid_row_identity (chores : Bool) (V Z e : Fin k → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (hvalues : ∀ i j, Z i j = paid V pi t i j + e i j) (i j : Fin k) :
    paid V pi t i j = Z i i +
      (if chores then signedGap chores Z i j - e i j else -(signedGap chores Z i j + e i j)) := by
  have hv := hvalues i j
  cases chores <;> simp only [signedGap, Bool.false_eq_true, ite_false, ite_true] <;> linarith

/-- Each row of the ideally paid matrix has range at most twice the largest
actual normalized envy-free margin. -/
theorem paid_row_range (chores : Bool) (V Z e : Fin k → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (hvalues : ∀ i j, Z i j = paid V pi t i j + e i j)
    (herr : ∀ i j, |e i j| ≤ signedGap chores Z i j)
    (Delta : ℝ) (hmax : ∀ i j, signedGap chores Z i j ≤ Delta) (i u v : Fin k) :
    paid V pi t i u - paid V pi t i v ≤ 2 * Delta := by
  have hu := paid_row_identity chores V Z e pi t hvalues i u
  have hv := paid_row_identity chores V Z e pi t hvalues i v
  have heu := abs_le.mp (herr i u)
  have hev := abs_le.mp (herr i v)
  have hmu := hmax i u
  have hmv := hmax i v
  cases chores <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hu hv <;> linarith

/-- Column payments cancel exactly, and inverse assignment columns recover
the selected old-label contrast. -/
theorem paid_contrast (V : Fin k → Fin k → ℝ) (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (i h u v : Fin k) :
    contrast V i h u v = contrast (paid V pi t) i h (pi.symm u) (pi.symm v) := by
  simp only [contrast, paid, Equiv.apply_symm_apply]
  ring

theorem contrast_le_four_gap (chores : Bool) (V Z e : Fin k → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (hvalues : ∀ i j, Z i j = paid V pi t i j + e i j)
    (herr : ∀ i j, |e i j| ≤ signedGap chores Z i j)
    (Delta : ℝ) (hmax : ∀ i j, signedGap chores Z i j ≤ Delta) (i h u v : Fin k) :
    contrast V i h u v ≤ 4 * Delta := by
  have hi := paid_row_range chores V Z e pi t hvalues herr Delta hmax i (pi.symm u) (pi.symm v)
  have hh := paid_row_range chores V Z e pi t hvalues herr Delta hmax h (pi.symm v) (pi.symm u)
  rw [paid_contrast V pi t]
  unfold contrast
  linarith

/-- A nonzero contrast forces a strictly positive, off-diagonal maximizing
actual margin. No row-range or maximum-margin conclusion is a premise. -/
theorem exists_large_gap (hk : 0 < k) (chores : Bool) (V Z e : Fin k → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (hvalues : ∀ i j, Z i j = paid V pi t i j + e i j)
    (herr : ∀ i j, |e i j| ≤ signedGap chores Z i j)
    (i h u v : Fin k) (Lambda theta : ℝ) (hLambda : 0 < Lambda) (htheta : 0 < theta)
    (hcontrast : Lambda / theta ≤ contrast V i h u v) :
    ∃ a b, a ≠ b ∧ Lambda / (4 * theta) ≤ signedGap chores Z a b ∧
      ∀ c d, signedGap chores Z c d ≤ signedGap chores Z a b := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨p, _, hp⟩ := Finset.univ.exists_max_image (fun p : Fin k × Fin k => signedGap chores Z p.1 p.2) Finset.univ_nonempty
  have hmax (c d : Fin k) : signedGap chores Z c d ≤ signedGap chores Z p.1 p.2 := hp (c, d) (Finset.mem_univ _)
  have hb := contrast_le_four_gap chores V Z e pi t hvalues herr _ hmax i h u v
  have hlarge : Lambda / (4 * theta) ≤ signedGap chores Z p.1 p.2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * theta)).mpr
    have hc := (div_le_iff₀ htheta).mp (hcontrast.trans hb)
    nlinarith
  refine ⟨p.1, p.2, ?_, hlarge, hmax⟩
  intro heq
  have hpos : 0 < signedGap chores Z p.1 p.2 := (div_pos hLambda (by positivity)).trans_le hlarge
  rw [heq, signedGap_self] at hpos
  exact (lt_irrefl 0) hpos

end EnvyFreeResearch.Full.UpperSnapshotContrast
