import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Maximum-determinant witnesses for the proposed reserve-free Repair.
These are finite algebraic lemmas, not an oracle-protocol theorem. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperDeterminant

abbrev Vec := ℝ × ℝ

def det (x y : Vec) : ℝ := x.1*y.2-x.2*y.1

def value (u v : ℝ) (x : Vec) : ℝ := u*x.1+v*x.2

theorem cramer (F G E : Vec) (h : det F G ≠ 0) :
    E.1 = (det E G / det F G)*F.1+(det F E / det F G)*G.1 ∧
    E.2 = (det E G / det F G)*F.2+(det F E / det F G)*G.2 := by
  constructor
  all_goals
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff h).mpr
    unfold det
    ring

theorem functional_cramer (F G E : Vec) (h : det F G ≠ 0) (u v : ℝ) :
    value u v E = (det E G / det F G)*value u v F+
      (det F E / det F G)*value u v G := by
  obtain ⟨hx,hy⟩ := cramer F G E h
  unfold value
  calc
    u*E.1+v*E.2 = u*((det E G / det F G)*F.1+(det F E / det F G)*G.1)+
      v*((det E G / det F G)*F.2+(det F E / det F G)*G.2) := by rw [← hx,← hy]
    _ = _ := by ring

/-- The selected pair controls every linear functional, including
normalizations chosen only after all parent removals. -/
theorem maxdet_witness (F G E : Vec) (h : det F G ≠ 0)
    (hF : |det E G| ≤ |det F G|) (hG : |det F E| ≤ |det F G|) (u v : ℝ) :
    |value u v E| ≤ |value u v F|+|value u v G| := by
  have hd : 0 < |det F G| := abs_pos.mpr h
  have ha : |det E G / det F G| ≤ 1 := by
    rw [abs_div]; exact (div_le_one hd).mpr hF
  have hb : |det F E / det F G| ≤ 1 := by
    rw [abs_div]; exact (div_le_one hd).mpr hG
  rw [functional_cramer F G E h u v]
  calc
    _ ≤ |(det E G / det F G)*value u v F|+
      |(det F E / det F G)*value u v G| := abs_add_le _ _
    _ = |det E G / det F G| *|value u v F|+
      |det F E / det F G| *|value u v G| := by rw [abs_mul,abs_mul]
    _ ≤ 1*|value u v F|+1*|value u v G| :=
      add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
    _ = _ := by ring

theorem maxdet_half_witness (F G E : Vec) (h : det F G ≠ 0)
    (hF : |det E G| ≤ |det F G|) (hG : |det F E| ≤ |det F G|) (u v : ℝ) :
    |value u v E|/2 ≤ max |value u v F| |value u v G| := by
  have hh := maxdet_witness F G E h hF hG u v
  have hf := le_max_left |value u v F| |value u v G|
  have hg := le_max_right |value u v F| |value u v G|
  linarith

/-- In rank one, a maximal positive first coordinate gives one witness. -/
theorem rank_one_witness (F E : Vec) (hF : 0 < F.1)
    (hE : 0 ≤ E.1) (hle : E.1 ≤ F.1) (hdet : det F E = 0) (u v : ℝ) :
    |value u v E| ≤ |value u v F| := by
  have hy : E.2 = (E.1/F.1)*F.2 := by
    unfold det at hdet
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hF.ne').mpr
    nlinarith
  have hx : E.1 = (E.1/F.1)*F.1 := by field_simp
  have he : value u v E = (E.1/F.1)*value u v F := by
    unfold value
    calc
      u*E.1+v*E.2 = u*((E.1/F.1)*F.1)+v*((E.1/F.1)*F.2) := by rw [← hx,← hy]
      _ = _ := by ring
  rw [he,abs_mul,abs_of_nonneg (div_nonneg hE hF.le)]
  exact (mul_le_mul_of_nonneg_right ((div_le_one hF).mpr hle) (abs_nonneg _)).trans_eq (one_mul _)

end EnvyFreeResearch.Full.RefinedUpperDeterminant
