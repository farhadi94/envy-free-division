import EnvyFreeResearch.Full.RefinedUpperDeterminant
import EnvyFreeResearch.Full.UpperRepresentatives
import Mathlib.Order.Prod.Lex.Basic

/-! A concrete maximum-determinant selector, including degeneracies and a
stable deterministic tie rule. Pairs include repeated cells. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperWitnessSelector
open MeasureTheory Set RefinedUpperDeterminant
open scoped Classical

/-- Deleting unchosen alternatives preserves the first maximizing choice. -/
theorem argmax_filter {Cell Key : Type*} [LinearOrder Key]
    (score : Cell → Key) (keep : Cell → Bool) (cells : List Cell) (chosen : Cell)
    (hc : cells.argmax score = some chosen) (hk : keep chosen = true) :
    (cells.filter keep).argmax score = some chosen := by
  induction cells with
  | nil => simp at hc
  | cons c cells ih =>
    cases ht : cells.argmax score with
    | none =>
      have he : cells = [] := List.argmax_eq_none.mp ht
      subst cells
      simp only [List.argmax_cons, List.argmax_nil] at hc
      cases hc
      simp [hk]
    | some t =>
      by_cases hct : score c < score t
      · have he : chosen = t := by simpa [List.argmax_cons,ht,hct] using hc.symm
        subst chosen
        have hi := ih ht
        by_cases hh : keep c = true
        · simp [hh,List.argmax_cons,hi,hct]
        · simp [hh,hi]
      · have he : chosen = c := by simpa [List.argmax_cons,ht,hct] using hc.symm
        subst chosen
        rw [List.filter_cons_of_pos hk,List.argmax_cons]
        cases hf : (cells.filter keep).argmax score with
        | none => rfl
        | some z =>
          have hzmemfilter : z ∈ cells.filter keep := List.argmax_mem (f := score) (by simp [hf])
          have hzmem : z ∈ cells := List.mem_of_mem_filter hzmemfilter
          have hzt : score z ≤ score t := List.le_of_mem_argmax hzmem (by simp [ht])
          have hzc : ¬ score c < score z := not_lt.mpr (hzt.trans (le_of_not_gt hct))
          simp [hzc]

def mass (x : Vec) : ℝ := x.1+x.2

def score {Cell : Type*} (x : Cell → Vec) (p : Cell × Cell) : ℝ ×ₗ ℝ :=
  toLex (|det (x p.1) (x p.2)|,mass (x p.1)+mass (x p.2))

def select {Cell : Type*} (x : Cell → Vec) (cells : List Cell) : Option (Cell × Cell) :=
  (cells ×ˢ cells).argmax (score x)

theorem rank_one_mass_witness (F E : Vec)
    (hF : 0 ≤ F.1 ∧ 0 ≤ F.2) (hE : 0 ≤ E.1 ∧ 0 ≤ E.2)
    (hm : mass E ≤ mass F) (hd : det F E = 0) (u v : ℝ) :
    |value u v E| ≤ |value u v F| := by
  have hmass : 0 ≤ mass F := add_nonneg hF.1 hF.2
  by_cases hz : mass F = 0
  · have hzero : F.1=0 ∧ F.2=0 ∧ E.1=0 ∧ E.2=0 := by
      dsimp [mass] at hz hm
      constructor
      · linarith [hF.2]
      constructor
      · linarith [hF.1]
      constructor <;> linarith [hE.1,hE.2]
    simp [value,hzero.1,hzero.2.1,hzero.2.2.1,hzero.2.2.2]
  · have hp : 0 < mass F := lt_of_le_of_ne hmass (Ne.symm hz)
    have hratio0 : 0 ≤ mass E / mass F := div_nonneg (add_nonneg hE.1 hE.2) hmass
    have hratio1 : mass E / mass F ≤ 1 := (div_le_one hp).mpr hm
    have hcoord : E.1=(mass E/mass F)*F.1 ∧ E.2=(mass E/mass F)*F.2 := by
      unfold det at hd
      constructor
      all_goals
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hz).mpr
        unfold mass
        nlinarith
    have he : value u v E = (mass E/mass F)*value u v F := by
      unfold value
      calc
        u*E.1+v*E.2 = u*((mass E/mass F)*F.1)+v*((mass E/mass F)*F.2) := by rw [← hcoord.1,← hcoord.2]
        _ = _ := by ring
    rw [he,abs_mul,abs_of_nonneg hratio0]
    exact (mul_le_mul_of_nonneg_right hratio1 (abs_nonneg _)).trans_eq (one_mul _)

theorem select_spec {Cell : Type*} (x : Cell → Vec) (cells : List Cell)
    (hne : cells ≠ []) (hnonneg : ∀ c ∈ cells, 0 ≤ (x c).1 ∧ 0 ≤ (x c).2) :
    ∃ F G, select x cells = some (F,G) ∧ F ∈ cells ∧ G ∈ cells ∧
      (∀ E H, E ∈ cells → H ∈ cells → |det (x E) (x H)| ≤ |det (x F) (x G)|) ∧
      ∀ E ∈ cells, ∀ u v, |value u v (x E)| ≤ |value u v (x F)|+|value u v (x G)| := by
  have hp : (cells ×ˢ cells) ≠ [] := by
    obtain ⟨c,hc⟩ := List.exists_mem_of_ne_nil cells hne
    intro he
    have : (c,c) ∈ (cells ×ˢ cells) := List.mem_product.mpr ⟨hc,hc⟩
    simp [he] at this
  obtain ⟨p,hp⟩ : ∃ p, (cells ×ˢ cells).argmax (score x) = some p := by
    cases h : (cells ×ˢ cells).argmax (score x) with
    | none => exact False.elim (hp (List.argmax_eq_none.mp h))
    | some p => exact ⟨p,rfl⟩
  have hmem : p.1 ∈ cells ∧ p.2 ∈ cells :=
    List.mem_product.mp (List.argmax_mem (f := score x) (by simp [hp]))
  have hmax (E H : Cell) (hE : E ∈ cells) (hH : H ∈ cells) :
      score x (E,H) ≤ score x p := List.le_of_mem_argmax
        (List.mem_product.mpr ⟨hE,hH⟩) (by simp [hp])
  have hdet (E H : Cell) (hE : E ∈ cells) (hH : H ∈ cells) :
      |det (x E) (x H)| ≤ |det (x p.1) (x p.2)| :=
    Prod.Lex.monotone_fst _ _ (hmax E H hE hH)
  refine ⟨p.1,p.2,hp,hmem.1,hmem.2,hdet,?_⟩
  intro E hE u v
  by_cases hd : det (x p.1) (x p.2) = 0
  · have hall (F G : Cell) (hF : F ∈ cells) (hG : G ∈ cells) : det (x F) (x G) = 0 := by
      have hh := hdet F G hF hG
      rw [hd,abs_zero] at hh
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    have hmass (F : Cell) (hF : F ∈ cells) : 2*mass (x F) ≤ mass (x p.1)+mass (x p.2) := by
      have hh := hmax F F hF hF
      simp only [score,hall F F hF hF,hd,abs_zero,Prod.Lex.toLex_le_toLex,lt_self_iff_false,
        true_and,false_or] at hh
      linarith
    have he : mass (x E) ≤ mass (x p.1) := by
      linarith [hmass E hE,hmass p.1 hmem.1,hmass p.2 hmem.2]
    have hw := rank_one_mass_witness (x p.1) (x E) (hnonneg _ hmem.1) (hnonneg _ hE)
      he (hall _ _ hmem.1 hE) u v
    linarith [abs_nonneg (value u v (x p.2))]
  · exact maxdet_witness _ _ _ hd (hdet E p.2 hE hmem.2) (hdet p.1 E hmem.1 hE) u v

end EnvyFreeResearch.Full.RefinedUpperWitnessSelector
