import EnvyFreeResearch.Full.ProtocolMeasurable

/-!
# Concrete two-cell representative selection

Maxima are computed by `List.argmax`, with the first listed maximizer chosen
on ties. The selection uses only cached finite tables and issues no queries.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace EnvyFreeResearch.Full.UpperRepresentatives

open ProtocolMeasurable

variable {Cell : Type*}

/-- Select by the manuscript's maximum-coordinate/maximum-residual rule.
The zero-row case selects one maximum of the other row, recorded twice. -/
def select (x y : Cell → ℝ) (cells : List Cell) : Option (Cell × Cell) :=
  (cells.argmax x).bind (fun first =>
    if x first = 0 then (cells.argmax y).map (fun last => (last, last))
    else (cells.argmax (fun c => |y c - (y first / x first) * x c|)).map
      (fun last => (first, last)))

theorem bounded_coefficient (a z : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    |a * z| ≤ |z| := by
  rw [abs_mul, abs_of_nonneg ha]
  nlinarith [abs_nonneg z]

/-- Algebraic certificate for the actual two choices made by `select`. -/
theorem two_cell_inequality (x y : Cell → ℝ) (first last c : Cell)
    (hfirst : 0 < x first) (hc : 0 ≤ x c) (hlast : 0 ≤ x last)
    (hcx : x c ≤ x first) (hlastx : x last ≤ x first)
    (hresidual : |y c - (y first / x first) * x c| ≤
      |y last - (y first / x first) * x last|) (u v : ℝ) :
    |u * x c - v * y c| ≤
      3 * max |u * x first - v * y first| |u * x last - v * y last| := by
  let z := fun a => u * x a - v * y a
  let r := fun a => y a - (y first / x first) * x a
  have hratio (a : Cell) (h0 : 0 ≤ x a) (h1 : x a ≤ x first) :
      0 ≤ x a / x first ∧ x a / x first ≤ 1 :=
    ⟨div_nonneg h0 hfirst.le, (div_le_one hfirst).mpr h1⟩
  have hzc : z c = (x c / x first) * z first - v * r c := by
    dsimp [z, r]
    field_simp
    ring
  have hzg : v * r last = (x last / x first) * z first - z last := by
    dsimp [z, r]
    field_simp
    ring
  have hrc : |v * r c| ≤ |v * r last| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hresidual (abs_nonneg v)
  have habs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  have hrg : |v * r last| ≤ |z first| + |z last| := by
    rw [hzg]
    exact (habs _ _).trans (add_le_add
      (bounded_coefficient _ _ (hratio last hlast hlastx).1
        (hratio last hlast hlastx).2) le_rfl)
  change |z c| ≤ 3 * max |z first| |z last|
  calc
    |z c| ≤ |(x c / x first) * z first| + |v * r c| := by
      rw [hzc]
      exact habs _ _
    _ ≤ |z first| + (|z first| + |z last|) :=
      add_le_add (bounded_coefficient _ _ (hratio c hc hcx).1 (hratio c hc hcx).2)
        (hrc.trans hrg)
    _ ≤ 3 * max |z first| |z last| := by
      linarith [le_max_left |z first| |z last|, le_max_right |z first| |z last|]

theorem argmax_exists (score : Cell → ℝ) (cells : List Cell) (hne : cells ≠ []) :
    ∃ c, cells.argmax score = some c := by
  cases h : cells.argmax score with
  | none => exact False.elim (hne (List.argmax_eq_none.mp h))
  | some c => exact ⟨c, rfl⟩

/-- A nonempty cached table produces actual representatives satisfying the
factor-three inequality simultaneously for every later pair of normalizers. -/
theorem select_spec (x y : Cell → ℝ) (cells : List Cell) (hne : cells ≠ [])
    (hx : ∀ c ∈ cells, 0 ≤ x c) (hy : ∀ c ∈ cells, 0 ≤ y c) :
    ∃ first last, select x y cells = some (first, last) ∧ first ∈ cells ∧ last ∈ cells ∧
      ∀ c ∈ cells, ∀ u v : ℝ,
        |u * x c - v * y c| ≤
          3 * max |u * x first - v * y first| |u * x last - v * y last| := by
  obtain ⟨first, hfirst⟩ := argmax_exists x cells hne
  have hfirstmem : first ∈ cells := List.argmax_mem (by simpa [hfirst])
  have hmax : ∀ c ∈ cells, x c ≤ x first :=
    fun c hc => List.le_of_mem_argmax hc (by simp [hfirst])
  by_cases hzero : x first = 0
  · obtain ⟨last, hlast⟩ := argmax_exists y cells hne
    have hlastmem : last ∈ cells := List.argmax_mem (by simpa [hlast])
    have hzeroAll : ∀ c ∈ cells, x c = 0 := by
      intro c hc
      exact le_antisymm (by simpa [hzero] using hmax c hc) (hx c hc)
    refine ⟨last, last, ?_, hlastmem, hlastmem, ?_⟩
    · simp [select, hfirst, hzero, hlast]
    · intro c hc u v
      have hle : y c ≤ y last := List.le_of_mem_argmax hc (by simp [hlast])
      simp only [hzeroAll c hc, hzeroAll last hlastmem, mul_zero, zero_sub,
        abs_neg, abs_mul, abs_of_nonneg (hy c hc), abs_of_nonneg (hy last hlastmem), max_self]
      have hm := mul_le_mul_of_nonneg_left hle (abs_nonneg v)
      nlinarith [mul_nonneg (abs_nonneg v) (hy last hlastmem)]
  · obtain ⟨last, hlast⟩ := argmax_exists (fun c => |y c - (y first / x first) * x c|) cells hne
    have hlastmem : last ∈ cells := List.argmax_mem (by simpa [hlast])
    refine ⟨first, last, ?_, hfirstmem, hlastmem, ?_⟩
    · simp [select, hfirst, hzero, hlast]
    · intro c hc u v
      exact two_cell_inequality x y first last c
        (lt_of_le_of_ne (hx first hfirstmem) (Ne.symm hzero)) (hx c hc) (hx last hlastmem)
        (hmax c hc) (hmax last hlastmem)
        (List.le_of_mem_argmax (f := fun c => |y c - (y first / x first) * x c|)
          hc (by simp [hlast])) u v

/-- After reserve normalization, keep the member of the selected pair with
largest absolute signed difference, with the first one chosen on a tie. -/
def witness (difference : Cell → ℝ) (pair : Cell × Cell) : Cell :=
  if |difference pair.1| < |difference pair.2| then pair.2 else pair.1

theorem witness_mem (difference : Cell → ℝ) (pair : Cell × Cell) :
    witness difference pair = pair.1 ∨ witness difference pair = pair.2 := by
  unfold witness
  split_ifs <;> simp

theorem witness_abs (difference : Cell → ℝ) (pair : Cell × Cell) :
    |difference (witness difference pair)| = max |difference pair.1| |difference pair.2| := by
  unfold witness
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (le_of_not_gt h)).symm

theorem witness_lower_bound (difference : Cell → ℝ) (pair : Cell × Cell) (c : Cell)
    (hbound : |difference c| ≤ 3 * max |difference pair.1| |difference pair.2|) :
    |difference c| / 3 ≤ |difference (witness difference pair)| := by
  rw [witness_abs]
  linarith

section Measurability

variable [Countable Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
  {X : Type*} [MeasurableSpace X]

theorem score_eval_measurable (score : X → Cell → ℝ)
    (hscore : ∀ c, Measurable (fun x => score x c)) :
    Measurable (fun p : X × Cell => score p.1 p.2) :=
  measurable_from_prod_countable_left hscore

/-- The explicit tie rule makes finite maximum selection measurable in every
real entry of the cached score table. -/
theorem argmax_measurable (cells : List Cell) (score : X → Cell → ℝ)
    (hscore : ∀ c, Measurable (fun x => score x c)) :
    Measurable (fun x => cells.argmax (score x)) := by
  classical
  induction cells with
  | nil => exact measurable_const
  | cons cell cells ih =>
    have htest : MeasurableSet {p : X × Cell | score p.1 cell < score p.1 p.2} :=
      measurableSet_lt ((hscore cell).comp measurable_fst) (score_eval_measurable score hscore)
    have hpresent : Measurable (fun p : X × Cell =>
        if score p.1 cell < score p.1 p.2 then some p.2 else some cell) :=
      (measurable_some.comp measurable_snd).ite htest measurable_const
    have h := measurable_option_cases
      (present := fun x c => if score x cell < score x c then some c else some cell)
      (absent := fun _ => some cell) ih hpresent measurable_const
    convert h using 1
    funext x
    rw [List.argmax_cons]
    cases cells.argmax (score x) <;> rfl

theorem option_map_measurable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (value : X → Option Y) (f : X → Y → Z) (hvalue : Measurable value)
    (hf : Measurable (fun p : X × Y => f p.1 p.2)) :
    Measurable (fun x => (value x).map (f x)) := by
  have h := measurable_option_cases (present := fun x y => some (f x y))
    (absent := fun _ => none) hvalue (measurable_some.comp hf) measurable_const
  convert h using 1
  funext x
  cases value x <;> rfl

/-- The full representative selector is Borel in both cached rows, including
the zero-first-row branch and all ties. -/
theorem select_measurable (cells : List Cell) (x y : X → Cell → ℝ)
    (hx : ∀ c, Measurable (fun z => x z c)) (hy : ∀ c, Measurable (fun z => y z c)) :
    Measurable (fun z => select (x z) (y z) cells) := by
  classical
  have hxeval := score_eval_measurable x hx
  have hyeval := score_eval_measurable y hy
  have hzero : Measurable (fun p : X × Cell =>
      (cells.argmax (y p.1)).map (fun c => (c, c))) := by
    apply option_map_measurable
    · exact (argmax_measurable cells y hy).comp measurable_fst
    · exact measurable_snd.prodMk measurable_snd
  have hresidual : Measurable (fun p : X × Cell => cells.argmax
      (fun c => |y p.1 c - (y p.1 p.2 / x p.1 p.2) * x p.1 c|)) := by
    apply argmax_measurable
    intro c
    exact (((hy c).comp measurable_fst).sub
      ((hyeval.div hxeval).mul ((hx c).comp measurable_fst))).abs
  have hnonzero : Measurable (fun p : X × Cell =>
      (cells.argmax (fun c => |y p.1 c - (y p.1 p.2 / x p.1 p.2) * x p.1 c|)).map
        (fun c => (p.2, c))) := by
    apply option_map_measurable
    · exact hresidual
    · exact (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have htest : MeasurableSet {p : X × Cell | x p.1 p.2 = 0} :=
    measurableSet_eq_fun hxeval measurable_const
  have hpresent : Measurable (fun p : X × Cell =>
      if x p.1 p.2 = 0 then (cells.argmax (y p.1)).map (fun c => (c, c)) else
        (cells.argmax (fun c => |y p.1 c - (y p.1 p.2 / x p.1 p.2) * x p.1 c|)).map
          (fun c => (p.2, c))) := hzero.ite htest hnonzero
  have h := measurable_option_cases
    (present := fun z first => if x z first = 0 then
      (cells.argmax (y z)).map (fun c => (c, c)) else
      (cells.argmax (fun c => |y z c - (y z first / x z first) * x z c|)).map
        (fun c => (first, c)))
    (absent := fun _ => none) (argmax_measurable cells x hx) hpresent measurable_const
  convert h using 1
  funext z
  unfold select
  cases cells.argmax (x z) <;> rfl

theorem witness_measurable (difference : X → Cell → ℝ)
    (hdifference : ∀ c, Measurable (fun x => difference x c))
    (pair : X → Cell × Cell) (hpair : Measurable pair) :
    Measurable (fun x => witness (difference x) (pair x)) := by
  classical
  have hfirst := (score_eval_measurable difference hdifference).comp
    (measurable_id.prodMk (measurable_fst.comp hpair))
  have hlast := (score_eval_measurable difference hdifference).comp
    (measurable_id.prodMk (measurable_snd.comp hpair))
  have htest : MeasurableSet {x | |difference x (pair x).1| < |difference x (pair x).2|} :=
    measurableSet_lt hfirst.abs hlast.abs
  exact (measurable_snd.comp hpair).ite htest (measurable_fst.comp hpair)

end Measurability

end EnvyFreeResearch.Full.UpperRepresentatives
