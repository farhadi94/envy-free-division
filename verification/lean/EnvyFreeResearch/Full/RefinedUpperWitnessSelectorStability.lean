import EnvyFreeResearch.Full.RefinedUpperWitnessSelector

/-! Deletion consistency and Borel measurability of the concrete selector. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperWitnessSelector
open MeasureTheory Set RefinedUpperDeterminant UpperRepresentatives ProtocolMeasurable
open scoped Classical

lemma filter_product {A B : Type*} (keepA : A → Bool) (keepB : B → Bool)
    (as : List A) (bs : List B) :
    (as.filter keepA) ×ˢ (bs.filter keepB) =
      (as ×ˢ bs).filter (fun p => keepA p.1 && keepB p.2) := by
  induction as with
  | nil => simp
  | cons a as ih =>
    by_cases ha : keepA a = true
    · simp [ha,List.product_cons,List.filter_append,List.filter_map,ih,Function.comp_def]
    · simp [ha,List.product_cons,List.filter_append,List.filter_map,ih,Function.comp_def]

theorem select_filter {Cell : Type*} (x : Cell → Vec) (cells : List Cell)
    (keep : Cell → Bool) (F G : Cell) (hsel : select x cells = some (F,G))
    (hF : keep F = true) (hG : keep G = true) :
    select x (cells.filter keep) = some (F,G) := by
  unfold select at *
  rw [filter_product]
  exact argmax_filter (score x) (fun p => keep p.1 && keep p.2)
    (cells ×ˢ cells) (F,G) hsel (by simp [hF,hG])

section Measurability
variable {X Cell : Type*} [MeasurableSpace X]
  [Countable Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]

/-- Lexicographic comparisons are tested explicitly in the finite loop;
no Borel structure for the lexicographic order topology is used. -/
theorem argmax_lex_measurable (cells : List Cell) (first second : X → Cell → ℝ)
    (hfirst : ∀ c, Measurable (fun x => first x c))
    (hsecond : ∀ c, Measurable (fun x => second x c)) :
    Measurable (fun x => cells.argmax (fun c => toLex (first x c,second x c))) := by
  induction cells with
  | nil => exact measurable_const
  | cons cell cells ih =>
    have hf := score_eval_measurable first hfirst
    have hs := score_eval_measurable second hsecond
    have htest : MeasurableSet {p : X × Cell |
        toLex (first p.1 cell,second p.1 cell) < toLex (first p.1 p.2,second p.1 p.2)} := by
      simp only [Prod.Lex.toLex_lt_toLex]
      exact (measurableSet_lt ((hfirst cell).comp measurable_fst) hf).union
        ((measurableSet_eq_fun ((hfirst cell).comp measurable_fst) hf).inter
          (measurableSet_lt ((hsecond cell).comp measurable_fst) hs))
    have hpresent : Measurable (fun p : X × Cell =>
        if toLex (first p.1 cell,second p.1 cell) < toLex (first p.1 p.2,second p.1 p.2)
        then some p.2 else some cell) :=
      (measurable_some.comp measurable_snd).ite htest measurable_const
    have hh := measurable_option_cases
      (present := fun x c => if toLex (first x cell,second x cell) < toLex (first x c,second x c)
        then some c else some cell) (absent := fun _ => some cell)
      ih hpresent measurable_const
    convert hh using 1
    funext x
    rw [List.argmax_cons]
    cases cells.argmax (fun c => toLex (first x c,second x c)) <;> rfl

theorem select_measurable (cells : List Cell) (x : X → Cell → Vec)
    (hx : ∀ c, Measurable (fun z => (x z c).1))
    (hy : ∀ c, Measurable (fun z => (x z c).2)) :
    Measurable (fun z => select (x z) cells) := by
  apply argmax_lex_measurable (cells ×ˢ cells)
  · intro p
    exact ((hx p.1).mul (hy p.2) |>.sub ((hy p.1).mul (hx p.2))).abs
  · intro p
    exact ((hx p.1).add (hy p.1)).add ((hx p.2).add (hy p.2))

end Measurability
end EnvyFreeResearch.Full.RefinedUpperWitnessSelector
