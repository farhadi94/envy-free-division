import EnvyFreeResearch.Full.UpperDomainDifferenceLists

/-! Measurability of an actual finite state fold on a changing recorded list. -/

noncomputable section

open MeasureTheory
open scoped Classical

namespace EnvyFreeResearch.Full.UpperDomainDifference

open ProtocolMeasurable

variable {X α β : Type*} [MeasurableSpace X] [MeasurableSpace α] [MeasurableSpace β]

def foldPrefix (step : β → α → β) (initial : β) (xs : List α) : ℕ → β
  | 0 => initial
  | n + 1 => match xs[n]? with
    | none => foldPrefix step initial xs n
    | some a => step (foldPrefix step initial xs n) a

theorem foldPrefix_eq_take (step : β → α → β) (initial : β) (xs : List α) (n : ℕ) :
    foldPrefix step initial xs n = (xs.take n).foldl step initial := by
  induction n with
  | zero => simp [foldPrefix]
  | succ n ih =>
    rw [foldPrefix, ih, List.take_add_one, List.foldl_append]
    cases xs[n]? <;> simp

theorem foldPrefix_measurable (step : X → β → α → β) (initial : X → β) (xs : X → List α)
    (hstep : Measurable (fun p : X × β × α => step p.1 p.2.1 p.2.2))
    (hinitial : Measurable initial) (hxs : Measurable xs) (n : ℕ) :
    Measurable (fun z => foldPrefix (step z) (initial z) (xs z) n) := by
  induction n with
  | zero => exact hinitial
  | succ n ih =>
    have hsome : Measurable (fun p : X × α => step p.1
        (foldPrefix (step p.1) (initial p.1) (xs p.1) n) p.2) :=
      hstep.comp (measurable_fst.prodMk ((ih.comp measurable_fst).prodMk measurable_snd))
    have h := measurable_option_cases
      (present := fun z a => step z (foldPrefix (step z) (initial z) (xs z) n) a)
      (absent := fun z => foldPrefix (step z) (initial z) (xs z) n)
      ((measurable_list_getElem n).comp hxs) hsome ih
    convert h using 1
    funext z
    dsimp only [Function.comp_def, foldPrefix]
    cases (xs z)[n]? <;> rfl

theorem list_foldl_measurable (step : X → β → α → β) (initial : X → β) (xs : X → List α)
    (hstep : Measurable (fun p : X × β × α => step p.1 p.2.1 p.2.2))
    (hinitial : Measurable initial) (hxs : Measurable xs) :
    Measurable (fun z => (xs z).foldl (step z) (initial z)) := by
  have hj : Measurable (fun p : X × ℕ => foldPrefix (step p.1) (initial p.1) (xs p.1) p.2) :=
    measurable_from_prod_countable_left
      (fun n => foldPrefix_measurable step initial xs hstep hinitial hxs n)
  convert hj.comp (measurable_id.prodMk (measurable_list_length.comp hxs)) using 1
  funext z
  simp [foldPrefix_eq_take]

end EnvyFreeResearch.Full.UpperDomainDifference
