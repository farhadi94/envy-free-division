import EnvyFreeResearch.Full.ProtocolMeasurable

/-! Measurable finite-list operations on the shared length/padded-coordinate encoding. -/

noncomputable section

open MeasureTheory
open scoped Classical

namespace EnvyFreeResearch.Full.UpperDomainDifference

open ProtocolMeasurable

variable {X α β : Type*} [MeasurableSpace X] [MeasurableSpace α] [MeasurableSpace β]

def flatMapPrefix (f : α → List β) (xs : List α) : ℕ → List β
  | 0 => []
  | n + 1 => flatMapPrefix f xs n ++ match xs[n]? with
      | none => []
      | some a => f a

theorem flatMapPrefix_eq_take (f : α → List β) (xs : List α) (n : ℕ) :
    flatMapPrefix f xs n = (xs.take n).flatMap f := by
  induction n with
  | zero => simp [flatMapPrefix]
  | succ n ih =>
    rw [flatMapPrefix, ih, List.take_add_one, List.flatMap_append]
    cases h : xs[n]? <;> simp

theorem flatMapPrefix_measurable (f : X → α → List β) (xs : X → List α)
    (hf : Measurable (fun p : X × α => f p.1 p.2)) (hxs : Measurable xs) (n : ℕ) :
    Measurable (fun z => flatMapPrefix (f z) (xs z) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hpiece : Measurable (fun z => match (xs z)[n]? with | none => [] | some a => f z a) := by
      have h := measurable_option_cases (present := f) (absent := fun _ : X => ([] : List β))
        ((measurable_list_getElem n).comp hxs) hf measurable_const
      convert h using 1
      funext z
      dsimp only [Function.comp_def]
      cases (xs z)[n]? <;> rfl
    exact measurable_list_append.comp (ih.prodMk hpiece)

/-- A variable finite input list is handled through its measurable length
and finitely many observable padded coordinates. -/
theorem list_flatMap_measurable (f : X → α → List β) (xs : X → List α)
    (hf : Measurable (fun p : X × α => f p.1 p.2)) (hxs : Measurable xs) :
    Measurable (fun z => (xs z).flatMap (f z)) := by
  have hj : Measurable (fun p : X × ℕ => flatMapPrefix (f p.1) (xs p.1) p.2) :=
    measurable_from_prod_countable_left (fun n => flatMapPrefix_measurable f xs hf hxs n)
  convert hj.comp (measurable_id.prodMk (measurable_list_length.comp hxs)) using 1
  funext z
  simp [Function.comp_def, flatMapPrefix_eq_take]

theorem list_filter_measurable (keep : X → α → Bool) (xs : X → List α)
    (hkeep : Measurable (fun p : X × α => keep p.1 p.2)) (hxs : Measurable xs) :
    Measurable (fun z => (xs z).filter (keep z)) := by
  have hf : Measurable (fun p : X × α => if keep p.1 p.2 then [p.2] else []) :=
    (measurable_list_singleton.comp measurable_snd).ite
      (measurableSet_eq_fun hkeep measurable_const) measurable_const
  have h := list_flatMap_measurable (fun z a => if keep z a then [a] else []) xs hf hxs
  convert h using 1
  funext z
  induction xs z with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : keep z a = true <;> simp [ha, ih]

theorem list_map_measurable (f : X → α → β) (xs : X → List α)
    (hf : Measurable (fun p : X × α => f p.1 p.2)) (hxs : Measurable xs) :
    Measurable (fun z => (xs z).map (f z)) := by
  have h := list_flatMap_measurable (fun z a => [f z a]) xs
    (measurable_list_singleton.comp hf) hxs
  convert h using 1
  funext z
  induction xs z with
  | nil => rfl
  | cons a rest ih => simp [ih]

end EnvyFreeResearch.Full.UpperDomainDifference
