import EnvyFreeResearch.Full.ChoresProgram
import EnvyFreeResearch.Full.ProtocolMeasurable

/-! Compositional Borel certificates for actual query-program families.
The certificate records measurable pure computations, queries, joint reply
continuations and countable branching. Its theorem concerns the compiled
next action on every coded history, including histories not reached by an
admissible oracle. -/

noncomputable section

open MeasureTheory
open scoped Classical

namespace EnvyFreeResearch.Full.ProgramMeasurable

open Chores.QueryProgram OracleProtocol ProtocolMeasurable

variable {Query Reply : Type} [MeasurableSpace Query] [MeasurableSpace Reply]

inductive Certified : {X Output : Type} → [MeasurableSpace X] → [MeasurableSpace Output] →
    (X → Program Query Reply Output) → Prop
  | returned {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]
      (value : X → Output) (hvalue : Measurable value) : Certified (fun x => .returned (value x))
  | failed {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output] :
      Certified (fun _ : X => (Program.failed : Program Query Reply Output))
  | ask {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]
      (query : X → Query) (hquery : Measurable query) (next : X × Reply → Program Query Reply Output)
      (hnext : Certified next) : Certified (fun x => .ask (query x) (fun reply => next (x, reply)))
  | branch {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]
      (condition : X → Bool) (hcondition : Measurable condition)
      (yes no : X → Program Query Reply Output) (hyes : Certified yes) (hno : Certified no) :
      Certified (fun x => if condition x then yes x else no x)
  | natCases {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]
      (index : X → ℕ) (hindex : Measurable index) (branches : ℕ → X → Program Query Reply Output)
      (hbranches : ∀ i, Certified (branches i)) : Certified (fun x => branches (index x) x)
  | optionCases {X Value Output : Type} [MeasurableSpace X] [MeasurableSpace Value] [MeasurableSpace Output]
      (value : X → Option Value) (hvalue : Measurable value)
      (present : X × Value → Program Query Reply Output) (absent : X → Program Query Reply Output)
      (hpresent : Certified present) (habsent : Certified absent) :
      Certified (fun x => match value x with | some a => present (x, a) | none => absent x)

theorem Certified.congr {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]
    {p q : X → Program Query Reply Output} (hp : Certified p) (heq : ∀ x, p x = q x) : Certified q := by
  rw [← funext heq]
  exact hp

theorem Certified.comp {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]
    {p : X → Program Query Reply Output} (hp : Certified p) :
    ∀ {Y : Type} [MeasurableSpace Y] (f : Y → X), Measurable f → Certified (fun y => p (f y)) := by
  induction hp with
  | returned value hvalue =>
    intro Y _ f hf
    exact Certified.returned _ (hvalue.comp hf)
  | failed =>
    intro Y _ f hf
    exact Certified.failed
  | ask query hquery next hnext ih =>
    intro Y _ f hf
    exact Certified.ask _ (hquery.comp hf) _
      (ih (fun p : Y × Reply => (f p.1, p.2)) ((hf.comp measurable_fst).prodMk measurable_snd))
  | branch condition hcondition yes no hyes hno ihyes ihno =>
    intro Y _ f hf
    exact Certified.branch _ (hcondition.comp hf) _ _ (ihyes f hf) (ihno f hf)
  | natCases index hindex branches hbranches ih =>
    intro Y _ f hf
    exact Certified.natCases _ (hindex.comp hf) _ (fun i => ih i f hf)
  | @optionCases X Value Output _ _ _ value hvalue present absent hpresent habsent ihpresent ihabsent =>
    intro Y _ f hf
    exact Certified.optionCases _ (hvalue.comp hf) _ _
      (ihpresent (fun p : Y × Value => (f p.1, p.2)) ((hf.comp measurable_fst).prodMk measurable_snd))
      (ihabsent f hf)

/-- Ordinary program composition preserves the certificate, including joint
dependence of the continuation on the original parameter and returned value. -/
theorem Certified.bind {X A B : Type} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    {p : X → Program Query Reply A} (hp : Certified p) :
    ∀ (next : X × A → Program Query Reply B), Certified next →
      Certified (fun x => (p x).bind (fun a => next (x, a))) := by
  induction hp with
  | returned value hvalue =>
    intro next hnext
    exact hnext.comp (fun x => (x, value x)) (measurable_id.prodMk hvalue)
  | failed =>
    intro next hnext
    exact Certified.failed
  | @ask X A _ _ query hquery next hnext ih =>
    intro continuation hc
    have hcont := hc.comp (fun z : (X × Reply) × A => (z.1.1, z.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact Certified.ask query hquery _ (ih _ hcont)
  | branch condition hcondition yes no hyes hno ihyes ihno =>
    intro next hnext
    apply (Certified.branch condition hcondition _ _ (ihyes next hnext) (ihno next hnext)).congr
    intro x
    by_cases h : condition x = true <;> simp only [h, Bool.false_eq_true, ite_true, ite_false]
  | natCases index hindex branches hbranches ih =>
    intro next hnext
    exact Certified.natCases index hindex _ (fun i => ih i next hnext)
  | @optionCases X Value A _ _ _ value hvalue present absent hpresent habsent ihpresent ihabsent =>
    intro next hnext
    have hcont := hnext.comp (fun p : (X × Value) × A => (p.1.1, p.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    apply (Certified.optionCases value hvalue _ _ (ihpresent _ hcont) (ihabsent next hnext)).congr
    intro x
    dsimp only
    cases value x <;> rfl

theorem measurable_list_tail {α : Type} [MeasurableSpace α] : Measurable (List.tail (α := α)) := by
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · simpa only [List.length_tail, Function.comp_def] using
      (measurable_of_countable (fun n : ℕ => n - 1)).comp (measurable_list_length (α := α))
  · apply Measurable.of_eval
    intro i
    simpa only [List.getElem?_tail] using measurable_list_getElem (α := α) (i + 1)

/-- The actual next action of the compiled program is Borel jointly in the
entire private parameter and every finite real-valued answered history. -/
theorem Certified.measurable_next {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]
    {p : X → Program Query Reply Output} (hp : Certified p) :
    Measurable (fun z : X × History Query Reply => ((p z.1).after z.2).action) := by
  induction hp with
  | returned value hvalue =>
    convert measurable_action_returned.comp (hvalue.comp measurable_fst) using 1
    funext z
    cases z.2 <;> rfl
  | failed =>
    convert (measurable_const : Measurable (fun _ => (Action.diverge : Action Query _))) using 1
    funext z
    cases z.2 <;> rfl
  | @ask X Output _ _ query hquery next hnext ih =>
    have hhead : Measurable (fun z : X × History Query Reply => z.2[0]?) :=
      (measurable_list_getElem 0).comp measurable_snd
    have hpresent : Measurable (fun z : (X × History Query Reply) × (Query × Reply) =>
        ((next (z.1.1, z.2.2)).after z.1.2.tail).action) :=
      ih.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd) |>.prodMk
        (measurable_list_tail.comp (measurable_snd.comp measurable_fst)))
    have habsent : Measurable (fun z : X × History Query Reply =>
        (Action.ask (query z.1) : Action Query Output)) :=
      measurable_action_ask.comp (hquery.comp measurable_fst)
    have h := measurable_option_cases (present := fun z entry => ((next (z.1, entry.2)).after z.2.tail).action)
      (absent := fun z => Action.ask (query z.1)) hhead hpresent habsent
    convert h using 1
    funext z
    cases z.2 <;> rfl
  | @branch X Output _ _ condition hcondition yes no hyes hno ihyes ihno =>
    have h : Measurable (fun z : X × History Query Reply =>
        if condition z.1 then ((yes z.1).after z.2).action else ((no z.1).after z.2).action) :=
      ihyes.ite (measurableSet_eq_fun (hcondition.comp measurable_fst) (measurable_const (a := true))) ihno
    convert h using 1
    funext z
    by_cases hc : condition z.1 = true <;> simp only [hc, Bool.false_eq_true, ite_true, ite_false]
  | @natCases X Output _ _ index hindex branches hbranches ih =>
    have h : Measurable (fun z : (X × History Query Reply) × ℕ =>
        ((branches z.2 z.1.1).after z.1.2).action) :=
      measurable_from_prod_countable_left (fun i => ih i)
    exact h.comp (measurable_id.prodMk (hindex.comp measurable_fst))
  | @optionCases X Value Output _ _ _ value hvalue present absent hpresent habsent ihpresent ihabsent =>
    have hsome : Measurable (fun p : (X × History Query Reply) × Value =>
        ((present (p.1.1, p.2)).after p.1.2).action) :=
      ihpresent.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))
    have h := measurable_option_cases (present := fun z a => ((present (z.1, a)).after z.2).action)
      (absent := fun z => ((absent z.1).after z.2).action) (hvalue.comp measurable_fst) hsome ihabsent
    convert h using 1
    funext z
    dsimp only [Function.comp_def]
    cases value z.1 <;> rfl

end EnvyFreeResearch.Full.ProgramMeasurable
