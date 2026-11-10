import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurableCases
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeMeasurableProgram

/-! Program certificates for finite selectors and the six physical phases. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.ProgramCertified
open RefinedUpperGlobalPhysical RefinedUpperGlobalNormalize ProtocolMeasurable ProgramMeasurable Chores.QueryProgram UpperQueryPrograms
variable {n : ℕ} {X A B Output Key : Type}
  [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Output]

theorem finite_select_certified [Fintype Key] [MeasurableSpace Key] [DiscreteMeasurableSpace Key]
    (index : X → Key) (hi : Measurable index) (p : Key → X → QProgram n Output)
    (hp : ∀ i, Certified (p i)) : Certified (fun x => p (index x) x) := by
  let e := Fintype.equivFin Key
  let branches : ℕ → X → QProgram n Output := fun j x =>
    if h : j<Fintype.card Key then p (e.symm ⟨j,h⟩) x else .failed
  have hb : ∀ j, Certified (branches j) := by
    intro j
    by_cases hj : j<Fintype.card Key
    · simpa only [branches,dite_eq_left hj] using hp (e.symm ⟨j,hj⟩)
    · simpa only [branches,dite_eq_right hj] using
        (Certified.failed : Certified (fun _ : X => (Program.failed : QProgram n Output)))
  apply (Certified.natCases (fun x => (e (index x)).val)
    ((measurable_of_countable (fun i => (e i).val)).comp hi) branches hb).congr
  intro x
  simp only [branches,dite_eq_left (e (index x)).isLt]
  exact congrArg (fun i => p i x) (e.symm_apply_apply (index x))

theorem sum_cases_certified (left : X × A → QProgram n Output) (right : X × B → QProgram n Output)
    (hl : Certified left) (hr : Certified right) :
    Certified (fun p : X × (A ⊕ B) => p.2.elim (fun a => left (p.1,a)) (fun b => right (p.1,b))) := by
  let toLeft : A ⊕ B → Option A := Sum.elim some (fun _ => none)
  let toRight : A ⊕ B → Option B := Sum.elim (fun _ => none) some
  have hleft : Measurable toLeft := measurable_some.sumElim measurable_const
  have hright : Measurable toRight := measurable_const.sumElim measurable_some
  have hrf := hr.comp (fun z : (X × (A ⊕ B)) × B => (z.1.1,z.2))
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hrc := Certified.optionCases (fun p : X × (A ⊕ B) => toRight p.2)
    (hright.comp measurable_snd) _ _ hrf (Certified.failed : Certified (fun _ : X × (A ⊕ B) => (Program.failed : QProgram n Output)))
  have hlf := hl.comp (fun z : (X × (A ⊕ B)) × A => (z.1.1,z.2))
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  apply (Certified.optionCases (fun p : X × (A ⊕ B) => toLeft p.2)
    (hleft.comp measurable_snd) _ _ hlf hrc).congr
  intro p
  cases p.2 <;> rfl

variable {Draw : Type} [MeasurableSpace Draw]

theorem phaseCases_certified
    (normalize snapshot done : Anchor n → Draw → QProgram n Output)
    (first : Pending n → ℝ → Draw → QProgram n Output) (second repair : Pending n → Draw → QProgram n Output)
    (hn : Certified (Function.uncurry normalize)) (hs : Certified (Function.uncurry snapshot))
    (hd : Certified (Function.uncurry done))
    (hf : Certified (fun z : (Pending n × ℝ) × Draw => first z.1.1 z.1.2 z.2))
    (hsecond : Certified (Function.uncurry second)) (hr : Certified (Function.uncurry repair)) :
    Certified (Function.uncurry (DispatchMeasurable.phaseCases normalize snapshot done first second repair)) := by
  let left := fun draw : Draw => fun p : Fin 3 × Anchor n =>
    if p.1=0 then normalize p.2 draw else if p.1=1 then snapshot p.2 draw else done p.2 draw
  let right := fun draw : Draw => fun p : Fin 3 × Pending n × ℝ =>
    if p.1=0 then first p.2.1 p.2.2 draw else if p.1=1 then second p.2.1 draw else repair p.2.1 draw
  have hl : Certified (fun z : Draw × (Fin 3 × Anchor n) => left z.1 z.2) := by
    have hm : Measurable (fun z : Draw × (Fin 3 × Anchor n) => (z.2.2,z.1)) :=
      (measurable_snd.comp measurable_snd).prodMk measurable_fst
    have hl := Certified.branch (fun z : Draw × (Fin 3 × Anchor n) => decide (z.2.1=1))
      (UpperDomainDifference.decide_measurable _ (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const))
      _ _ (hs.comp _ hm) (hd.comp _ hm)
    apply (Certified.branch (fun z : Draw × (Fin 3 × Anchor n) => decide (z.2.1=0))
      (UpperDomainDifference.decide_measurable _ (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const))
      _ _ (hn.comp _ hm) hl).congr
    intro z
    simp only [left,decide_eq_true_eq,Function.uncurry]
  have hright : Certified (fun z : Draw × (Fin 3 × Pending n × ℝ) => right z.1 z.2) := by
    have hm : Measurable (fun z : Draw × (Fin 3 × Pending n × ℝ) => (z.2.2.1,z.1)) :=
      (measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk measurable_fst
    have hl := Certified.branch (fun z : Draw × (Fin 3 × Pending n × ℝ) => decide (z.2.1=1))
      (UpperDomainDifference.decide_measurable _ (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const))
      _ _ (hsecond.comp _ hm) (hr.comp _ hm)
    apply (Certified.branch (fun z : Draw × (Fin 3 × Pending n × ℝ) => decide (z.2.1=0))
      (UpperDomainDifference.decide_measurable _ (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const))
      _ _ (hf.comp _ ((measurable_snd.comp measurable_snd).prodMk measurable_fst)) hl).congr
    intro z
    simp only [right,decide_eq_true_eq,Function.uncurry,Function.comp_def]
  have h := (sum_cases_certified _ _ hl hright).comp
    (fun z : Phase n × Draw => (z.2,Phase.code z.1))
    (measurable_snd.prodMk ((comap_measurable Phase.code).comp measurable_fst))
  apply h.congr
  intro z
  rcases z with ⟨phase,draw⟩
  cases phase <;> rfl
end EnvyFreeResearch.Full.RefinedUpperGlobalRun.ProgramCertified
