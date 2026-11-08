import EnvyFreeResearch.Full.ProgramMeasurable
import EnvyFreeResearch.Full.UpperQueryPrograms
import EnvyFreeResearch.Full.UpperRecordedGrid

/-! Borel certificates for the actual ordinary Cut/Eval leaf programs.
All pure inputs may vary jointly, including the finite component list and
the entire recorded history. No response policy occurs in the builders. -/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperQueryProgramsMeasurable

open Chores.QueryProgram ProgramMeasurable ProtocolMeasurable
  UpperQueryPrograms UpperCircularStage UpperRecordedDomain UpperUnionSampling
  UpperUnionCircular UpperDomainDifference UpperDynamicRouting UpperDynamicExecutor

variable {n : ℕ}

def queriesFuel : ℕ → History n → List (Query n) → QProgram n (History n)
  | 0, history, _ => .returned history
  | fuel + 1, history, qs =>
    match qs[0]? with
    | none => .returned history
    | some q => .ask q (fun reply => queriesFuel fuel (history ++ [(q, reply)]) qs.tail)

theorem queriesFuel_eq (fuel : ℕ) (history : History n) (qs : List (Query n))
    (h : qs.length ≤ fuel) : queriesFuel fuel history qs = queries history qs := by
  induction fuel generalizing history qs with
  | zero =>
    have : qs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst qs
    rfl
  | succ fuel ih =>
    cases qs with
    | nil => rfl
    | cons q qs =>
      simp only [queriesFuel, List.getElem?_cons_zero, List.tail_cons, queries]
      congr 1
      funext reply
      exact ih _ _ (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using h)

theorem queriesFuel_certified (fuel : ℕ) :
    ∀ {X : Type} [MeasurableSpace X] (history : X → History n) (qs : X → List (Query n)),
      Measurable history → Measurable qs → Certified (fun x => queriesFuel fuel (history x) (qs x)) := by
  induction fuel with
  | zero =>
    intro X _ history qs hhistory hqs
    exact Certified.returned history hhistory
  | succ fuel ih =>
    intro X _ history qs hhistory hqs
    have hhead := (measurable_list_getElem 0).comp hqs
    have hnext : Certified (fun z : (X × Query n) × ℝ =>
        queriesFuel fuel (history z.1.1 ++ [(z.1.2, z.2)]) (qs z.1.1).tail) := by
      apply ih
      · exact measurable_list_append.comp ((hhistory.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_list_singleton.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      · exact measurable_list_tail.comp (hqs.comp (measurable_fst.comp measurable_fst))
    apply (Certified.optionCases _ hhead _ _
      (Certified.ask (fun z : X × Query n => z.2) measurable_snd _ hnext)
      (Certified.returned history hhistory)).congr
    intro x
    simp only [queriesFuel, Function.comp_def]
    cases (qs x)[0]? <;> rfl

theorem queries_certified {X : Type} [MeasurableSpace X]
    (history : X → History n) (qs : X → List (Query n))
    (hhistory : Measurable history) (hqs : Measurable qs) :
    Certified (fun x => queries (history x) (qs x)) := by
  apply (Certified.natCases (fun x => (qs x).length) (measurable_list_length.comp hqs)
    (fun fuel x => queriesFuel fuel (history x) (qs x))
    (fun fuel => queriesFuel_certified fuel history qs hhistory hqs)).congr
  intro x
  exact queriesFuel_eq _ _ _ le_rfl

theorem recordings_measurable : Measurable (recordings n) := by
  apply (UpperRecordedGrid.ofFn_measurable n).comp
  apply Measurable.of_eval
  intro i
  exact measurable_query_eval.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem route_certified {X : Type} [MeasurableSpace X]
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (target : X → ℝ) (routes : X → Route Component)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htarget : Measurable target) (hroutes : Measurable routes) :
    Certified (fun z => route (history z) (cutter z) (cache z) (target z) (routes z)) := by
  let residual : X → ℝ := fun z => target z - sumValues (cache z) (routes z).before
  let query : X → Query n := fun z => componentQuery (cutter z) (routes z).cell (residual z)
  have hcell := route_cell_measurable.comp hroutes
  have hres : Measurable residual := htarget.sub
    (sumValues_measurable cache hcache _ (route_before_measurable.comp hroutes))
  have hval : Measurable (fun z => cache z (routes z).cell) :=
    hcache.comp (measurable_id.prodMk hcell)
  have hquery : Measurable query := componentQuery_joint_measurable cutter _ residual hcutter hcell hres
  have hrecorded : Certified (fun z : X × ℝ =>
      queries (history z.1 ++ [(query z.1, z.2)]) (recordings n z.2)) :=
    queries_certified _ _
      (measurable_list_append.comp ((hhistory.comp measurable_fst).prodMk
        (measurable_list_singleton.comp ((hquery.comp measurable_fst).prodMk measurable_snd))))
      (recordings_measurable.comp measurable_snd)
  have hpaired := hrecorded.bind
    (fun z : (X × ℝ) × History n => Program.returned (z.1.2, z.2))
    (Certified.returned _ ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hcondition := decide_measurable (fun z => residual z = cache z (routes z).cell)
    (measurableSet_eq_fun hres hval)
  apply (Certified.branch _ hcondition _ _
    (Certified.returned _ ((component_right_measurable.comp hcell).prodMk hhistory))
    (Certified.ask query hquery _ hpaired)).congr
  intro z
  simp only [route, decide_eq_true_eq, residual, query, Function.comp_def]

theorem domainCut_certified {X : Type} [MeasurableSpace X]
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (target : X → ℝ) (cells : X → List Component)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htarget : Measurable target) (hcells : Measurable cells) :
    Certified (fun z => domainCut (history z) (cutter z) (cache z) (target z) (cells z)) := by
  have hlocate := locate_measurable cache hcache target cells htarget hcells
  have hroute : Certified (fun z : X × Route Component =>
      route (history z.1) (cutter z.1) (cache z.1) (target z.1) z.2) :=
    route_certified _ _ _ _ _ (hhistory.comp measurable_fst) (hcutter.comp measurable_fst)
      (hcache.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (htarget.comp measurable_fst) measurable_snd
  have hsome := hroute.bind (fun z => Program.returned (some z.2))
    (Certified.returned _ (measurable_some.comp measurable_snd))
  apply (Certified.optionCases _ hlocate _ _ hsome
    (Certified.returned (fun _ : X => (none : Option (ℝ × History n))) measurable_const)).congr
  intro z
  dsimp only [domainCut]
  cases locate (cache z) (target z) (cells z) <;> rfl

theorem sample_certified {X : Type} [MeasurableSpace X]
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (total : X → ℝ) (cells : X → List Component) (draw : X → I)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htotal : Measurable total) (hcells : Measurable cells) (hdraw : Measurable draw) :
    Certified (fun z => sample (history z) (cutter z) (cache z) (total z) (cells z) (draw z)) := by
  have hcut := domainCut_certified history cutter cache (fun z => (draw z : ℝ) * total z) cells
    hhistory hcutter hcache ((measurable_subtype_coe.comp hdraw).mul htotal) hcells
  have h := measurable_option_cases
    (value := fun z : X × Option (ℝ × History n) => z.2)
    (present := fun _ result => result) (absent := fun z => ((0 : ℝ), history z.1))
    measurable_snd measurable_snd (measurable_const.prodMk (hhistory.comp measurable_fst))
  have hget : Measurable (fun z : X × Option (ℝ × History n) => z.2.getD (0, history z.1)) := by
    convert h using 1
    funext z
    cases z.2 <;> rfl
  exact hcut.bind (fun z => Program.returned (z.2.getD (0, history z.1)))
    (Certified.returned _ hget)

end EnvyFreeResearch.Full.UpperQueryProgramsMeasurable
