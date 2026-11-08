import EnvyFreeResearch.Full.UpperDynamicRouting

/-!
# Actual adaptive endpoints on varying recorded domains

Every component endpoint, cache lookup, cutter, amount, and preceding history
may vary measurably. The second Cut consumes the full first execution history.
The cache is accessed jointly at actual variable endpoints, rather than treated
as an uncountable discrete object.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperDynamicExecutor

open UpperRecordedDomain UpperDomainDifference ProtocolMeasurable UpperDynamicRouting
  UpperCircularStage UpperStageMeasurable UpperUnionSampling UpperUnionCircular UpperCircular

abbrev Circle := UpperCircular.Circle

variable {n : ℕ} {X : Type*} [MeasurableSpace X]

theorem componentQuery_joint_measurable (cutter : X → Fin n) (cell : X → Component)
    (residual : X → ℝ) (hcutter : Measurable cutter) (hcell : Measurable cell)
    (hresidual : Measurable residual) :
    Measurable (fun z => componentQuery (cutter z) (cell z) (residual z)) :=
  measurable_query_cut.comp (hcutter.prodMk ((component_left_measurable.comp hcell).prodMk
    ((component_right_measurable.comp hcell).prodMk hresidual)))

theorem executeRoute_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (target : X → ℝ) (route : X → Route Component)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htarget : Measurable target) (hroute : Measurable route) :
    Measurable (fun z => executeRoute policy (history z) (cutter z) (cache z) (target z) (route z)) := by
  classical
  have hcell := route_cell_measurable.comp hroute
  have hsum := sumValues_measurable cache hcache (fun z => (route z).before)
    (route_before_measurable.comp hroute)
  have hres := htarget.sub hsum
  have hval : Measurable (fun z => cache z (route z).cell) :=
    hcache.comp (measurable_id.prodMk hcell)
  have hquery := componentQuery_joint_measurable cutter (fun z => (route z).cell) _ hcutter hcell hres
  have hroot : Measurable (fun z => policy (history z)
      (componentQuery (cutter z) (route z).cell (target z - sumValues (cache z) (route z).before))) :=
    hpolicy.comp (hhistory.prodMk hquery)
  have hrecord : Measurable (fun z => executeQueries policy
      (recordings n (policy (history z)
        (componentQuery (cutter z) (route z).cell (target z - sumValues (cache z) (route z).before))))
      (history z ++ [(componentQuery (cutter z) (route z).cell
        (target z - sumValues (cache z) (route z).before), policy (history z)
        (componentQuery (cutter z) (route z).cell (target z - sumValues (cache z) (route z).before)))])) := by
    apply executeQueries_ofFn_measurable
    · exact hpolicy
    · intro i
      exact measurable_query_eval.comp
        (measurable_const.prodMk (measurable_const.prodMk hroot))
    · exact measurable_list_append.comp (hhistory.prodMk
        (measurable_list_singleton.comp (hquery.prodMk hroot)))
  exact ((component_right_measurable.comp hcell).prodMk hhistory).ite
    (measurableSet_eq_fun hres hval) (hroot.prodMk hrecord)

/-- Full joint Borel measurability of the existing ordinary union-Cut
executor, including the branch that reuses a previously recorded boundary. -/
theorem executeDomain_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (target : X → ℝ) (cells : X → List Component)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htarget : Measurable target) (hcells : Measurable cells) :
    Measurable (fun z => executeDomain policy (history z) (cutter z) (cache z) (target z) (cells z)) := by
  have hlocate := locate_measurable cache hcache target cells htarget hcells
  have hrun : Measurable (fun p : X × Route Component =>
      executeRoute policy (history p.1) (cutter p.1) (cache p.1) (target p.1) p.2) :=
    executeRoute_joint_measurable policy hpolicy _ _ _ _ _ (hhistory.comp measurable_fst)
      (hcutter.comp measurable_fst)
      (hcache.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (htarget.comp measurable_fst) measurable_snd
  have h := measurable_option_cases
    (present := fun z r => some (executeRoute policy (history z) (cutter z) (cache z) (target z) r))
    (absent := fun _ : X => (none : Option (ℝ × History n)))
    hlocate (measurable_some.comp hrun) measurable_const
  convert h using 1
  funext z
  unfold executeDomain
  cases locate (cache z) (target z) (cells z) <;> rfl

theorem sampleExecution_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (total : X → ℝ) (cells : X → List Component) (draw : X → I)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htotal : Measurable total) (hcells : Measurable cells) (hdraw : Measurable draw) :
    Measurable (fun z => sampleExecution policy (history z) (cutter z) (cache z) (total z) (cells z) (draw z)) := by
  have hrun := executeDomain_joint_measurable policy hpolicy history cutter cache
    (fun z => (draw z : ℝ) * total z) cells hhistory hcutter hcache
    ((measurable_subtype_coe.comp hdraw).mul htotal) hcells
  have h := measurable_option_cases (present := fun _ result => result)
    (absent := fun z => ((0 : ℝ), history z)) hrun measurable_snd (measurable_const.prodMk hhistory)
  convert h using 1
  funext z
  unfold sampleExecution
  cases executeDomain policy (history z) (cutter z) (cache z) ((draw z : ℝ) * total z) (cells z) <;> rfl

theorem firstRun_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (total : X → ℝ) (cells : X → List Component) (start : X → Circle)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htotal : Measurable total) (hcells : Measurable cells) (hstart : Measurable start) :
    Measurable (fun z => firstRun policy (history z) (cutter z) (cache z) (total z) (cells z) (start z)) :=
  sampleExecution_joint_measurable policy hpolicy history cutter cache total cells _
    hhistory hcutter hcache htotal hcells (measurable_value.comp hstart)

/-- The second endpoint is measurable after composing the first actual
execution and all its intervening observer recordings. -/
theorem secondRun_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (total : X → ℝ) (cells : X → List Component) (amount : X → I) (start : X → Circle)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htotal : Measurable total) (hcells : Measurable cells)
    (hamount : Measurable amount) (hstart : Measurable start) :
    Measurable (fun z => secondRun policy (history z) (cutter z) (cache z) (total z) (cells z)
      (amount z) (start z)) :=
  sampleExecution_joint_measurable policy hpolicy _ cutter cache total cells _
    (measurable_snd.comp (firstRun_joint_measurable policy hpolicy history cutter cache total cells
      start hhistory hcutter hcache htotal hcells hstart)) hcutter hcache htotal hcells
    (measurable_value.comp (hstart.add (measurable_project.comp hamount)))

theorem recordedCorrection_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (total : X → ℝ) (cells : X → List Component) (amount : X → I) (start : X → Circle)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htotal : Measurable total) (hcells : Measurable cells)
    (hamount : Measurable amount) (hstart : Measurable start) :
    Measurable (fun z => recordedCorrection policy (history z) (cutter z) (cache z) (total z)
      (cells z) (amount z) (start z)) := by
  apply measurable_comap_iff.mpr
  exact hamount.prodMk (hstart.prodMk
    ((measurable_fst.comp (firstRun_joint_measurable policy hpolicy history cutter cache total cells
      start hhistory hcutter hcache htotal hcells hstart)).prodMk
    (measurable_fst.comp (secondRun_joint_measurable policy hpolicy history cutter cache total cells
      amount start hhistory hcutter hcache htotal hcells hamount hstart))))

/-- Actual latest-Eval cache access is jointly Borel even when the cutter and
both component endpoints depend on the preceding execution. -/
theorem history_cache_joint_measurable (history : X → History n) (cutter : X → Fin n)
    (hhistory : Measurable history) (hcutter : Measurable cutter) :
    Measurable (fun p : X × Component => cached (historyPrefix (history p.1)) (cutter p.1) p.2) :=
  (historyPrefix_measurable _ _ _ (hhistory.comp measurable_fst) (hcutter.comp measurable_fst)
    (component_right_measurable.comp measurable_snd)).sub
  (historyPrefix_measurable _ _ _ (hhistory.comp measurable_fst) (hcutter.comp measurable_fst)
    (component_left_measurable.comp measurable_snd))

end EnvyFreeResearch.Full.UpperDynamicExecutor
