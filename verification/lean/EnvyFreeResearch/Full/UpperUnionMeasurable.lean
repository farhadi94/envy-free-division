import EnvyFreeResearch.Full.UpperUnionSampling
import EnvyFreeResearch.Full.UpperStageMeasurable

/-! Measurability of the actual cached scan and ordinary-query realization on
a general recorded finite union. The finite scan is proved measurable by its
comparisons, rather than assigned a discrete space of physical components. -/

noncomputable section

open MeasureTheory Set
open scoped unitInterval

namespace EnvyFreeResearch.Full.UpperUnionMeasurable

open ProtocolMeasurable UpperCircularStage UpperRecordedDomain UpperStageMeasurable
  UpperUnionSampling Chores

variable {n : ℕ} {X : Type*} [MeasurableSpace X]

theorem componentQuery_measurable (cutter : Fin n) (cell : Component) :
    Measurable (componentQuery cutter cell) :=
  measurable_query_cut.comp (measurable_const.prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

theorem executeRoute_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (hhistory : Measurable history) (cutter : Fin n)
    (cached : Component → ℝ) (target : X → ℝ) (htarget : Measurable target)
    (r : Route Component) :
    Measurable (fun x => executeRoute policy (history x) cutter cached (target x) r) := by
  classical
  have hquery : Measurable (fun x =>
      componentQuery cutter r.cell (target x - sumValues cached r.before)) :=
    (componentQuery_measurable cutter r.cell).comp (htarget.sub_const _)
  have hroot : Measurable (fun x => policy (history x)
      (componentQuery cutter r.cell (target x - sumValues cached r.before))) :=
    hpolicy.comp (hhistory.prodMk hquery)
  have hrecord : Measurable (fun x => executeQueries policy
      (recordings n (policy (history x)
        (componentQuery cutter r.cell (target x - sumValues cached r.before))))
      (history x ++ [(componentQuery cutter r.cell (target x - sumValues cached r.before),
        policy (history x) (componentQuery cutter r.cell (target x - sumValues cached r.before)))])) := by
    apply executeQueries_ofFn_measurable
    · exact hpolicy
    · intro i
      exact measurable_query_eval.comp
        (measurable_const.prodMk (measurable_const.prodMk hroot))
    · exact measurable_list_append.comp (hhistory.prodMk
        (measurable_list_singleton.comp (hquery.prodMk hroot)))
  have htest : MeasurableSet {x | target x - sumValues cached r.before = cached r.cell} :=
    measurableSet_eq_fun (htarget.sub_const _) measurable_const
  exact (measurable_const.prodMk hhistory).ite htest (hroot.prodMk hrecord)

/-- During the cached scan, already skipped cells are accumulated in `before`.
This proves the actual route selection measurable without a route measurability
assumption or an abstract selection kernel. -/
theorem scan_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (hhistory : Measurable history) (cutter : Fin n)
    (cached : Component → ℝ) (target search : X → ℝ)
    (htarget : Measurable target) (hsearch : Measurable search)
    (cells before : List Component) :
    Measurable (fun x => (locate cached (search x) cells).map (fun r =>
      executeRoute policy (history x) cutter cached (target x)
        ⟨before ++ r.before, r.cell, r.after⟩)) := by
  classical
  induction cells generalizing before search with
  | nil => exact measurable_const
  | cons cell cells ih =>
    have hhit := measurable_some.comp
      (executeRoute_measurable policy hpolicy history hhistory cutter cached target htarget
        ⟨before, cell, cells⟩)
    have hskip := ih (fun x => search x - cached cell) (hsearch.sub_const _) (before ++ [cell])
    have htest : MeasurableSet {x | search x ≤ cached cell} :=
      measurableSet_le hsearch measurable_const
    have hresult : Measurable (fun x =>
        if search x ≤ cached cell then
          some (executeRoute policy (history x) cutter cached (target x) ⟨before, cell, cells⟩)
        else (locate cached (search x - cached cell) cells).map (fun r =>
          executeRoute policy (history x) cutter cached (target x)
            ⟨(before ++ [cell]) ++ r.before, r.cell, r.after⟩)) :=
      hhit.ite htest hskip
    convert hresult using 1
    funext x
    simp only [locate]
    split_ifs
    · simp
    · cases locate cached (search x - cached cell) cells <;>
        simp [List.append_assoc]

theorem executeDomain_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : X → History n) (hhistory : Measurable history) (cutter : Fin n)
    (cached : Component → ℝ) (target : X → ℝ) (htarget : Measurable target)
    (cells : List Component) :
    Measurable (fun x => executeDomain policy (history x) cutter cached (target x) cells) := by
  have h := scan_measurable policy hpolicy history hhistory cutter cached target target
    htarget htarget cells []
  convert h using 1
  funext x
  unfold executeDomain
  cases locate cached (target x) cells with
  | none => rfl
  | some r => cases r; rfl

theorem sampleExecution_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) (cached : Component → ℝ) (total : ℝ)
    (cells : List Component) :
    Measurable (sampleExecution policy history cutter cached total cells) := by
  have hrun := executeDomain_measurable policy hpolicy (fun _ : I => history) measurable_const
    cutter cached (fun draw : I => (draw : ℝ) * total)
    (measurable_subtype_coe.mul_const total) cells
  have h := measurable_option_cases (present := fun _ result => result)
    (absent := fun _ => (0, history)) hrun measurable_snd measurable_const
  convert h using 1
  funext draw
  unfold sampleExecution
  cases executeDomain policy history cutter cached ((draw : ℝ) * total) cells <;> rfl

theorem sampleExecution_family_measurable (policy : Policy n)
    (hpolicy : MeasurablePolicy policy) (history : X → History n)
    (hhistory : Measurable history) (cutter : Fin n) (cached : Component → ℝ) (total : ℝ)
    (cells : List Component) (draw : X → I) (hdraw : Measurable draw) :
    Measurable (fun x => sampleExecution policy (history x) cutter cached total cells (draw x)) := by
  have hrun := executeDomain_measurable policy hpolicy history hhistory cutter cached
    (fun x => (draw x : ℝ) * total) ((measurable_subtype_coe.comp hdraw).mul_const total) cells
  have h := measurable_option_cases (present := fun _ result => result)
    (absent := fun x => (0, history x)) hrun measurable_snd (measurable_const.prodMk hhistory)
  convert h using 1
  funext x
  unfold sampleExecution
  cases executeDomain policy (history x) cutter cached ((draw x : ℝ) * total) cells <;> rfl

/-- The normalized physical union sampler follows from the full measurable
legal policy and exact recorded masses; no endpoint-map hypothesis remains. -/
theorem measurable_union_sampler (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (cutter : Fin n) (cells : List Component) (hordered : Ordered cells)
    (hdisjoint : DisjointComponents cells) (cached : Component → ℝ)
    (hcache : ∀ cell ∈ cells, cached cell = mass (μ cutter) cell)
    (hpositive : 0 < (μ cutter).real (domain cells))
    (policy : AdaptiveOracle.Policy (Query n) ℝ)
    (hlegal : AdaptiveOracle.IsLegalPolicy (measureProfile μ) policy)
    (hmeas : Measurable (fun p : History n × Query n => policy p.1 p.2))
    (history : History n) :
    (volume : Measure I).map (fun draw =>
      (sampleExecution (AdaptiveOracle.answer policy) history cutter cached
        ((μ cutter).real (domain cells)) cells draw).1) =
      ProbabilityTheory.cond (μ cutter) (domain cells) := by
  apply sampleExecution_law μ (AdaptiveOracle.answer policy)
    (answer_admissible _ policy hlegal) history cutter cached cells hordered hdisjoint hcache hpositive
  exact measurable_fst.comp
    (sampleExecution_measurable _ (answer_measurable policy hmeas) history cutter cached _ cells)

end EnvyFreeResearch.Full.UpperUnionMeasurable
