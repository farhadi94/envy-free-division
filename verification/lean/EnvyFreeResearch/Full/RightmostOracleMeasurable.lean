import EnvyFreeResearch.Full.RightmostOracle

/-! Borel measurability of the actual fixed greatest-root oracle. -/

namespace EnvyFreeResearch.Full.RightmostOracle
open Set MeasureTheory IntervalOracle ProtocolMeasurable MixedViews PhysicalReflection

variable {Agent : Type*} [Fintype Agent] [MeasurableSpace Agent]
  [MeasurableSingletonClass Agent]

theorem mirrorQuery_measurable (P : Profile Agent) : Measurable (mirrorQuery P) := by
  apply measurable_query_cases
  · apply measurable_from_prod_countable_right
    intro i
    exact measurable_query_eval.comp
      (measurable_const.prodMk ((measurable_const.sub measurable_snd).prodMk
        (measurable_const.sub measurable_fst)))
  · apply measurable_from_prod_countable_right
    intro i
    have ha : Measurable (fun p : ℝ × ℝ × ℝ => 1-p.1) :=
      measurable_const.sub measurable_fst
    have hb : Measurable (fun p : ℝ × ℝ × ℝ => 1-p.2.1) :=
      measurable_const.sub (measurable_fst.comp measurable_snd)
    have ht : Measurable (fun p : ℝ × ℝ × ℝ =>
        P.cumulative i (1-p.1) - P.cumulative i (1-p.2.1) - p.2.2) :=
      (((P.continuous i).measurable.comp ha).sub
        ((P.continuous i).measurable.comp hb)).sub (measurable_snd.comp measurable_snd)
    exact measurable_query_cut.comp (measurable_const.prodMk (hb.prodMk (ha.prodMk ht)))

theorem actual_oracle_measurable (P : Profile Agent) : Measurable (oracle P) := by
  have hraw := (MixedViews.actual_oracle_measurable P).comp (mirrorQuery_measurable P)
  apply measurable_query_cases
  · have h := hraw.comp measurable_query_eval
    simpa only [oracle, mirrorReply, Option.map_id, Function.comp_def, id_eq] using h
  · have h := hraw.comp measurable_query_cut
    have hm := measurable_option_cases (present := fun _ (r : ℝ) => some (1-r))
      (absent := fun _ => (none : Option ℝ)) h
      (measurable_some.comp (measurable_const.sub measurable_snd)) measurable_const
    convert hm using 1
    funext p
    simp only [oracle, mirrorReply, Function.comp_apply]
    cases IntervalOracle.oracle P (mirrorQuery P (.cut p.1 p.2.1 p.2.2.1 p.2.2.2)) <;> rfl

end EnvyFreeResearch.Full.RightmostOracle
