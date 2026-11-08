import EnvyFreeResearch.Full.UpperSnapshotRepetitionProbability

/-! Joint event measurability for history-adapted finite repetition. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition

theorem failed_joint_measurable {State Draw : Type}
    [MeasurableSpace State] [MeasurableSpace Draw]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next))
    (hr : Measurable (Function.uncurry reject)) (m : ℕ) :
    MeasurableSet {p : State × Tape Draw m | failed next reject m p.1 p.2} := by
  induction m with
  | zero => simp only [failed,Set.setOf_true]; exact MeasurableSet.univ
  | succ m ih =>
    have hsd : Measurable (fun p : State × (Draw × Tape Draw m) => (p.1,p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hnext : Measurable (fun p : State × (Draw × Tape Draw m) =>
        (next p.1 p.2.1,p.2.2)) :=
      (hn.comp hsd).prodMk (measurable_snd.comp measurable_snd)
    exact (measurableSet_eq_fun (hr.comp hsd) measurable_const).inter (ih.preimage hnext)

theorem failure_geometric_measurable {State Draw : Type}
    [MeasurableSpace State] [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next))
    (hr : Measurable (Function.uncurry reject))
    (b : ℝ≥0∞) (hchance : ∀ s, rho {d | reject s d=true} ≤ b)
    (m : ℕ) (s : State) : law rho m {t | failed next reject m s t} ≤ b^m := by
  apply failure_geometric rho next reject b
  · intro j state
    exact (failed_joint_measurable next reject hn hr j).preimage
      (measurable_const.prodMk measurable_id)
  · intro state
    exact measurableSet_eq_fun hr.of_uncurry_left measurable_const
  · exact hchance

end EnvyFreeResearch.Full.UpperSnapshotRepetition
