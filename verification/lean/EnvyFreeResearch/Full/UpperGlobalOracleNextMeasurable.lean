import EnvyFreeResearch.Full.UpperGlobalOracleNext

/-! The countable search is Borel on every tape and every finite history,
without conditioning on legality, successful execution, or eventual return. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalRun.OracleNext
open UpperGlobalPhysical UpperGlobalTape UpperCircularStage UpperQueryPrograms OracleProtocol
variable {n : ℕ}

theorem next_measurable (fallback : Fin n) (chores : Bool) :
    Measurable (Function.uncurry (next fallback chores)) := by
  classical
  let P : (Stream (Universal n) × UpperCircularStage.History n) → ℕ → Prop :=
    fun z t => observable (prefixAction fallback chores z.1 z.2 t) = true
  have hp : ∀ t, MeasurableSet {z | P z t} := fun t =>
    measurableSet_eq_fun (observable_measurable.comp (prefixAction_measurable fallback chores t)) measurable_const
  have he : MeasurableSet {z | ∃ t, P z t} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion hp
  let R : (Stream (Universal n) × UpperCircularStage.History n) → ℕ → Prop :=
    fun z t => P z t ∨ ¬ ∃ s, P z s
  have hr : ∀ z, ∃ t, R z t := by
    intro z
    by_cases h : ∃ t, P z t
    · obtain ⟨t,ht⟩ := h
      exact ⟨t,Or.inl ht⟩
    · exact ⟨0,Or.inr h⟩
  have hmr : ∀ t, MeasurableSet {z | R z t} := fun t => (hp t).union he.compl
  have hindex : Measurable (fun z => Nat.find (hr z)) := measurable_find hr hmr
  have hfamily : Measurable (fun z : (Stream (Universal n) × UpperCircularStage.History n) × ℕ =>
      prefixAction fallback chores z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_left (fun t => prefixAction_measurable fallback chores t)
  have hchosen := hfamily.comp (measurable_id.prodMk hindex)
  have hpiece : Measurable (fun z => if ∃ t, P z t then
      prefixAction fallback chores z.1 z.2 (Nat.find (hr z)) else Action.diverge) :=
    hchosen.ite he measurable_const
  convert hpiece using 1
  funext z
  dsimp only [Function.uncurry,Function.comp_def,id_eq]
  by_cases h : ∃ t, P z t
  · rw [ite_eq_left h,next_eq_find fallback chores z.1 z.2 h]
    congr 1
    exact Nat.find_congr' (fun {t} => by
      simp only [R,h,not_true_eq_false,or_false]
      rfl)
  · rw [ite_eq_right h,next_eq_diverge_of_none fallback chores z.1 z.2 h]

end EnvyFreeResearch.Full.UpperGlobalRun.OracleNext
