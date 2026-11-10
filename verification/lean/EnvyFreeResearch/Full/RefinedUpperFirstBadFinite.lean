import EnvyFreeResearch.Full.RefinedUpperFirstBad
import EnvyFreeResearch.Full.UpperAdaptiveProduct

/-! The adaptive retry bounds on the actual finite independent draw vector. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperFirstBadFinite
open UpperSnapshotRepetition RefinedUpperFirstBad
variable {Draw State : Type} [MeasurableSpace Draw] [MeasurableSpace State]

def pack : (m : ℕ) → (Fin m → Draw) → Tape Draw m
  | 0, _ => ()
  | m + 1, t => (t 0, pack m (fun i => t i.succ))

theorem pack_preserves (rho : Measure Draw) [IsProbabilityMeasure rho] (m : ℕ) :
    MeasurePreserving (pack m) (UpperAdaptiveProduct.tapeLaw rho m) (law rho m) := by
  induction m with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [pack, law, Measure.map_const]
  | succ m ih =>
    have h := ((MeasurePreserving.id rho).prod ih).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => rho) 0)
    convert h using 1
    · funext t
      simp only [Function.comp_apply, Prod.map_apply, id_eq, pack,
        MeasurableEquiv.piFinSuccAbove_apply]
      rfl
    · rfl
    · rfl

theorem hit_bound (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (bad again : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next)) (hb : Measurable (Function.uncurry bad))
    (ha : Measurable (Function.uncurry again))
    (Inv : State → Prop) (hnext : ∀ s d, Inv s → again s d = true → Inv (next s d))
    (a b B : ℝ≥0∞)
    (hbad : ∀ s, Inv s → rho {d | bad s d = true} ≤ a)
    (hagain : ∀ s, Inv s → rho {d | again s d = true} ≤ b)
    (hfixed : a + B * b ≤ B)
    (m : ℕ) (s : State) (hs : Inv s) :
    UpperAdaptiveProduct.tapeLaw rho m {t | hit next bad again m s (pack m t)} ≤ B := by
  have he : MeasurableSet {t : Tape Draw m | hit next bad again m s t} :=
    (hit_joint_measurable next bad again hn hb ha m).preimage
      (measurable_const.prodMk measurable_id)
  have heq : UpperAdaptiveProduct.tapeLaw rho m {t | hit next bad again m s (pack m t)} =
      law rho m {t | hit next bad again m s t} := by
    simpa only [Set.preimage_setOf_eq] using
      (pack_preserves rho m).measure_preimage he.nullMeasurableSet
  rw [heq]
  exact hit_le_fixed_point rho next bad again hn hb ha Inv hnext a b B hbad hagain hfixed m s hs

theorem exhaustion_bound (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (again : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next)) (ha : Measurable (Function.uncurry again))
    (Inv : State → Prop) (hnext : ∀ s d, Inv s → again s d = true → Inv (next s d))
    (b : ℝ≥0∞) (hagain : ∀ s, Inv s → rho {d | again s d = true} ≤ b)
    (m : ℕ) (s : State) (hs : Inv s) :
    UpperAdaptiveProduct.tapeLaw rho m {t | failed next again m s (pack m t)} ≤ b ^ m := by
  have he : MeasurableSet {t : Tape Draw m | failed next again m s t} :=
    (failed_joint_measurable next again hn ha m).preimage
      (measurable_const.prodMk measurable_id)
  have heq : UpperAdaptiveProduct.tapeLaw rho m {t | failed next again m s (pack m t)} =
      law rho m {t | failed next again m s t} := by
    simpa only [Set.preimage_setOf_eq] using
      (pack_preserves rho m).measure_preimage he.nullMeasurableSet
  rw [heq]
  exact exhaustion_le rho next again hn ha Inv hnext b hagain m s hs

end EnvyFreeResearch.Full.RefinedUpperFirstBadFinite
