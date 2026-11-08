import Mathlib

/-! Literal product-space projections used to put every original-trial
failure event on the same label/sampler/isolation/correction probability law. -/

noncomputable section

open MeasureTheory

namespace EnvyFreeResearch.Full.UpperProductViews

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

theorem isolation_view (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c] [IsProbabilityMeasure d] :
    MeasurePreserving (fun p : A × ((B × C) × D) => ((p.2.1.1, p.1), p.2.1.2))
      (a.prod ((b.prod c).prod d)) ((b.prod a).prod c) := by
  have hdrop : MeasurePreserving (fun p : A × ((B × C) × D) => (p.1, p.2.1))
      (a.prod ((b.prod c).prod d)) (a.prod (b.prod c)) :=
    (MeasurePreserving.id a).prod measurePreserving_fst
  have hgroup : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : A × (B × C) ≃ᵐ (A × B) × C)
      (a.prod (b.prod c)) ((a.prod b).prod c) :=
    MeasurePreserving.symm _ (measurePreserving_prodAssoc a b c)
  have hswap : MeasurePreserving (fun p : (A × B) × C => (p.1.swap, p.2))
      ((a.prod b).prod c) ((b.prod a).prod c) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id c)
  exact hswap.comp (hgroup.comp hdrop)

theorem preparation_view (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c] [IsProbabilityMeasure d] :
    MeasurePreserving (fun p : A × ((B × C) × D) => (p.2.1.1, p.1))
      (a.prod ((b.prod c).prod d)) (b.prod a) :=
  measurePreserving_fst.comp (isolation_view a b c d)

end EnvyFreeResearch.Full.UpperProductViews
