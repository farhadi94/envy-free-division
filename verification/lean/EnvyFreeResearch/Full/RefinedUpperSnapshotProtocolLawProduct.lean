import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolLaw

/-! The full preparation history and final independent Repair are a genuine
product decomposition of the original Snapshot tape, including coordinates
unused by the realized branch. -/
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
abbrev GridTape (n k : ℕ) := Fin (RefinedUpperRepair.fine n) → Fin k × I
abbrev PreparationTape (n k : ℕ) := GridTape n k × (UpperCircular.Circle × CandidateTape k)
def gridLaw (n k : ℕ) : Measure (GridTape n k) :=
  UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) (RefinedUpperRepair.fine n)
def preparationLaw (n k : ℕ) : Measure (PreparationTape n k) :=
  (gridLaw n k).prod (volume.prod (candidateLaw k))
instance gridLaw_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (gridLaw n k) := by
  unfold gridLaw
  infer_instance
instance preparationLaw_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (preparationLaw n k) := by
  unfold preparationLaw
  infer_instance

def joinTape {n k : ℕ} (p : PreparationTape n k × RefinedUpperRepair.Tape n k) : Tape n k :=
  (p.1.1,(p.1.2.1,(p.1.2.2,p.2)))

theorem joinTape_measurePreserving (n k : ℕ) [Nonempty (Fin k)] :
    MeasurePreserving (joinTape (n:=n) (k:=k)) ((preparationLaw n k).prod (RefinedUpperRepair.law n k)) (law n k) := by
  have houter := measurePreserving_prodAssoc (gridLaw n k)
    ((volume : Measure UpperCircular.Circle).prod (candidateLaw k)) (RefinedUpperRepair.law n k)
  have hinner := (MeasurePreserving.id (gridLaw n k)).prod
    (measurePreserving_prodAssoc (volume : Measure UpperCircular.Circle) (candidateLaw k) (RefinedUpperRepair.law n k))
  exact hinner.comp houter

theorem preparation_zero_projection (n k : ℕ) [Nonempty (Fin k)] :
    MeasurePreserving (fun p : PreparationTape n k => (p.1,p.2.1))
      (preparationLaw n k) ((gridLaw n k).prod (volume : Measure UpperCircular.Circle)) :=
  (MeasurePreserving.id _).prod measurePreserving_fst

theorem preparation_small_projection (n k : ℕ) [Nonempty (Fin k)] :
    MeasurePreserving (fun p : PreparationTape n k => (p.1,p.2.2))
      (preparationLaw n k) ((gridLaw n k).prod (candidateLaw k)) :=
  (MeasurePreserving.id _).prod measurePreserving_snd
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
