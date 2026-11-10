import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolDispatch
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurableCases

/-! Fixed active-set projections of the actual universal fresh draw. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
open MeasureTheory RefinedUpperGlobalPhysical RefinedUpperGlobalTape
variable {n : ℕ}

def requestAt (active : Finset (Fin n)) (hk : 2 ≤ active.card) (kind : Kind) : Request n :=
  (⟨⟨active.card,by have := UpperZeroRows.active_size_bound active; omega⟩,hk⟩,kind)

def snapshotTape (active : Finset (Fin n)) (hk : 2 ≤ active.card) (draw : Universal n) :
    RefinedUpperSnapshotProtocol.Tape n active.card := draw (requestAt active hk .snapshot)
def shrinkTape (active : Finset (Fin n)) (hk : 2 ≤ active.card) (draw : Universal n) :
    RefinedUpperRepair.Tape n active.card := draw (requestAt active hk .shrink)
def repairTape (active : Finset (Fin n)) (hk : 2 ≤ active.card) (draw : Universal n) :
    RefinedUpperRepair.Tape n active.card := draw (requestAt active hk .repair)

theorem snapshotTape_measurable (active : Finset (Fin n)) (hk : 2 ≤ active.card) :
    Measurable (snapshotTape active hk) := measurable_pi_apply _
theorem shrinkTape_measurable (active : Finset (Fin n)) (hk : 2 ≤ active.card) :
    Measurable (shrinkTape active hk) := measurable_pi_apply _
theorem repairTape_measurable (active : Finset (Fin n)) (hk : 2 ≤ active.card) :
    Measurable (repairTape active hk) := measurable_pi_apply _

theorem requestAt_eq (a : Anchor n) (hk : 2 ≤ a.active.card) (kind : Kind) :
    requestAt a.active hk kind = a.request hk kind := rfl

end EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
