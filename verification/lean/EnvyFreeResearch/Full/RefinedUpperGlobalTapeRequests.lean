import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolLaw

/-! One universal attempt draw contains independent actual tapes for every
permitted population and request kind. The current phase chooses a projection. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalTape
open MeasureTheory
open scoped Classical

inductive Kind where
  | snapshot
  | shrink
  | repair
  deriving DecidableEq

instance : Fintype Kind := ⟨{.snapshot,.shrink,.repair},by intro k; cases k <;> simp⟩

instance : MeasurableSpace Kind := ⊤
instance : DiscreteMeasurableSpace Kind := ⟨fun _ => trivial⟩

abbrev Population (n : ℕ) := {k : Fin (n+1) // 2 ≤ k.val}
abbrev Request (n : ℕ) := Population n × Kind

theorem population_nonempty (n : ℕ) (p : Population n) : Nonempty (Fin p.val.val) :=
  ⟨⟨0,by have h := p.property; omega⟩⟩

def Draw (n : ℕ) (request : Request n) : Type :=
  match request.2 with
  | .snapshot => RefinedUpperSnapshotProtocol.Tape n request.1.val.val
  | .shrink => RefinedUpperRepair.Tape n request.1.val.val
  | .repair => RefinedUpperRepair.Tape n request.1.val.val

instance (n : ℕ) (request : Request n) : MeasurableSpace (Draw n request) := by
  rcases request with ⟨p,kind⟩
  cases kind <;> dsimp [Draw] <;> infer_instance

def drawLaw (n : ℕ) (request : Request n) : Measure (Draw n request) := by
  rcases request with ⟨p,kind⟩
  cases kind
  · exact RefinedUpperSnapshotProtocol.law n p.val.val
  · exact RefinedUpperRepair.law n p.val.val
  · exact RefinedUpperRepair.law n p.val.val

instance drawLaw_probability (n : ℕ) (request : Request n) :
    IsProbabilityMeasure (drawLaw n request) := by
  rcases request with ⟨p,kind⟩
  letI : Nonempty (Fin p.val.val) := population_nonempty n p
  cases kind
  · exact RefinedUpperSnapshotProtocol.law_probability (n := n) (k := p.val.val)
  · exact RefinedUpperRepair.law_probability (n := n) (k := p.val.val)
  · exact RefinedUpperRepair.law_probability (n := n) (k := p.val.val)

abbrev Universal (n : ℕ) := (request : Request n) → Draw n request

def universalLaw (n : ℕ) : Measure (Universal n) := Measure.pi (drawLaw n)

instance universalLaw_probability (n : ℕ) : IsProbabilityMeasure (universalLaw n) := by
  unfold universalLaw
  infer_instance

theorem request_preserves (n : ℕ) (request : Request n) :
    MeasurePreserving (fun draw : Universal n => draw request)
      (universalLaw n) (drawLaw n request) := measurePreserving_eval _ request

end EnvyFreeResearch.Full.RefinedUpperGlobalTape
