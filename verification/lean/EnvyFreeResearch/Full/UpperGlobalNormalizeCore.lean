import EnvyFreeResearch.Full.UpperGlobalNormalizeChoice
import EnvyFreeResearch.Full.UpperGlobalProtocolTwoAgents
import EnvyFreeResearch.Full.UpperGlobalProtocolMachine

/-! Query-free bounded normalization requests. Proper-sink steps only reduce
the active set; the sole potentially paid branch is the terminal two-agent call. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalNormalize
open UpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
open UpperGlobal.Sink
variable {n : ℕ}

inductive Request (n : ℕ) where
  | done : Anchor n → Request n
  | two : Anchor n → Fin n → Fin n → Request n
  | snapshot : Anchor n → Request n

def Request.anchor : Request n → Anchor n
  | .done a | .two a _ _ | .snapshot a => a

def positiveCore (fallback : Fin n) (chores : Bool) : ℕ → Anchor n → Request n
  | 0, a => .snapshot a
  | fuel+1, a =>
    if a.active.card ≤ 1 then .done (giveAllTerminal a (pick fallback a.active))
    else if a.active.card ≤ 2 then .two a (pick fallback a.active) (second fallback a.active)
    else if sinkAvailable (direction chores) a then
      positiveCore fallback chores fuel (selectedFreeze (direction chores) a)
    else .snapshot a

def normalize (fallback : Fin n) (chores : Bool) (fuel : ℕ) (a : Anchor n) : Request n :=
  if chores then
    if (zeroRows a.residue a.active).Nonempty then
      .done (giveAllTerminal a (pick fallback (zeroRows a.residue a.active)))
    else positiveCore fallback chores fuel a
  else if (positiveRows a.residue a.active).Nonempty then
    positiveCore fallback chores fuel (freezeZero a)
  else .done (giveAllTerminal a (pick fallback a.active))

def Request.Valid (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (whole : Set ℝ) : Request n → Prop
  | .done a => a.Committed μ (direction chores) whole ∧ a.HistoryCompatible ∧
      (⋃ j, domain (a.bundles j).cells)=whole
  | .two a cutter chooser => a.Committed μ (direction chores) whole ∧ a.HistoryCompatible ∧
      a.active={cutter,chooser} ∧ chooser≠cutter ∧ 0 < total a.residue cutter
  | .snapshot a => a.Committed μ (direction chores) whole ∧ a.HistoryCompatible ∧
      3 ≤ a.active.card ∧ positive a ∧ StrongOn (a.edge (direction chores)) a.active

end EnvyFreeResearch.Full.UpperGlobalNormalize
