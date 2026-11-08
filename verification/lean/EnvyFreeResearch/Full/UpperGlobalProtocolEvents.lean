import EnvyFreeResearch.Full.UpperGlobalProtocolDispatch
import EnvyFreeResearch.Full.UpperGlobalProtocolMachineMeasurable
import EnvyFreeResearch.Full.UpperGlobalRun

/-! Events of the concrete global execution, indexed by every actual machine
step. The normalization step is deterministic; all paid tapes remain fresh. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape
variable {n : ℕ}

def Phase.paidKind : Phase n → Option Kind
  | .snapshot _ => some .snapshot
  | .firstShrink _ _ | .secondShrink _ => some .shrink
  | .finalRepair _ => some .repair
  | .normalize _ | .done _ => none

def Phase.accepted (policy : Policy n) (chores : Bool) (phase : Phase n) (draw : Universal n) : Bool :=
  match phase with
  | .snapshot a =>
    if hk : 3 ≤ a.active.card then
      letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
      !(a.snapshotResult policy hk chores (draw (a.request (by omega) .snapshot))).2.2
    else false
  | .firstShrink p G =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      !(p.shrinkResult policy (by omega) chores G (draw (p.anchor.request (by omega) .shrink))).2.2
    else false
  | .secondShrink p =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      !(p.shrinkResult policy (by omega) chores (2/UpperRepair.nearError n)
        (draw (p.anchor.request (by omega) .shrink))).2.2
    else false
  | .finalRepair p =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      !(p.repairResult policy (by omega) chores (draw (p.anchor.request (by omega) .repair))).2.2
    else false
  | .normalize _ | .done _ => false

def Phase.run (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (t : ℕ) (omega : Stream (Universal n)) : Phase n :=
  UpperGlobalRun.run (Phase.step policy fallback chores) initial t omega

def paidEvent (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (kind : Kind) (t : ℕ) : Set (Stream (Universal n)) :=
  {omega | (Phase.run policy fallback chores initial t omega).paidKind=some kind}

def successEvent (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (kind : Kind) (t : ℕ) : Set (Stream (Universal n)) :=
  {omega | (Phase.run policy fallback chores initial t omega).paidKind=some kind ∧
    Phase.accepted policy chores (Phase.run policy fallback chores initial t omega) (omega t)=true}

def Phase.finished : Phase n → Bool
  | .done _ => true
  | _ => false

theorem phaseRun_zero (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) : Phase.run policy fallback chores initial 0 omega=initial := rfl

theorem phaseRun_succ (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (t : ℕ) (omega : Stream (Universal n)) :
    Phase.run policy fallback chores initial (t+1) omega=
      Phase.step policy fallback chores (Phase.run policy fallback chores initial t omega) (omega t) := rfl

end EnvyFreeResearch.Full.UpperGlobalPhysical
