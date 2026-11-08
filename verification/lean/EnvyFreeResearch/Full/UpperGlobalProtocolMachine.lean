import EnvyFreeResearch.Full.UpperGlobalProtocolHistory
import EnvyFreeResearch.Full.UpperGlobalProtocolMeasurable
import EnvyFreeResearch.Full.UpperPopulationIndex

/-! Concrete saved data between paid calls. All original observers' endpoint
records are retained; shrinking pieces remain with their original owners. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

structure Pending (n : ℕ) where
  anchor : Anchor n
  snapshot : Fin n → State n
  shrunk : Fin n → State n
  buffer : State n
  permutation : Equiv.Perm (Fin n)
  witness : Fin n
  target : Fin n

def Pending.endowments (p : Pending n) (j : Fin n) : State n :=
  join (p.anchor.bundles j)
    (join (p.shrunk j) (p.snapshot (p.permutation j)) p.buffer.history) p.buffer.history

def Pending.addShrink (p : Pending n) (pieces : Fin n → State n) (residue : State n) : Pending n :=
  { p with shrunk := fun j => join (p.shrunk j) (pieces j) residue.history, buffer := residue }

def Pending.transfer (p : Pending n) (alpha : Equiv.Perm (Fin n)) (b h : Fin n) : Pending n :=
  { p with permutation := alpha, witness := b, target := h }

def Pending.start (a : Anchor n) (pieces : Fin n → State n) (residue : State n)
    (b h : Fin n) : Pending n :=
  ⟨a,pieces,fun _ => empty residue.history,residue,Equiv.refl _,b,h⟩

/-- A failed paid call retains the physical saved data and adopts its complete
query history. The cached values of every retained endpoint are still available. -/
def Pending.refresh (p : Pending n) (history : UpperCircularStage.History n) : Pending n :=
  { p with buffer := ⟨p.buffer.cells,history⟩ }

inductive Phase (n : ℕ) where
  | normalize : Anchor n → Phase n
  | snapshot : Anchor n → Phase n
  | firstShrink : Pending n → ℝ → Phase n
  | secondShrink : Pending n → Phase n
  | finalRepair : Pending n → Phase n
  | done : Anchor n → Phase n

def Phase.anchor : Phase n → Anchor n
  | .normalize a | .snapshot a | .done a => a
  | .firstShrink p _ | .secondShrink p | .finalRepair p => p.anchor

def Phase.population (phase : Phase n) : ℕ := phase.anchor.active.card

theorem population_le (phase : Phase n) : phase.population ≤ n :=
  UpperZeroRows.active_size_bound phase.anchor.active

theorem endowments_domain (p : Pending n) (j : Fin n) :
    domain (p.endowments j).cells = domain (p.anchor.bundles j).cells ∪
      domain (p.shrunk j).cells ∪ domain (p.snapshot (p.permutation j)).cells := by
  simp only [Pending.endowments,join_domain,Set.union_assoc]

theorem addShrink_domain (p : Pending n) (pieces : Fin n → State n) (residue : State n) (j : Fin n) :
    domain ((p.addShrink pieces residue).shrunk j).cells =
      domain (p.shrunk j).cells ∪ domain (pieces j).cells := by
  simp only [Pending.addShrink,join_domain]

theorem refresh_buffer_domain (p : Pending n) (history : UpperCircularStage.History n) :
    domain (p.refresh history).buffer.cells = domain p.buffer.cells := rfl

theorem endowments_history (p : Pending n) (j : Fin n) :
    (p.endowments j).history = p.buffer.history := rfl

end EnvyFreeResearch.Full.UpperGlobalPhysical
