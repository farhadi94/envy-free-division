import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolValidity

/-! The actual saved anchor potential has room for one in-flight Snapshot
credit. Strong connectivity rules out saturation before a paid phase. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
open RefinedUpperGlobalPhysical GlobalCompletion
variable {n : ℕ}

def pendingCredit : Phase n → ℕ
  | .firstShrink _ _ | .secondShrink _ | .finalRepair _ => 1
  | _ => 0

def credit (chores : Bool) (phase : Phase n) : ℕ :=
  phase.anchor.cachedPotential (if chores then .chore else .cake) + pendingCredit phase

/-- Number of accepted non-Snapshot calls still available in this iteration. -/
def remainingCalls : Phase n → ℕ
  | .firstShrink _ _ => 3
  | .secondShrink _ => 2
  | .finalRepair _ => 1
  | _ => 0

theorem cached_potential_le (a : Anchor n) (direction : Direction) :
    a.cachedPotential direction ≤ n*(n-1) := by
  simpa only [Anchor.cachedPotential,GlobalCompletion.dominationPotential,Fintype.card_fin] using
    R4GlobalPotential.global_potential_cap (margin direction a.cachedValue) a.cachedResidue

theorem cached_potential_lt_of_edge (a : Anchor n) (direction : Direction)
    (i j : Fin n) (hedge : a.edge direction i j) :
    a.cachedPotential direction < n*(n-1) := by
  have hmissing : j ∉ R4GlobalPotential.targets (margin direction a.cachedValue) a.cachedResidue i := by
    simp only [R4GlobalPotential.targets,Finset.mem_filter,Finset.mem_univ,true_and]
    exact fun h => not_le_of_gt hedge.2.2.2 h.2
  simpa only [Anchor.cachedPotential,GlobalCompletion.dominationPotential,Fintype.card_fin] using
    R2OnlinePotential.potential_lt_of_missing _
      (R4GlobalPotential.targets_proper (margin direction a.cachedValue) a.cachedResidue)
      i j hedge.2.2.1 hmissing

theorem strong_has_edge (a : Anchor n) (direction : Direction)
    (hk : 2 ≤ a.active.card)
    (hs : RefinedUpperGlobal.Sink.StrongOn (a.edge direction) a.active) :
    ∃ i j, a.edge direction i j := by
  obtain ⟨i,hi,j,hj,hne⟩ := Finset.one_lt_card.mp (by omega : 1 < a.active.card)
  rcases (hs i hi j hj).cases_tail with heq | ⟨k,_,hkj⟩
  · exact (hne heq.symm).elim
  · exact ⟨k,j,hkj⟩

theorem strong_credit_room (a : Anchor n) (direction : Direction)
    (hk : 2 ≤ a.active.card)
    (hs : RefinedUpperGlobal.Sink.StrongOn (a.edge direction) a.active) :
    a.cachedPotential direction + 1 ≤ n*(n-1) := by
  obtain ⟨i,j,he⟩ := strong_has_edge a direction hk hs
  exact cached_potential_lt_of_edge a direction i j he

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (chores : Bool) (whole : Set ℝ)

theorem valid_credit_le (phase : Phase n) (hv : phase.Valid μ chores whole) :
    credit chores phase ≤ n*(n-1) := by
  cases phase with
  | normalize a => exact cached_potential_le a _
  | snapshot a => exact cached_potential_le a _
  | done a => exact cached_potential_le a _
  | firstShrink p G => exact strong_credit_room p.anchor _ (by have := hv.population; omega) hv.strong
  | secondShrink p => exact strong_credit_room p.anchor _ (by have := hv.population; omega) hv.strong
  | finalRepair p => exact strong_credit_room p.anchor _ (by have := hv.population; omega) hv.strong

theorem valid_snapshot_room (a : Anchor n) (hv : (Phase.snapshot a).Valid μ chores whole) :
    a.cachedPotential (if chores then .chore else .cake) + 1 ≤ n*(n-1) :=
  strong_credit_room a _ (by have := hv.2.2.1; omega) hv.2.2.2.2

end EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
