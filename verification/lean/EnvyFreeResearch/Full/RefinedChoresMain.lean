import EnvyFreeResearch.Full.RefinedChoresMainProtocol
import EnvyFreeResearch.Full.RefinedChoresComplete
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryUnit
import EnvyFreeResearch.Full.RefinedChoresBudgets

/-! The complete deterministic chore protocol, from the original ordinary
oracle to a literal complete envy-free allocation of the closed unit interval.
The concrete local step discharges the entire population induction premise. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresMain
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion Chores.QueryProgram
open Chores.Population RefinedChoresParameters

theorem native_complete (n : ℕ) (hn : 0 < n) (cost : Costs n) :
    CompleteSpec cost id (nativeProgram n) (totalCapacity n).queries (totalCapacity n).cuts :=
  recursive_complete_specification RefinedChoresLocal.concreteStep
    (fun k => (totalCapacity k).queries) (fun k => (totalCapacity k).cuts)
    RefinedChoresLocal.concrete_step_complete n hn cost

def bound (n : ℕ) : ℕ := Nat.factorial n*2^(25*n+18)

theorem capacity_bound {n : ℕ} (hn : 3 ≤ n) : n+(totalCapacity n).queries ≤ bound n := by
  have hcap := (total_capacity_envelope (by omega : 1 ≤ n)).1
  have hnsmall : n ≤ Nat.factorial n*2^(25*n+17) := by
    calc
      n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self (n := n))
      _ ≤ 2^(25*n+17) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := by simpa only [one_mul] using
        Nat.mul_le_mul_right (2^(25*n+17)) (show 1 ≤ Nat.factorial n from Nat.factorial_pos n)
  have he : bound n=2*(Nat.factorial n*2^(25*n+17)) := by
    unfold bound
    rw [show 25*n+18=(25*n+17)+1 by omega,pow_succ]
    ring
  rw [he]
  omega

/-- The actual execution includes every original Eval/Cut and starts with
no supplied valuation cache. Output endpoints are inherited or actual Cut
replies; endpoint zero has one fixed owner. -/
theorem deterministic_chores {n : ℕ} (hn : 3 ≤ n) (cost : Costs n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle) :
    ∃ out : UnitEntry.Output n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (program n (by omega)).protocol oracle () (bound n) [] =
        ⟨trace,.returned out⟩ ∧
      trace.length ≤ bound n ∧ virtualCuts trace ≤ bound n ∧
      Pairwise (fun i j => Disjoint (out.share i) (out.share j)) ∧
      (⋃ i, out.share i)=Icc 0 1 ∧
      (∀ i j, (cost.measure i).real (out.share i) ≤ (cost.measure i).real (out.share j)) ∧
      (∀ i, MeasurableSet (out.share i)) ∧
      (∀ i p, p ∈ out.allocation.pieces i → 0 ≤ p.left ∧ p.left ≤ p.right ∧ p.right ≤ 1) ∧
      Boundary.AllocationKnown (Boundary.Known ({0,1} : Set ℝ) trace) out.allocation ∧
      Boundary.Scoped ({0,1} : Set ℝ) trace ∧
      (∀ qr ∈ trace, Legal (measureProfile cost.measure) qr.1 ∧
        ValidReply (measureProfile cost.measure) qr.1 qr.2) := by
  have hnpos : 0 < n := by omega
  have hc := native_complete n hnpos cost
  obtain ⟨out,trace,he,hQ,hC,howner,hs,hlegal⟩ := UnitEntry.program_correct cost
    (⟨0,hnpos⟩ : Fin n) (nativeProgram n) (totalCapacity n).queries (totalCapacity n).cuts
    hc.1 oracle hpolicy []
  have hbound := hQ.trans (capacity_bound hn)
  have hcuts : virtualCuts trace ≤ bound n :=
    (show virtualCuts trace ≤ trace.length from List.countP_le_length).trans hbound
  obtain ⟨hknown,hscope⟩ := Outer.unit_program_known cost (⟨0,hnpos⟩ : Fin n)
    (nativeProgram n) hc.2 oracle hpolicy [] trace out he
  exact ⟨out,trace,he.run (bound n) hbound,hbound,hcuts,
    UnitEntry.share_disjoint cost.measure out hs,UnitEntry.share_cover cost.measure out hs,
    UnitEntry.share_envy_free cost.measure out hs,UnitEntry.share_measurable out,
    UnitEntry.interval_bounds cost.measure out hs,hknown,hscope,hlegal⟩

theorem bound_le_leading (n : ℕ) : bound n ≤ n^n*2^(25*n+18) :=
  Nat.mul_le_mul_right _ (Nat.factorial_le_pow n)

end EnvyFreeResearch.Full.RefinedChoresMain
#print axioms EnvyFreeResearch.Full.RefinedChoresMain.deterministic_chores
