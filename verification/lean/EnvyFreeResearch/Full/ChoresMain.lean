import EnvyFreeResearch.Full.ChoresMainProtocol
import EnvyFreeResearch.Full.ChoresOuterLocalComplete
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryUnit
import EnvyFreeResearch.Full.ChoresComponentBudgetAsymptoticGlobal

/-! The complete deterministic chore protocol, from the original ordinary
oracle to a literal complete envy-free allocation of the closed unit interval.
The concrete local step discharges the entire population induction premise. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Main
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open Population Parameters

theorem native_complete (n : ℕ) (hn : 0 < n) (cost : Costs n) :
    CompleteSpec cost id (nativeProgram n) (totalCapacity n).queries (totalCapacity n).cuts :=
  recursive_complete_specification Outer.concreteStep
    (fun k => (totalCapacity k).queries) (fun k => (totalCapacity k).cuts)
    Outer.concrete_step_complete n hn cost

def bound (n : ℕ) : ℕ := min (n^(3*n)*2^(27*n)) (2^(14*weight n))

theorem capacity_bound {n : ℕ} (hn : 3 ≤ n) : n+(totalCapacity n).queries ≤ bound n :=
  Nat.le_min.mpr ⟨(total_capacity_leading_exponent hn).1,total_with_initial_evals hn⟩

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

theorem bound_le_leading (n : ℕ) : bound n ≤ n^(3*n)*2^(27*n) := Nat.min_le_left _ _

theorem bound_le_explicit (n : ℕ) : bound n ≤ 2^(14*weight n) := Nat.min_le_right _ _

end EnvyFreeResearch.Full.Chores.Main
