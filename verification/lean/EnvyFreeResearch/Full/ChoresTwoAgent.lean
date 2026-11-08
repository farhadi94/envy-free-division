import EnvyFreeResearch.Full.ChoresContinuous
import EnvyFreeResearch.Full.IntervalOracle

/-!
# A complete deterministic physical two-agent chore protocol

The protocol is a next-action function of its answered history. It performs
four ordinary interval queries: cutter total, cutter half Cut, and the two
chooser interval costs. Its correctness holds for every legal oracle, with
no restriction on plateau replies. All material of `[0,1]`, including zero
cost endpoints, is assigned. The general-n scheduler is not implemented here.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open Set MeasureTheory
open OracleProtocol IntervalOracle

/-- An actual nonatomic measure profile supplies the concrete cumulative oracle. -/
def measureProfile {Agent : Type*} (cost : Agent → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)] :
    IntervalOracle.Profile Agent where
  cumulative := fun i => prefixCost (cost i) 0
  continuous := fun i => prefixCost_continuous (cost i) 0
  zero := fun i => prefixCost_self (cost i) 0

/-- Convert the actual two observed costs to a physical assignment. -/
def choiceAllocation (x leftCost rightCost : ℝ) : Fin 2 → Set ℝ :=
  if leftCost ≤ rightCost then
    fun i => if i = 0 then Ioc x 1 else Icc 0 x
  else
    fun i => if i = 0 then Icc 0 x else Ioc x 1

/-- The deterministic four-query algorithm; no valuation is supplied to it. -/
def twoAgentProtocol :
    Protocol Unit (Query (Fin 2)) ℝ (Fin 2 → Set ℝ) := fun _ history =>
  match history with
  | [] => .ask (.eval 0 0 1)
  | [(_, total)] => .ask (.cut 0 0 1 (total / 2))
  | [_, (_, x)] => .ask (.eval 1 0 x)
  | [_, (_, x), _] => .ask (.eval 1 x 1)
  | [_, (_, x), (_, leftCost), (_, rightCost)] =>
      .returned (choiceAllocation x leftCost rightCost)
  | _ => .diverge

def isCutQuery {Agent : Type*} : Query Agent → Bool
  | .eval _ _ _ => false
  | .cut _ _ _ _ => true

/-- Exact execution through all four actual interval requests. -/
theorem twoAgentProtocol_trace (O : Query (Fin 2) → Option ℝ)
    (total x leftCost rightCost : ℝ)
    (htotal : O (.eval 0 0 1) = some total)
    (hcut : O (.cut 0 0 1 (total / 2)) = some x)
    (hleft : O (.eval 1 0 x) = some leftCost)
    (hright : O (.eval 1 x 1) = some rightCost) :
    run twoAgentProtocol O () 4 [] =
      ⟨[(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x),
        (.eval 1 0 x, leftCost), (.eval 1 x 1, rightCost)],
        .returned (choiceAllocation x leftCost rightCost)⟩ := by
  simp [twoAgentProtocol, htotal, hcut, hleft, hright]

/-- End-to-end physical correctness and ordinary-query accounting for the
complete two-agent protocol. The only oracle assumption is the ordinary
Eval/Cut contract; it contains no allocation or envy-freeness conclusion. -/
theorem complete_twoAgent_protocol (cost : Fin 2 → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (O : Query (Fin 2) → Option ℝ) (hO : IsLegalOracle (measureProfile cost) O) :
    ∃ x ∈ Icc (0 : ℝ) 1,
      let A := twoAgentAllocation cost 0 x 1
      let execution := run twoAgentProtocol O () 4 []
      execution.stop = .returned A ∧ execution.answered.length = 4 ∧
        (execution.answered.filter (fun qr => isCutQuery qr.1)).length = 1 ∧
        Disjoint (A 0) (A 1) ∧ A 0 ∪ A 1 = Icc 0 1 ∧
        ∀ i j, (cost i).real (A i) ≤ (cost i).real (A j) := by
  obtain ⟨total, htotal⟩ := hO.complete (.eval 0 0 1) (by norm_num [Legal])
  have htotalval : total = (cost 0).real (Icc 0 1) := by
    have h := (hO.sound _ _ htotal).2
    simpa [ValidReply, measureProfile, prefixCost_self, prefixCost, measureReal_def] using h
  have hnonneg : (0 : ℝ) ≤ (cost 0).real (Icc 0 1) := measureReal_nonneg
  have hlegalCut : Legal (measureProfile cost) (.cut 0 0 1 (total / 2)) := by
    simp only [Legal, measureProfile, ExtremalRoots.LegalTarget]
    rw [prefixCost_self]
    change 0 ≤ (0 : ℝ) ∧ 0 ≤ (1 : ℝ) ∧ 1 ≤ (1 : ℝ) ∧
      min 0 ((cost 0).real (Icc 0 1) - 0) ≤ total / 2 ∧
        total / 2 ≤ max 0 ((cost 0).real (Icc 0 1) - 0)
    rw [sub_zero, min_eq_left hnonneg, max_eq_right hnonneg, htotalval]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor <;> linarith
  obtain ⟨x, hcut⟩ := hO.complete _ hlegalCut
  have hcutval : x ∈ Icc (0 : ℝ) 1 ∧
      (cost 0).real (Icc 0 x) = (cost 0).real (Icc 0 1) / 2 := by
    have h := (hO.sound _ _ hcut).2
    simpa [ValidReply, measureProfile, prefixCost_self, htotalval, prefixCost,
      measureReal_def] using h
  obtain ⟨leftCost, hleft⟩ := hO.complete (.eval 1 0 x)
    ⟨le_rfl, hcutval.1.1, hcutval.1.2⟩
  obtain ⟨rightCost, hright⟩ := hO.complete (.eval 1 x 1)
    ⟨hcutval.1.1, hcutval.1.2, le_rfl⟩
  have hleftval : leftCost = (cost 1).real (Icc 0 x) := by
    have h := (hO.sound _ _ hleft).2
    simpa [ValidReply, measureProfile, prefixCost_self, prefixCost, measureReal_def] using h
  have hrightval : rightCost = (cost 1).real (Ioc x 1) := by
    have h := (hO.sound _ _ hright).2
    change rightCost = prefixCost (cost 1) 0 1 - prefixCost (cost 1) 0 x at h
    rw [prefix_difference_eq_interval (cost 1) hcutval.1.1 hcutval.1.2] at h
    exact h
  have htrace := twoAgentProtocol_trace O total x leftCost rightCost htotal hcut hleft hright
  have hallocation : choiceAllocation x leftCost rightCost = twoAgentAllocation cost 0 x 1 := by
    rw [hleftval, hrightval]
    rfl
  rw [hallocation] at htrace
  refine ⟨x, hcutval.1, ?_⟩
  dsimp only
  rw [htrace]
  simpa [isCutQuery] using twoAgent_every_half_root cost hcutval.1 hcutval.2

/-- In particular the constructed always-leftmost ordinary oracle realizes
this protocol on every finite nonatomic input profile. -/
theorem complete_twoAgent_constructed_oracle (cost : Fin 2 → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)] :
    ∃ x ∈ Icc (0 : ℝ) 1,
      let A := twoAgentAllocation cost 0 x 1
      let execution := run twoAgentProtocol (IntervalOracle.oracle (measureProfile cost)) () 4 []
      execution.stop = .returned A ∧ execution.answered.length = 4 ∧
        (execution.answered.filter (fun qr => isCutQuery qr.1)).length = 1 ∧
        Disjoint (A 0) (A 1) ∧ A 0 ∪ A 1 = Icc 0 1 ∧
        ∀ i j, (cost i).real (A i) ≤ (cost i).real (A j) :=
  complete_twoAgent_protocol cost _ (IntervalOracle.oracle_isLegal _)

end EnvyFreeResearch.Full.Chores
