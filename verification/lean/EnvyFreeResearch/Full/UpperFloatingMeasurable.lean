import EnvyFreeResearch.Full.UpperFloatingPayments
import EnvyFreeResearch.Full.UpperFloatingPatterns

/-!
# A deterministic Borel floating selector

Enumerate the finitely many zero/one/free patterns. Each yields an explicit
Gram-inverse candidate. Choose the first candidate satisfying the original
payment equations, frozen coordinates, box bounds, and split-cell bound.
The proved basic-point theorem guarantees that a candidate passes.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperFloating

open UpperFloatingStep

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def Good (a : Agent → Cell → ℝ) (initial x : PaymentCoord Agent Cell → ℝ) : Prop :=
  FrozenFeasible (coefficients a) (linearValue (coefficients a) initial) initial x ∧
    (splitCells x).card ≤ Fintype.card Agent ^ 2

def paymentCandidate (a : Agent → Cell → ℝ) (initial : PaymentCoord Agent Cell → ℝ)
    (p : Pattern (PaymentCoord Agent Cell)) : PaymentCoord Agent Cell → ℝ :=
  candidate (coefficients a) (linearValue (coefficients a) initial) p

def firstGood (a : Agent → Cell → ℝ) (initial : PaymentCoord Agent Cell → ℝ) :
    List (Pattern (PaymentCoord Agent Cell)) → (PaymentCoord Agent Cell → ℝ)
  | [] => initial
  | p :: rest => if Good a initial (paymentCandidate a initial p)
      then paymentCandidate a initial p else firstGood a initial rest

theorem firstGood_spec (a : Agent → Cell → ℝ) (initial : PaymentCoord Agent Cell → ℝ)
    (patterns : List (Pattern (PaymentCoord Agent Cell)))
    (hex : ∃ p ∈ patterns, Good a initial (paymentCandidate a initial p)) :
    Good a initial (firstGood a initial patterns) := by
  induction patterns with
  | nil => simp at hex
  | cons p rest ih =>
    by_cases h : Good a initial (paymentCandidate a initial p)
    · simp [firstGood, h]
    · have hr : ∃ q ∈ rest, Good a initial (paymentCandidate a initial q) := by
        obtain ⟨q, hq, hg⟩ := hex
        rcases List.mem_cons.mp hq with heq | hq
        · exact False.elim (h (heq ▸ hg))
        · exact ⟨q, hq, hg⟩
      simpa [firstGood, h] using ih hr

def select (a : Agent → Cell → ℝ) (initial : PaymentCoord Agent Cell → ℝ) :
    PaymentCoord Agent Cell → ℝ := firstGood a initial Finset.univ.toList

theorem select_good (a : Agent → Cell → ℝ) (initial : PaymentCoord Agent Cell → ℝ)
    (hbox : ∀ c, 0 ≤ initial c ∧ initial c ≤ 1)
    (hrow : ∀ e, ∑ j, initial (e, j) = 1) : Good a initial (select a initial) := by
  apply firstGood_spec
  obtain ⟨x, hx, hcount, hk⟩ := exists_floated_basic a initial hbox hrow
  refine ⟨patternOf x, by simp, ?_⟩
  have heq : paymentCandidate a initial (patternOf x) = x :=
    candidate_patternOf (coefficients a) (linearValue (coefficients a) initial) x hx.1 hk
  rw [heq]
  exact ⟨hx, hcount⟩

/-- Complete guarantees for the deterministic finite selector. -/
theorem select_spec (a : Agent → Cell → ℝ) (initial : PaymentCoord Agent Cell → ℝ)
    (hbox : ∀ c, 0 ≤ initial c ∧ initial c ≤ 1)
    (hrow : ∀ e, ∑ j, initial (e, j) = 1) :
    (∀ c, 0 ≤ select a initial c ∧ select a initial c ≤ 1) ∧
      (∀ e, ∑ j, select a initial (e, j) = 1) ∧
      (∀ i j, (∑ e, a i e * select a initial (e, some j)) =
        ∑ e, a i e * initial (e, some j)) ∧
      Frozen initial (select a initial) ∧
      (splitCells (select a initial)).card ≤ Fintype.card Agent ^ 2 := by
  obtain ⟨hx, hcount⟩ := select_good a initial hbox hrow
  refine ⟨hx.1.1, ?_, ?_, hx.2, hcount⟩
  · intro e
    rw [← cell_equation a (select a initial) e, hx.1.2, cell_equation, hrow]
  · intro i j
    rw [← moment_equation a (select a initial) i j, hx.1.2, moment_equation]

section Measurability

variable {X : Type*} [MeasurableSpace X]

omit [Fintype Agent] [Fintype Cell] in
theorem coefficients_measurable (a : X → Agent → Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (r : PaymentEquation Agent Cell) (c : PaymentCoord Agent Cell) :
    Measurable (fun z => coefficients (a z) r c) := by
  cases r with
  | inl e => exact measurable_const
  | inr ij =>
    dsimp [coefficients]
    split_ifs
    · exact ha ij.1 c.1
    · exact measurable_const

theorem linearValue_measurable {Coord Equation : Type*} [Fintype Coord]
    (A : X → Equation → Coord → ℝ) (x : X → Coord → ℝ)
    (hA : ∀ r c, Measurable (fun z => A z r c))
    (hx : ∀ c, Measurable (fun z => x z c)) (r : Equation) :
    Measurable (fun z => linearValue (A z) (x z) r) :=
  Finset.measurable_sum _ (fun c _ => (hA r c).mul (hx c))

theorem split_card_measurable {Color : Type*} [Fintype Color]
    (x : X → Cell × Color → ℝ) (hx : ∀ c, Measurable (fun z => x z c)) :
    Measurable (fun z => (splitCells (x z)).card) := by
  have htest (e : Cell) : MeasurableSet {z | ∃ j, 0 < x z (e, j) ∧ x z (e, j) < 1} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun j =>
      (measurableSet_lt measurable_const (hx (e, j))).inter
        (measurableSet_lt (hx (e, j)) measurable_const))
  have hm : Measurable (fun z => ∑ e : Cell,
      if ∃ j, 0 < x z (e, j) ∧ x z (e, j) < 1 then (1 : ℕ) else 0) :=
    Finset.measurable_sum _ (fun e _ => measurable_const.ite (htest e) measurable_const)
  convert hm using 1
  funext z
  rw [splitCells_eq_filter, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem measurableSet_good (a : X → Agent → Cell → ℝ)
    (initial x : X → PaymentCoord Agent Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hinitial : ∀ c, Measurable (fun z => initial z c))
    (hx : ∀ c, Measurable (fun z => x z c)) :
    MeasurableSet {z | Good (a z) (initial z) (x z)} := by
  have hbox : MeasurableSet {z | ∀ c, 0 ≤ x z c ∧ x z c ≤ 1} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun c =>
      (measurableSet_le measurable_const (hx c)).inter (measurableSet_le (hx c) measurable_const))
  have hequations : MeasurableSet {z | ∀ r,
      linearValue (coefficients (a z)) (x z) r = linearValue (coefficients (a z)) (initial z) r} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun r => measurableSet_eq_fun
      (linearValue_measurable _ x (coefficients_measurable a ha) hx r)
      (linearValue_measurable _ initial (coefficients_measurable a ha) hinitial r))
  have hfrozen : MeasurableSet {z | Frozen (initial z) (x z)} := by
    unfold Frozen
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro c
    have hzero : MeasurableSet {z | initial z c = 0} :=
      measurableSet_eq_fun (hinitial c) measurable_const
    have hone : MeasurableSet {z | initial z c = 1} :=
      measurableSet_eq_fun (hinitial c) measurable_const
    have heq : MeasurableSet {z | x z c = initial z c} :=
      measurableSet_eq_fun (hx c) (hinitial c)
    convert (hzero.union hone).compl.union heq using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hcount : MeasurableSet {z | (splitCells (x z)).card ≤ Fintype.card Agent ^ 2} :=
    measurableSet_le (split_card_measurable x hx) measurable_const
  exact ((hbox.inter hequations).inter hfrozen).inter hcount

theorem paymentCandidate_measurable (a : X → Agent → Cell → ℝ)
    (initial : X → PaymentCoord Agent Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hinitial : ∀ c, Measurable (fun z => initial z c))
    (p : Pattern (PaymentCoord Agent Cell)) (c : PaymentCoord Agent Cell) :
    Measurable (fun z => paymentCandidate (a z) (initial z) p c) :=
  candidate_measurable _ _ (coefficients_measurable a ha)
    (linearValue_measurable _ initial (coefficients_measurable a ha) hinitial) p c

theorem firstGood_measurable (a : X → Agent → Cell → ℝ)
    (initial : X → PaymentCoord Agent Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hinitial : ∀ c, Measurable (fun z => initial z c))
    (patterns : List (Pattern (PaymentCoord Agent Cell))) (c : PaymentCoord Agent Cell) :
    Measurable (fun z => firstGood (a z) (initial z) patterns c) := by
  induction patterns with
  | nil => exact hinitial c
  | cons p rest ih =>
    have hc := paymentCandidate_measurable a initial ha hinitial p
    simpa only [firstGood, ite_apply] using
      (hc c).ite (measurableSet_good a initial
        (fun z => paymentCandidate (a z) (initial z) p) ha hinitial hc) ih

/-- Borel measurability of every coordinate of the actual selected plan.
The real tables keep their ordinary Borel structures. -/
theorem select_measurable (a : X → Agent → Cell → ℝ)
    (initial : X → PaymentCoord Agent Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hinitial : ∀ c, Measurable (fun z => initial z c)) :
    Measurable (fun z => select (a z) (initial z)) :=
  Measurable.of_eval (fun c => firstGood_measurable a initial ha hinitial _ c)

end Measurability

end EnvyFreeResearch.Full.UpperFloating
