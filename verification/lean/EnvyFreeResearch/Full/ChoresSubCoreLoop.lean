import EnvyFreeResearch.Full.ChoresSubCoreStep

/-!
# The selected-set loop program and its exact inherited transition

The loop is an actual compositional query program. A smaller recursive call
is made only while fewer than all contested parents are assigned. After it
returns, the fixed cached-data growth operator and cap refresh prepare the
next inherited state. Closing the recursive-call implementation is separate
from this program definition and its local invariant theorem.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set QueryProgram

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]
    {value : Agent → Parent → Coord → Value} {feasible : Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}

structure Node (selected : Finset Agent) (Parent Coord : Type*) where
  assigned : selected ↪ Parent
  point : Parent → Coord

structure LoopState (Agent Parent Coord : Type*) where
  selected : Finset Agent
  node : Node selected Parent Coord

def ownValue (selected : Finset Agent) (node : Node selected Parent Coord)
    (value : Agent → Parent → Coord → Value) (i : selected) : Value :=
  value i.val (node.assigned i) (node.point (node.assigned i))

def loopBenchmark (selected : Finset Agent) (node : Node selected Parent Coord)
    (value : Agent → Parent → Coord → Value) (target : Agent → Value) (i : Agent) : Value :=
  if hi : i ∈ selected then ownValue selected node value ⟨i, hi⟩ else target i

def Inherited (table : TrimTable value feasible whole target) (s : LoopState Agent Parent Coord) : Prop :=
  (∀ p, s.node.point p ∈ feasible ∧ s.node.point p ≤ table.remainingCap s.selected p) ∧
  (∀ i : s.selected, target i.val ≤ ownValue s.selected s.node value i) ∧
  (∀ i j : s.selected, value i.val (s.node.assigned j) (s.node.point (s.node.assigned j)) ≤
    ownValue s.selected s.node value i) ∧
  (∀ p, (∀ i, s.node.assigned i ≠ p) → s.node.point p = table.remainingCap s.selected p)

def nextLoopState (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (hcard : selected.card < Fintype.card Parent) (returned : Node selected Parent Coord) : LoopState Agent Parent Coord :=
  let growth := growthStep table oldOwner hOwner selected hcard returned.assigned
  let enlarged := insert growth.entrant selected
  ⟨enlarged, growth.assigned,
    refreshUnused enlarged growth.assigned returned.point (table.remainingCap enlarged)⟩

theorem nextLoopState_card (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (hcard : selected.card < Fintype.card Parent) (returned : Node selected Parent Coord) :
    (nextLoopState table oldOwner hOwner selected hcard returned).selected.card = selected.card + 1 :=
  Finset.card_insert_of_notMem (growthStep table oldOwner hOwner selected hcard returned.assigned).outside

theorem nextLoopState_contains (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (hcard : selected.card < Fintype.card Parent) (returned : Node selected Parent Coord) :
    selected ⊆ (nextLoopState table oldOwner hOwner selected hcard returned).selected := Finset.subset_insert _ _

def RecursiveCorrect (table : TrimTable value feasible whole target) (selected : Finset Agent)
    (before returned : Node selected Parent Coord) : Prop :=
  (∀ p, returned.point p ∈ feasible ∧ returned.point p ≤ table.remainingCap selected p) ∧
  (∀ i : selected, ∀ p, value i.val p (returned.point p) ≤ ownValue selected returned value i) ∧
  (∀ i : selected, ownValue selected before value i ≤ ownValue selected returned value i) ∧
  (∀ p, (∀ i, returned.assigned i ≠ p) → returned.point p = table.remainingCap selected p)

/-- The exact output of growth-and-refresh is the coherent inherited input
for the next smaller call, with assigned records and own costs preserved. -/
theorem nextLoopState_inherited (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (hstrict : ∀ i p, StrictMonoOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (old : Parent → Coord) (hold : ∀ p, old p ∈ feasible) (holdCap : ∀ p, old p ≤ whole p)
    (hOldEF : ∀ p q, value (oldOwner p) q (old q) ≤ value (oldOwner p) p (old p))
    (hOldTarget : ∀ p, target (oldOwner p) ≤ value (oldOwner p) p (old p))
    (selected : Finset Agent) (hcard : selected.card < Fintype.card Parent)
    (before returned : Node selected Parent Coord)
    (hbefore : Inherited table ⟨selected, before⟩) (hreturn : RecursiveCorrect table selected before returned) :
    Inherited table (nextLoopState table oldOwner hOwner selected hcard returned) := by
  classical
  let benchmark := loopBenchmark selected before value target
  let growth := growthStep table oldOwner hOwner selected hcard returned.assigned
  let enlarged := insert growth.entrant selected
  have hbench : ∀ i : selected, benchmark i.val ≤ ownValue selected returned value i := by
    intro i
    simpa only [benchmark, loopBenchmark, dite_eq_left i.property] using hreturn.2.2.1 i
  have houtBench : ∀ i, i ∉ selected → benchmark i ≤ target i := by
    intro i hi
    simp only [benchmark, loopBenchmark, dite_eq_right hi, le_refl]
  have htargetBench : ∀ i, target i ≤ benchmark i := by
    intro i
    unfold benchmark loopBenchmark
    split_ifs with hi
    · exact hbefore.2.1 ⟨i, hi⟩
    · exact le_rfl
  obtain ⟨_, hbest, hnewBench, _⟩ := growthStep_correct table oldOwner hOwner selected hcard returned.assigned
    hstrict hwhole old returned.point benchmark hold holdCap hOldEF hOldTarget
    (fun p => (hreturn.1 p).1) (fun p => (hreturn.1 p).2) hreturn.2.1 hbench houtBench hreturn.2.2.2
  have hEF : ∀ i j : enlarged, value i.val (growth.assigned j) (returned.point (growth.assigned j)) ≤
      value i.val (growth.assigned i) (returned.point (growth.assigned i)) :=
    fun i j => hbest i (growth.assigned j)
  obtain ⟨hvalid, _, hown, hEF', hunused⟩ := refresh_inherited enlarged growth.assigned value feasible
    returned.point (table.remainingCap selected) (table.remainingCap enlarged)
    (fun p => (hreturn.1 p).1) (fun p => (table.cap_feasible hwhole enlarged p).1)
    (fun p => (hreturn.1 p).2) (fun p => table.cap_mono hwhole selected enlarged (Finset.subset_insert _ _) p) hEF
  refine ⟨hvalid, ?_, hEF', hunused⟩
  intro i
  change target i.val ≤ value i.val (growth.assigned i)
    (refreshUnused enlarged growth.assigned returned.point (table.remainingCap enlarged) (growth.assigned i))
  rw [hown i]
  exact (htargetBench i.val).trans (hnewBench i)

/-- `recurse` is the not-yet-closed smaller-population procedure. This loop
definition does not assume fairness of its answers; semantic correctness must
discharge the smaller-call invariant separately. -/
def loopProgram {Query Reply : Type*} (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, Node selected Parent Coord → Program Query Reply (Node selected Parent Coord)) :
    ℕ → LoopState Agent Parent Coord → Program Query Reply (LoopState Agent Parent Coord)
  | fuel, s => if s.selected.card = Fintype.card Parent then .returned s else
      match fuel with
      | 0 => .failed
      | fuel + 1 => if hcard : s.selected.card < Fintype.card Parent then
          (recurse s.selected s.node).bind (fun returned =>
            loopProgram table oldOwner hOwner recurse fuel (nextLoopState table oldOwner hOwner s.selected hcard returned))
        else .failed

/-- There is no last recursive call after every contested parent is assigned. -/
theorem loopProgram_full {Query Reply : Type*} (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, Node selected Parent Coord → Program Query Reply (Node selected Parent Coord))
    (fuel : ℕ) (s : LoopState Agent Parent Coord) (hfull : s.selected.card = Fintype.card Parent) :
    loopProgram table oldOwner hOwner recurse fuel s = .returned s := by
  cases fuel <;> simp only [loopProgram, ite_eq_left hfull]

def loopBudget (bound : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, count + 1 => bound start + loopBudget bound (start + 1) count

/-- A full injective assignment turns inherited pairwise EF into comparison
with every contested parent, without an extra same-size recursive call. -/
theorem inherited_full_best (table : TrimTable value feasible whole target) (s : LoopState Agent Parent Coord)
    (h : Inherited table s) (hfull : s.selected.card = Fintype.card Parent) :
    ∀ i : s.selected, ∀ p, value i.val p (s.node.point p) ≤ ownValue s.selected s.node value i := by
  have hsurj : Function.Surjective s.node.assigned := by
    by_contra hs
    have hlt := Fintype.card_lt_of_injective_not_surjective s.node.assigned s.node.assigned.injective hs
    simp only [Fintype.card_coe, hfull, lt_self_iff_false] at hlt
  intro i p
  obtain ⟨j, rfl⟩ := hsurj p
  exact h.2.2.1 i j

/-- Compositional loop correctness under the explicit induction hypothesis
for smaller participant counts. This is a helper for the still-open whole
SubCore recursion: `hcall` must be discharged, not postulated as an EF oracle. -/
theorem loop_executes_of_smaller_calls {Query Reply : Type*}
    (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (hstrict : ∀ i p, StrictMonoOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (old : Parent → Coord) (hold : ∀ p, old p ∈ feasible) (holdCap : ∀ p, old p ≤ whole p)
    (hOldEF : ∀ p q, value (oldOwner p) q (old q) ≤ value (oldOwner p) p (old p))
    (hOldTarget : ∀ p, target (oldOwner p) ≤ value (oldOwner p) p (old p))
    (recurse : ∀ selected : Finset Agent, Node selected Parent Coord → Program Query Reply (Node selected Parent Coord))
    (oracle : AdaptiveOracle.Policy Query Reply) (isCut : Query → Bool) (queryBound cutBound : ℕ → ℕ)
    (hcall : ∀ s : LoopState Agent Parent Coord, Inherited table s → s.selected.card < Fintype.card Parent →
      ∀ prior : OracleProtocol.History Query Reply,
      ∃ returned : Node s.selected Parent Coord, ∃ trace : OracleProtocol.History Query Reply,
        Executes oracle (recurse s.selected s.node) prior returned trace ∧ RecursiveCorrect table s.selected s.node returned ∧
        trace.length ≤ queryBound s.selected.card ∧ trace.countP (fun qr => isCut qr.1) ≤ cutBound s.selected.card)
    (fuel : ℕ) (s : LoopState Agent Parent Coord) (hs : Inherited table s)
    (hsize : s.selected.card + fuel = Fintype.card Parent) (prior : OracleProtocol.History Query Reply) :
    ∃ out : LoopState Agent Parent Coord, ∃ trace : OracleProtocol.History Query Reply,
      Executes oracle (loopProgram table oldOwner hOwner recurse fuel s) prior out trace ∧
      Inherited table out ∧ out.selected.card = Fintype.card Parent ∧
      trace.length ≤ loopBudget queryBound s.selected.card fuel ∧
      trace.countP (fun qr => isCut qr.1) ≤ loopBudget cutBound s.selected.card fuel := by
  induction fuel generalizing s prior with
  | zero =>
    have hfull : s.selected.card = Fintype.card Parent := by simpa only [Nat.add_zero] using hsize
    refine ⟨s, [], ?_, hs, hfull, Nat.zero_le _, Nat.zero_le _⟩
    rw [loopProgram_full table oldOwner hOwner recurse 0 s hfull]
    exact Executes.returned _ _
  | succ fuel ih =>
    have hcard : s.selected.card < Fintype.card Parent := by omega
    have hnotfull : s.selected.card ≠ Fintype.card Parent := Nat.ne_of_lt hcard
    obtain ⟨returned, first, hfirst, hreturn, hfirstQ, hfirstC⟩ := hcall s hs hcard prior
    let next := nextLoopState table oldOwner hOwner s.selected hcard returned
    have hnext : Inherited table next := nextLoopState_inherited table oldOwner hOwner hstrict hwhole old
      hold holdCap hOldEF hOldTarget s.selected hcard s.node returned hs hreturn
    have hnextCard : next.selected.card = s.selected.card + 1 := nextLoopState_card table oldOwner hOwner s.selected hcard returned
    have hnextSize : next.selected.card + fuel = Fintype.card Parent := by rw [hnextCard]; omega
    obtain ⟨out, tail, htail, hout, hfull, htailQ, htailC⟩ := ih next hnext hnextSize (prior ++ first)
    refine ⟨out, first ++ tail, ?_, hout, hfull, ?_, ?_⟩
    · rw [loopProgram, ite_eq_right hnotfull, dite_eq_left hcard]
      exact hfirst.bind _ htail
    · rw [List.length_append, loopBudget]
      rw [hnextCard] at htailQ
      exact Nat.add_le_add hfirstQ htailQ
    · rw [List.countP_append, loopBudget]
      rw [hnextCard] at htailC
      exact Nat.add_le_add hfirstC htailC

end EnvyFreeResearch.Full.Chores.SubCore
