import EnvyFreeResearch.Full.ChoresComponentBoundaryRecord

/-! Actual initial parent boundaries come only from the input interval and
replies to its physical equal-cutter requests. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent
open scoped Classical

variable {n : ℕ}

def ParentKnown (points : Set ℝ) (p : Parent n) : Prop := p.left ∈ points ∧ p.right ∈ points

theorem cut_parents_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (target : ℝ) (k : ℕ) (a b : ℝ)
    (ha : a ∈ points) (hb : b ∈ points) (remaining : Fin n → ℝ)
    (prior : History (Query (Fin n)) ℝ) (out : List (Parent n))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (cutParentsProgram c target k a b remaining) prior out trace) :
    ∀ p ∈ out, ParentKnown (Known points trace) p := by
  induction k generalizing points a b remaining prior out trace with
  | zero =>
    cases h
    intro p hp
    have hp' : p = ⟨a, b, remaining⟩ := by simpa using hp
    subst p
    simpa only [ParentKnown, known_nil] using And.intro ha hb
  | succ k ih =>
    obtain ⟨record, first, second, hfirst, hrest, htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨parents, tail, empty, htail, hreturn, hsecond⟩ := Executes.split_bind _ _ hrest
    cases hreturn
    simp only [List.append_nil] at hsecond
    subst second
    subst trace
    have hpoint : record.point ∈ Known points first :=
      Or.inr (endpoint_from_trace oracle c a b target prior record first hfirst)
    have hparents := ih (Known points first) record.point b hpoint (Or.inl hb) _
      (prior ++ first) parents tail htail
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · constructor
      · exact known_mono points first tail (Or.inl ha)
      · exact known_mono points first tail hpoint
    · simpa only [known_append] using hparents p hp

def InitialKnown (points : Set ℝ) : InitialPartition.Outcome n → Prop
  | .zero _ => True
  | .partition _ parents => ∀ p ∈ parents, ParentKnown points p

theorem initial_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (a b : ℝ) (ha : a ∈ points) (hb : b ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : InitialPartition.Outcome n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (initialProgram c a b) prior out trace) :
    InitialKnown (Known points trace) out := by
  obtain ⟨total, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  by_cases hz : ∃ i, total i = 0
  · simp only [dite_eq_left hz] at hsecond
    cases hsecond
    trivial
  · simp only [dite_eq_right hz] at hsecond
    obtain ⟨parents, tail, empty, htail, hreturn, hsecond⟩ := Executes.split_bind _ _ hsecond
    cases hreturn
    simp only [List.append_nil] at hsecond
    subst second
    subst trace
    have hparents := cut_parents_known oracle (Known points first) c _ (n - 1) a b
      (Or.inl ha) (Or.inl hb) total (prior ++ first) parents tail htail
    simpa only [InitialKnown, known_append] using hparents

end EnvyFreeResearch.Full.Chores.Boundary
