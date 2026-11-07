import EnvyFreeResearch.R6Core

/-!
# Round 7 exact finite Core compression counterexamples

The coefficients are strictly positive linear parent costs. The results refute
specific fixed-order and rectangular-state rules, not every base-two algorithm.
-/

noncomputable section

namespace EnvyFreeResearch.R7Core

def orderCoefficient : Fin 3 → Fin 3 → ℝ := ![![3,1,3], ![2,1,2], ![1,1,1]]
def canonicalEndpoint : Fin 3 → ℝ := ![1/2,1,1/2]
def canonicalOwn : Fin 3 → ℝ := ![1,1,1/2]
def canonicalMatching : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem order_coefficients_positive (i p : Fin 3) : 0 < orderCoefficient i p := by
  fin_cases i <;> fin_cases p <;> norm_num [orderCoefficient]

theorem canonical_own_cost (i : Fin 3) :
    orderCoefficient i (canonicalMatching i)*canonicalEndpoint (canonicalMatching i)=
      canonicalOwn i := by
  fin_cases i <;> norm_num [orderCoefficient, canonicalEndpoint, canonicalOwn, canonicalMatching,
    Equiv.swap_apply_def]

theorem canonical_envy_free (i p : Fin 3) :
    canonicalOwn i ≤ orderCoefficient i p*canonicalEndpoint p := by
  fin_cases i <;> fin_cases p <;> norm_num [orderCoefficient, canonicalEndpoint, canonicalOwn]

/-- The explicit anchored state bounds every feasible EF endpoint vector, not just enumerated trials. -/
theorem fixed_order_canonical_bound (y : Fin 3 → ℝ) (assignment : Equiv.Perm (Fin 3))
    (hcap : ∀ p, y p ≤ 1)
    (hEF : ∀ i p, orderCoefficient i (assignment i)*y (assignment i) ≤
      orderCoefficient i p*y p) : ∀ p, y p ≤ canonicalEndpoint p := by
  apply R6Core.anchored_prefix_maximality
    (fun i p t => orderCoefficient i p*t) canonicalEndpoint y (fun _ => 1)
    canonicalOwn (fun i => orderCoefficient i (assignment i)*y (assignment i))
    canonicalMatching assignment (fun i => i.val) (fun i => i=0)
  · intro i p a b hab
    exact mul_lt_mul_of_pos_left hab (order_coefficients_positive i p)
  · exact canonical_own_cost
  · intro i
    rfl
  · exact canonical_envy_free
  · exact hEF
  · intro i
    fin_cases i
    · exact Or.inl rfl
    · refine Or.inr ⟨0, by decide, ?_⟩
      norm_num [orderCoefficient, canonicalEndpoint, canonicalOwn, canonicalMatching]
    · refine Or.inr ⟨1, by decide, ?_⟩
      norm_num [orderCoefficient, canonicalEndpoint, canonicalOwn, canonicalMatching]
  · intro i hi
    subst i
    norm_num [canonicalEndpoint, canonicalMatching]
  · exact hcap

theorem only_middle_can_be_whole (y : Fin 3 → ℝ) (p : Fin 3)
    (hbound : ∀ q, y q ≤ canonicalEndpoint q) (hwhole : y p=1) : p=1 := by
  have h := hbound p
  fin_cases p <;> norm_num [canonicalEndpoint, hwhole] at * <;> linarith

theorem first_row_off_middle (p : Fin 3) (hp : p ≠ 1) : orderCoefficient 0 p=3 := by
  fin_cases p <;> norm_num [orderCoefficient] at *

theorem second_row_off_middle (p : Fin 3) (hp : p ≠ 1) : orderCoefficient 1 p=2 := by
  fin_cases p <;> norm_num [orderCoefficient] at *

/-- Every whole assigned prefix in every EF state belongs to agent zero. -/
theorem only_agent_zero_owns_whole (y : Fin 3 → ℝ) (assignment : Equiv.Perm (Fin 3))
    (hcap : ∀ p, y p ≤ 1)
    (hEF : ∀ i p, orderCoefficient i (assignment i)*y (assignment i) ≤
      orderCoefficient i p*y p) (i : Fin 3) (hwhole : y (assignment i)=1) : i=0 := by
  have hbound := fixed_order_canonical_bound y assignment hcap hEF
  have hmiddle := only_middle_can_be_whole y (assignment i) hbound hwhole
  have hy1 : y 1=1 := by simpa only [hmiddle] using hwhole
  fin_cases i
  · rfl
  · change assignment 1=1 at hmiddle
    have hnot : assignment 0 ≠ 1 := by
      intro h
      have heq : assignment 0=assignment 1 := h.trans hmiddle.symm
      have hbad := assignment.injective heq
      norm_num at hbad
    have h0 := hEF 0 1
    have h1 := hEF 1 (assignment 0)
    rw [first_row_off_middle _ hnot] at h0
    rw [hmiddle, second_row_off_middle _ hnot] at h1
    norm_num [orderCoefficient, hy1] at h0 h1
    linarith
  · change assignment 2=1 at hmiddle
    have h := hEF 2 0
    rw [hmiddle] at h
    have hb := hbound 0
    norm_num [orderCoefficient, canonicalEndpoint, hy1] at h hb
    linarith

/-- Since an anchored construction starts whole, either of the other prescribed first agents fails. -/
theorem fixed_first_agent_obstruction (y : Fin 3 → ℝ) (assignment : Equiv.Perm (Fin 3))
    (hcap : ∀ p, y p ≤ 1)
    (hEF : ∀ i p, orderCoefficient i (assignment i)*y (assignment i) ≤
      orderCoefficient i p*y p) (first : Fin 3) (hfirst : first ≠ 0) :
    y (assignment first) ≠ 1 := by
  intro hwhole
  exact hfirst (only_agent_zero_owns_whole y assignment hcap hEF first hwhole)

def rectangularCoefficient : Fin 3 → ℝ := ![1,2,2]
def rectangularX : Fin 3 → ℝ := ![1,1/2,1]
def rectangularY : Fin 3 → ℝ := ![1,1,1/2]

theorem rectangular_X_neat (p : Fin 3) :
    1 ≤ rectangularCoefficient p*rectangularX p := by
  fin_cases p <;> norm_num [rectangularCoefficient, rectangularX]

theorem rectangular_Y_neat (p : Fin 3) :
    1 ≤ rectangularCoefficient p*rectangularY p := by
  fin_cases p <;> norm_num [rectangularCoefficient, rectangularY]

theorem rectangular_assigned_costs :
    rectangularCoefficient 0*rectangularX 0=1 ∧
    rectangularCoefficient 1*rectangularX 1=1 ∧
    rectangularCoefficient 0*rectangularY 0=1 ∧
    rectangularCoefficient 2*rectangularY 2=1 := by
  norm_num [rectangularCoefficient, rectangularX, rectangularY]

theorem rectangular_partial_assignments_injective :
    Function.Injective (![0,1] : Fin 2 → Fin 3) ∧
      Function.Injective (![0,2] : Fin 2 → Fin 3) := by
  constructor <;> intro i j h <;> fin_cases i <;> fin_cases j <;> norm_num at *

theorem rectangular_join_is_whole (p : Fin 3) : max (rectangularX p) (rectangularY p)=1 := by
  fin_cases p <;> norm_num [rectangularX, rectangularY]

theorem rectangular_unique_minimum (p : Fin 3) (hcost : rectangularCoefficient p ≤ 1) : p=0 := by
  fin_cases p <;> norm_num [rectangularCoefficient] at *

/-- The two old identical observers cannot be injected into distinct minimizing whole parents. -/
theorem rectangular_join_has_no_matching :
    ¬∃ assignment : Fin 2 → Fin 3, Function.Injective assignment ∧
      ∀ i p, rectangularCoefficient (assignment i) ≤ rectangularCoefficient p := by
  rintro ⟨assignment, hinj, hEF⟩
  have h0 : assignment 0=0 := rectangular_unique_minimum _ (by simpa [rectangularCoefficient] using hEF 0 0)
  have h1 : assignment 1=0 := rectangular_unique_minimum _ (by simpa [rectangularCoefficient] using hEF 1 0)
  have hbad := hinj (h0.trans h1.symm)
  norm_num at hbad

def extensionCoefficient : Fin 3 → Fin 3 → ℝ := ![![1,2,2], ![1,2,2], ![1,1,100]]
def extensionMatching : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Y has an actual complete EF extension for the future row (1,1,100). -/
theorem rectangular_Y_extends (i p : Fin 3) :
    extensionCoefficient i (extensionMatching i)*rectangularY (extensionMatching i) ≤
      extensionCoefficient i p*rectangularY p := by
  fin_cases i <;> fin_cases p <;>
    norm_num [extensionCoefficient, extensionMatching, rectangularY, Equiv.swap_apply_def]

/-- Keeping X fixes the two old parents; no remaining prefix can satisfy both old and new EF. -/
theorem rectangular_X_cannot_extend (t : ℝ) : ¬((1 : ℝ) ≤ 2*t ∧ 100*t ≤ 1/2) := by
  rintro ⟨hOld, hNew⟩
  linarith

/-- Unfolding the actual three-agent table yields the same impossible completion inequalities. -/
theorem rectangular_X_no_EF_completion (t : ℝ) :
    ¬∀ i p : Fin 3, extensionCoefficient i i*(![1,1/2,t] : Fin 3 → ℝ) i ≤
      extensionCoefficient i p*(![1,1/2,t] : Fin 3 → ℝ) p := by
  intro hEF
  have hOld := hEF 0 2
  have hNew := hEF 2 1
  norm_num [extensionCoefficient] at hOld hNew
  exact rectangular_X_cannot_extend t ⟨hOld, hNew⟩

end EnvyFreeResearch.R7Core

#print axioms EnvyFreeResearch.R7Core.fixed_order_canonical_bound
#print axioms EnvyFreeResearch.R7Core.only_agent_zero_owns_whole
#print axioms EnvyFreeResearch.R7Core.fixed_first_agent_obstruction
#print axioms EnvyFreeResearch.R7Core.rectangular_join_has_no_matching
#print axioms EnvyFreeResearch.R7Core.rectangular_Y_extends
#print axioms EnvyFreeResearch.R7Core.rectangular_X_cannot_extend
#print axioms EnvyFreeResearch.R7Core.rectangular_X_no_EF_completion
