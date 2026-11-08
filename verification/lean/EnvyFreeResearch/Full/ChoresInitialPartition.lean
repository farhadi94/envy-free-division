import EnvyFreeResearch.Full.ChoresPrefixValues

/-!
# Initial equal-cutter partition by actual ordinary queries

The initial costs are obtained by one Eval per observer. Each subsequent
parent is cut from the remaining physical interval and recorded for all
observers. The last parent's costs are obtained by subtraction from the
already recorded remaining costs. All reply choices may depend on the full
enclosing history.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.InitialPartition

open Set OracleProtocol IntervalOracle QueryProgram

structure Parent (n : ℕ) where
  left : ℝ
  right : ℝ
  value : Fin n → ℝ

/-- Literal adjacent intervals, with the exact physical cost of every parent
recorded for every observer. -/
def Chain {n : ℕ} (P : Profile (Fin n)) : ℝ → ℝ → List (Parent n) → Prop
  | a, b, [] => a = b
  | a, b, p :: rest => p.left = a ∧ a ≤ p.right ∧ p.right ≤ b ∧
      (∀ i, p.value i = P.cumulative i p.right - P.cumulative i p.left) ∧
      Chain P p.right b rest

def valuesProgram {n : ℕ} (a b : ℝ) : List (Fin n) → Program (Query (Fin n)) ℝ (Fin n → ℝ)
  | [] => .returned (fun _ => 0)
  | i :: rest => .ask (.eval i a b) (fun r => (valuesProgram a b rest).bind
      (fun values => .returned (Function.update values i r)))

theorem values_program_correct {n : ℕ} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1) (agents : List (Fin n))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ values : Fin n → ℝ, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (valuesProgram a b agents) prior values trace ∧
      trace.length = agents.length ∧ trace.countP (fun qr => isCutQuery qr.1) = 0 ∧
      ∀ i ∈ agents, values i = P.cumulative i b - P.cumulative i a := by
  induction agents generalizing prior with
  | nil => exact ⟨fun _ => 0, [], Executes.returned _ _, rfl, rfl, by simp⟩
  | cons i rest ih =>
    let q := Query.eval i a b
    let r := AdaptiveOracle.answer oracle prior q
    obtain ⟨hr, hvalue⟩ := AdaptiveOracle.answer_spec P oracle hpolicy prior q hbound
    obtain ⟨values, trace, hexec, hlen, hcuts, hvalues⟩ := ih (prior ++ [(q, r)])
    have htail : Executes oracle ((valuesProgram a b rest).bind
        (fun values => .returned (Function.update values i r))) (prior ++ [(q, r)])
        (Function.update values i r) trace := by
      simpa only [List.append_nil] using hexec.bind
        (fun values => Program.returned (Function.update values i r)) (Executes.returned _ _)
    refine ⟨Function.update values i r, (q, r) :: trace,
      Executes.ask q _ prior r _ trace hr htail, ?_, ?_, ?_⟩
    · simp only [List.length_cons, hlen]
    · simpa only [List.countP_cons, q, isCutQuery, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hcuts
    · intro j hj
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self, ValidReply, q, r] using hvalue
      · rw [Function.update_of_ne hji]
        exact hvalues j ((List.mem_cons.mp hj).resolve_left hji)

/-- The existing endpoint recorder embedded with the complete prior history. -/
def endpointProgram {n : ℕ} (c : Fin n) (a b t : ℝ) : Program (Query (Fin n)) ℝ (EndpointRecord n) :=
  ofProtocol (endpointProtocol c a b t) n []

theorem endpoint_program_correct {n : ℕ} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (a b t : ℝ) (hlegal : Legal P (.cut c a b t))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ record : EndpointRecord n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (endpointProgram c a b t) prior record trace ∧
      trace.length = n ∧ trace.countP (fun qr => isCutQuery qr.1) = 1 ∧
      record.point ∈ Icc a b ∧
      (∀ j, record.value j = P.cumulative j record.point - P.cumulative j a) ∧ record.value c = t := by
  let shifted := fun history => oracle (prior ++ history)
  have hshifted : AdaptiveOracle.IsLegalPolicy P shifted := fun history => hpolicy (prior ++ history)
  obtain ⟨record, hreturn, hlen, hcuts, hpoint, hvalue, hc⟩ :=
    endpoint_protocol_correct P shifted hshifted c a b t hlegal
  exact ⟨record, _, by simpa only [endpointProgram, List.append_nil] using
    ofProtocol_executes (endpointProtocol c a b t) oracle prior n [] record hreturn,
    hlen, hcuts, hpoint, hvalue, hc⟩

/-- There are `k` physical Cuts for `k+1` parents; the final parent uses cached
subtraction and requires no further query. -/
def cutParentsProgram {n : ℕ} (c : Fin n) (t : ℝ) :
    ℕ → ℝ → ℝ → (Fin n → ℝ) → Program (Query (Fin n)) ℝ (List (Parent n))
  | 0, a, b, remaining => .returned [⟨a, b, remaining⟩]
  | k + 1, a, b, remaining => (endpointProgram c a b t).bind (fun record =>
      (cutParentsProgram c t k record.point b (fun i => remaining i - record.value i)).bind
        (fun parents => .returned (⟨a, record.point, record.value⟩ :: parents)))

/-- Every target is legal, all cached costs are exact, and the concrete trace
contains precisely the promised Cuts and recording Evals. -/
theorem cut_parents_program_correct {n : ℕ} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (a b : ℝ)
    (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1) (remaining : Fin n → ℝ)
    (hremaining : ∀ i, remaining i = P.cumulative i b - P.cumulative i a)
    (hc : remaining c = (k + 1 : ℕ) * t) (prior : History (Query (Fin n)) ℝ) :
    ∃ parents : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (cutParentsProgram c t k a b remaining) prior parents trace ∧
      trace.length = n * k ∧ trace.countP (fun qr => isCutQuery qr.1) = k ∧
      parents.length = k + 1 ∧ Chain P a b parents ∧ ∀ p ∈ parents, p.value c = t := by
  induction k generalizing a remaining prior with
  | zero =>
    refine ⟨[⟨a, b, remaining⟩], [], Executes.returned _ _, by simp, rfl, rfl,
      ⟨rfl, hbound.2.1, le_rfl, hremaining, rfl⟩, ?_⟩
    intro p hp
    have hp' : p = ⟨a, b, remaining⟩ := List.mem_singleton.mp hp
    subst p
    simpa only [Nat.zero_add, Nat.cast_one, one_mul] using hc
  | succ k ih =>
    have htotal : t ≤ P.cumulative c b - P.cumulative c a := by
      rw [← hremaining c, hc]
      have hk : (1 : ℝ) ≤ (k + 1 + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 + 1 by omega)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk ht
    have hlegal : Legal P (.cut c a b t) := by
      refine ⟨hbound.1, hbound.2.1, hbound.2.2, ?_⟩
      have htotal0 : 0 ≤ P.cumulative c b - P.cumulative c a := ht.trans htotal
      simpa only [ExtremalRoots.LegalTarget, min_eq_left htotal0, max_eq_right htotal0] using And.intro ht htotal
    obtain ⟨record, first, hfirst, hfirstlen, hfirstcuts, hx, hvalues, hct⟩ :=
      endpoint_program_correct P oracle hpolicy c a b t hlegal prior
    have hrest : ∀ i, remaining i - record.value i = P.cumulative i b - P.cumulative i record.point := by
      intro i
      rw [hremaining i, hvalues i]
      ring
    have hc' : remaining c - record.value c = (k + 1 : ℕ) * t := by
      rw [hc, hct]
      push_cast
      ring
    obtain ⟨parents, tail, htail, htaillen, htailcuts, hparentslen, hchain, hequal⟩ :=
      ih record.point ⟨hbound.1.trans hx.1, hx.2, hbound.2.2⟩
        (fun i => remaining i - record.value i) hrest hc' (prior ++ first)
    let output : List (Parent n) := ⟨a, record.point, record.value⟩ :: parents
    have htail' : Executes oracle ((cutParentsProgram c t k record.point b
        (fun i => remaining i - record.value i)).bind
        (fun parents => .returned (⟨a, record.point, record.value⟩ :: parents)))
        (prior ++ first) output tail := by
      simpa only [List.append_nil] using htail.bind
        (fun parents => Program.returned (⟨a, record.point, record.value⟩ :: parents))
        (Executes.returned output _)
    refine ⟨output, first ++ tail, hfirst.bind _ htail', ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, hfirstlen, htaillen]
      ring
    · simp only [List.countP_append, hfirstcuts, htailcuts]
      omega
    · simp only [output, List.length_cons, hparentslen]
    · exact ⟨rfl, hx.1, hx.2, hvalues, hchain⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hct
      · exact hequal p hp

inductive Outcome (n : ℕ)
  | zero (agent : Fin n)
  | partition (total : Fin n → ℝ) (parents : List (Parent n))

def allAgents (n : ℕ) : List (Fin n) := by classical exact Finset.univ.toList

/-- The zero-total exit is selected solely from actual returned Eval answers.
Otherwise the cutter makes the equal partition, with every observer recorded. -/
def initialProgram {n : ℕ} (c : Fin n) (a b : ℝ) : Program (Query (Fin n)) ℝ (Outcome n) := by
  classical
  exact (valuesProgram a b (allAgents n)).bind (fun total =>
    if h : ∃ i, total i = 0 then .returned (.zero (Classical.choose h))
    else (cutParentsProgram c (total c / n) (n - 1) a b total).bind
      (fun parents => .returned (.partition total parents)))

def Correct {n : ℕ} (P : Profile (Fin n)) (c : Fin n) (a b : ℝ) : Outcome n → Prop
  | .zero i => P.cumulative i b - P.cumulative i a = 0
  | .partition total parents =>
      (∀ i, total i = P.cumulative i b - P.cumulative i a) ∧
      (∀ i, 0 < total i) ∧ parents.length = n ∧ Chain P a b parents ∧
      ∀ p ∈ parents, p.value c = total c / n

/-- Exact initial physical construction, including the zero-total exit. The
bound `n²` includes all initial Evals and all endpoint recording; the last
parent is never queried merely to recover already cached values. -/
theorem initial_program_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ outcome : Outcome n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (initialProgram c a b) prior outcome trace ∧
      trace.length ≤ n ^ 2 ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ n - 1 ∧
      Correct P c a b outcome := by
  classical
  have hn : 0 < n := Fin.pos c
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  obtain ⟨total, first, hfirst, hfirstlen, hfirstcuts, htotal⟩ :=
    values_program_correct P oracle hpolicy a b hbound (allAgents n) prior
  have hvalues : ∀ i, total i = P.cumulative i b - P.cumulative i a := by
    intro i
    exact htotal i (by simp [allAgents])
  have hfirstlen' : first.length = n := by simpa [allAgents] using hfirstlen
  have hnonneg : ∀ i, 0 ≤ total i := by
    intro i
    rw [hvalues i]
    exact sub_nonneg.mpr (hmono i hbound.2.1)
  by_cases hzero : ∃ i, total i = 0
  · let outcome : Outcome n := .zero (Classical.choose hzero)
    have hfinish : Executes oracle
        (if h : ∃ i, total i = 0 then Program.returned (Outcome.zero (Classical.choose h))
          else (cutParentsProgram c (total c / n) (n - 1) a b total).bind
            (fun parents => .returned (.partition total parents)))
        (prior ++ first) outcome [] := by
      rw [dite_eq_left hzero]
      exact Executes.returned _ _
    refine ⟨outcome, first, ?_, ?_, ?_, ?_⟩
    · simpa only [initialProgram, List.append_nil] using hfirst.bind
        (fun total => if h : ∃ i, total i = 0 then Program.returned (Outcome.zero (Classical.choose h))
          else (cutParentsProgram c (total c / n) (n - 1) a b total).bind
            (fun parents => .returned (Outcome.partition total parents))) hfinish
    · rw [hfirstlen', pow_two]
      exact Nat.le_mul_self n
    · rw [hfirstcuts]
      exact Nat.zero_le _
    · change P.cumulative (Classical.choose hzero) b - P.cumulative (Classical.choose hzero) a = 0
      rw [← hvalues]
      exact Classical.choose_spec hzero
  · have hpositive : ∀ i, 0 < total i := fun i =>
      lt_of_le_of_ne (hnonneg i) (Ne.symm (fun h => hzero ⟨i, h⟩))
    have ht : 0 ≤ total c / (n : ℝ) := div_nonneg (hnonneg c) (Nat.cast_nonneg n)
    have hc : total c = (n - 1 + 1 : ℕ) * (total c / (n : ℝ)) := by
      rw [hn1]
      exact (mul_div_cancel₀ (total c) (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℝ) ≠ 0)).symm.trans
        (by ring)
    obtain ⟨parents, tail, htail, htaillen, htailcuts, hparentslen, hchain, hequal⟩ :=
      cut_parents_program_correct P oracle hpolicy c (total c / n) ht (n - 1) a b
        hbound total hvalues hc (prior ++ first)
    let outcome : Outcome n := .partition total parents
    have hfinish : Executes oracle
        (if h : ∃ i, total i = 0 then Program.returned (Outcome.zero (Classical.choose h))
          else (cutParentsProgram c (total c / n) (n - 1) a b total).bind
            (fun parents => .returned (.partition total parents)))
        (prior ++ first) outcome tail := by
      rw [dite_eq_right hzero]
      simpa only [List.append_nil] using htail.bind
        (fun parents => Program.returned (Outcome.partition total parents)) (Executes.returned outcome _)
    refine ⟨outcome, first ++ tail, hfirst.bind _ hfinish, ?_, ?_,
      hvalues, hpositive, hparentslen.trans hn1, hchain, hequal⟩
    · rw [List.length_append, hfirstlen', htaillen]
      have heq : n + n * (n - 1) = n ^ 2 := by
        calc
          n + n * (n - 1) = n * (n - 1 + 1) := by ring
          _ = n ^ 2 := by rw [hn1, pow_two]
      exact heq.le
    · simp only [List.countP_append, hfirstcuts, htailcuts, Nat.zero_add, le_refl]

end EnvyFreeResearch.Full.Chores.InitialPartition
