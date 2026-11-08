import EnvyFreeResearch.Full.ChoresUnionQuery

/-! Refine a recorded finite union at any specified real coordinate using
at most one Eval per observer. This removes the need to assume that a
virtual protocol's query endpoints have already been recorded. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ}

def Contained (old fresh : List (Parent n)) : Prop :=
  ∀ q ∈ fresh, ∃ p ∈ old, p.left ≤ q.left ∧ q.right ≤ p.right

def alignProgram (x : ℝ) : List (Parent n) → Program (Query (Fin n)) ℝ (List (Parent n))
  | [] => .returned []
  | p::ps =>
    if p.left < x ∧ x < p.right then
      (valuesProgram p.left x (allAgents n)).bind (fun values =>
        .returned (leftPart p x values :: rightPart p x values :: ps))
    else (alignProgram x ps).bind (fun fresh => .returned (p::fresh))

theorem align_program_correct (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (x : ℝ) (ps : List (Parent n)) (hv : Valid P ps) (ho : Ordered ps)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (alignProgram x ps) prior fresh trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) = 0 ∧
      Valid P fresh ∧ Ordered fresh ∧ material fresh = material ps ∧
      Aligned fresh x ∧ Contained ps fresh ∧ fresh.length ≤ ps.length+1 := by
  induction ps generalizing prior with
  | nil => exact ⟨[],[],Executes.returned _ _,Nat.zero_le _,rfl,trivial,
      by simp [Ordered],rfl,by simp [Aligned],by simp [Contained],by simp⟩
  | cons p ps ih =>
    obtain ⟨hp,hps⟩ := hv
    obtain ⟨hbefore,horder⟩ := List.pairwise_cons.mp ho
    by_cases hx : p.left < x ∧ x < p.right
    · have hbound : 0 ≤ p.left ∧ p.left ≤ x ∧ x ≤ 1 :=
        ⟨hp.1.1,hx.1.le,hx.2.le.trans hp.1.2.2⟩
      obtain ⟨values,trace,hexec,hlen,hcuts,hvalues⟩ :=
        values_program_correct P oracle hpolicy p.left x hbound (allAgents n) prior
      have hlen' : trace.length = n := by simpa only [allAgents,Finset.length_toList,Finset.card_univ,Fintype.card_fin] using hlen
      have hvalues' : ∀ i, values i = P.cumulative i x-P.cumulative i p.left :=
        fun i => hvalues i (by simp [allAgents])
      have hvalid := split_parts_valid P hp x values ⟨hx.1.le,hx.2.le⟩ hvalues'
      have hsplit : PrefixSplit (p::ps) [leftPart p x values] (rightPart p x values::ps) :=
        PrefixSplit.cut p ps x values ⟨hx.1.le,hx.2.le⟩
      let fresh := leftPart p x values :: rightPart p x values :: ps
      refine ⟨fresh,trace,?_,hlen'.le,hcuts,⟨hvalid.1,hvalid.2,hps⟩,
        hsplit.ordered (List.pairwise_cons.mpr ⟨hbefore,horder⟩),?_,?_,?_,?_⟩
      · simpa only [alignProgram,ite_eq_left hx,List.append_nil] using hexec.bind
          (fun values => Program.returned (leftPart p x values::rightPart p x values::ps))
          (Executes.returned _ _)
      · simpa only [fresh,material,union_empty] using hsplit.cover
      · intro q hq
        rcases List.mem_cons.mp hq with heq | hq
        · subst q
          exact Or.inl le_rfl
        · rcases List.mem_cons.mp hq with heq | hq
          · subst q
            exact Or.inr le_rfl
          · exact Or.inr (hx.2.le.trans (hbefore q hq))
      · exact fun q hq => hsplit.component_contained hq
      · simp only [fresh,List.length_cons]
        omega
    · obtain ⟨fresh,trace,hexec,hlen,hcuts,hvalid,hordered,hmaterial,haligned,hcontained,hcount⟩ :=
        ih hps horder prior
      have hpx : p.right ≤ x ∨ x ≤ p.left := by
        by_cases hxr : p.right ≤ x
        · exact Or.inl hxr
        · exact Or.inr (le_of_not_gt (fun hl => hx ⟨hl,lt_of_not_ge hxr⟩))
      refine ⟨p::fresh,trace,?_,hlen,hcuts,⟨hp,hvalid⟩,?_,?_,?_,?_,?_⟩
      · simpa only [alignProgram,ite_eq_right hx,List.append_nil] using hexec.bind
          (fun fresh => Program.returned (p::fresh)) (Executes.returned _ _)
      · apply List.pairwise_cons.mpr
        refine ⟨?_,hordered⟩
        intro q hq
        obtain ⟨r,hr,hl,hu⟩ := hcontained q hq
        exact (hbefore r hr).trans hl
      · simp only [material,hmaterial]
      · intro q hq
        rcases List.mem_cons.mp hq with heq | hq
        · subst q
          exact hpx
        · exact haligned q hq
      · intro q hq
        rcases List.mem_cons.mp hq with heq | hq
        · subst q
          exact ⟨p,List.mem_cons_self,le_rfl,le_rfl⟩
        · obtain ⟨r,hr,hl,hu⟩ := hcontained q hq
          exact ⟨r,List.mem_cons_of_mem p hr,hl,hu⟩
      · simp only [List.length_cons]
        omega

theorem align_program_cache (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (U : Set ℝ) (x : ℝ) (ps : List (Parent n)) (hc : CacheValid P U ps)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (alignProgram x ps) prior fresh trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) = 0 ∧
      CacheValid P U fresh ∧ Aligned fresh x ∧
      (∀ y, Aligned ps y → Aligned fresh y) ∧ fresh.length ≤ ps.length+1 := by
  obtain ⟨fresh,trace,hexec,hlen,hcuts,hvalid,horder,hmaterial,halign,hcontained,hcount⟩ :=
    align_program_correct P oracle hpolicy x ps hc.1 hc.2.1 prior
  exact ⟨fresh,trace,hexec,hlen,hcuts,⟨hvalid,horder,hmaterial.trans hc.2.2⟩,
    halign,fun y hy => aligned_of_refinement hy hcontained,hcount⟩

end EnvyFreeResearch.Full.Chores.OrderedUnion
