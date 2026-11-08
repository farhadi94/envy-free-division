import EnvyFreeResearch.Full.ChoresMainUnitAllocation

/-! Public no-cache unit-interval entry point. The native Specification is
an explicit obligation for the main scheduler/recursion, not assumed solved. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.UnitEntry
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion Completion QueryProgram
open scoped Classical
variable {n : ℕ}

def program (owner : Fin n)
    (native : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin n))) :
    Program (Query (Fin n)) ℝ (Output n) :=
  (initialCacheProgram n).bind (fun cache => (native cache).bind
    (fun allocation => .returned ⟨allocation,owner⟩))

theorem execution_legal {A : Type*} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    {p : Program (Query (Fin n)) ℝ A} {prior : History (Query (Fin n)) ℝ}
    {out : A} {trace : History (Query (Fin n)) ℝ} (he : Executes oracle p prior out trace) :
    ∀ qr ∈ trace, Legal P qr.1 ∧ ValidReply P qr.1 qr.2 := by
  induction he with
  | returned a history => simp
  | ask q next history reply a tail hreply hnext ih =>
    intro qr hqr
    rcases List.mem_cons.mp hqr with rfl | hm
    · exact (hpolicy history).sound q reply hreply
    · exact ih qr hm

theorem program_correct (cost : Population.Costs n) (owner : Fin n)
    (native : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin n)))
    (Q C : ℕ) (hnative : Population.Specification cost id native Q C)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (program owner native) prior out trace ∧
      trace.length ≤ n+Q ∧ virtualCuts trace ≤ C ∧ out.zeroOwner=owner ∧
      out.allocation.Sound cost.measure id (Ioc 0 1) ∧
      (∀ qr ∈ trace, Legal (measureProfile cost.measure) qr.1 ∧
        ValidReply (measureProfile cost.measure) qr.1 qr.2) := by
  obtain ⟨cache,t1,h1,hQ1,hC1,hcache⟩ :=
    initial_cache_correct (measureProfile cost.measure) oracle hpolicy prior
  have hcache' : CacheValid (measureProfile cost.measure) (material cache) cache :=
    ⟨hcache.1,hcache.2.1,rfl⟩
  obtain ⟨allocation,t2,h2,hQ2,hC2,hs,hscope,hknown⟩ := hnative cache hcache' oracle hpolicy (prior++t1)
  have h2' := h2.bind (fun allocation => Program.returned (⟨allocation,owner⟩ : Output n))
    (Executes.returned _ ((prior++t1)++t2))
  have he : Executes oracle (program owner native) prior ⟨allocation,owner⟩ (t1++t2) := by
    simpa only [program,List.append_nil] using h1.bind
      (fun cache => (native cache).bind (fun allocation => Program.returned (⟨allocation,owner⟩ : Output n))) h2'
  refine ⟨⟨allocation,owner⟩,t1++t2,he,?_,?_,rfl,?_,execution_legal _ oracle hpolicy he⟩
  · rw [List.length_append,hQ1]
    exact Nat.add_le_add_left hQ2 n
  · change (t1++t2).countP (fun qr => isCutQuery qr.1) ≤ C
    rw [List.countP_append]
    change virtualCuts t1+virtualCuts t2 ≤ C
    simpa only [hC1,zero_add] using hC2
  · simpa only [hcache.2.2] using hs

theorem unit_complete_protocol (cost : Population.Costs n) (owner : Fin n)
    (native : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin n)))
    (Q C : ℕ) (hnative : Population.Specification cost id native Q C)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle) :
    ∃ out trace,
      AdaptiveOracle.run (program owner native).protocol oracle () (n+Q) []=⟨trace,.returned out⟩ ∧
      trace.length ≤ n+Q ∧ virtualCuts trace ≤ C ∧
      Pairwise (fun i j => Disjoint (out.share i) (out.share j)) ∧
      (⋃ i, out.share i)=Icc 0 1 ∧
      (∀ i j, (cost.measure i).real (out.share i) ≤ (cost.measure i).real (out.share j)) ∧
      (∀ i, MeasurableSet (out.share i)) ∧
      (∀ i p, p ∈ out.allocation.pieces i → 0 ≤ p.left ∧ p.left ≤ p.right ∧ p.right ≤ 1) ∧
      (∀ qr ∈ trace, Legal (measureProfile cost.measure) qr.1 ∧
        ValidReply (measureProfile cost.measure) qr.1 qr.2) := by
  obtain ⟨out,trace,he,hQ,hC,howner,hs,hlegal⟩ := program_correct cost owner native Q C hnative oracle hpolicy []
  exact ⟨out,trace,he.run (n+Q) hQ,hQ,hC,share_disjoint cost.measure out hs,
    share_cover cost.measure out hs,share_envy_free cost.measure out hs,
    share_measurable out,interval_bounds cost.measure out hs,hlegal⟩
end EnvyFreeResearch.Full.Chores.UnitEntry
