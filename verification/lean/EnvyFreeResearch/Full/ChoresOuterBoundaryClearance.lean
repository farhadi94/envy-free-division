import EnvyFreeResearch.Full.ChoresOuterBoundaryGeneration
import EnvyFreeResearch.Full.ChoresClearanceProgram

/-! Coordinate provenance for the adaptive clearance loop, with every
triggered snapshot block executed at its actual accumulated history. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Equalizers Snapshot
open scoped Classical

variable {n : ℕ} {Index : Type*} [DecidableEq Index]
  (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)

include hn hpolicy

theorem generate_chain_of_executes (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (c : Fin n) (count : ℕ)
    (prior : History (Query (Fin n)) ℝ) (batch : Snapshot.Batch n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Snapshot.generate c count cache) prior batch trace) :
    Snapshot.Chain cost c U batch.snapshots batch.residue := by
  obtain ⟨actual,t,hexec,_,_,_,hchain⟩ := Snapshot.generate_correct hn cost oracle hpolicy U cache hc c count prior
  have hout := (hexec.deterministic h).1
  exact hout ▸ hchain

theorem clearance_known (entries : Index → Clearance.Entry n) (H : ℝ) (blockLength fuel : ℕ)
    (pending : List Index) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache)
    (points : Set ℝ) (hcache : CacheKnown points cache) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (prior : History (Query (Fin n)) ℝ) (batch : Snapshot.Batch n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Clearance.program entries H blockLength fuel pending cache) prior batch trace) :
    (∀ out ∈ batch.snapshots, SnapshotKnown (Known points trace) out) ∧
      CacheKnown (Known points trace) batch.residue ∧ Scoped points trace := by
  induction fuel generalizing pending U cache points prior batch trace with
  | zero =>
    cases h
    exact ⟨by simp,by simpa only [known_nil] using hcache,trivial⟩
  | succ fuel ih =>
    cases hfind : pending.find? (fun t => decide (Clearance.middle H (entries t) cache)) with
    | none =>
      rw [Clearance.program,hfind] at h
      cases h
      exact ⟨by simp,by simpa only [known_nil] using hcache,trivial⟩
    | some t =>
      rw [Clearance.program,hfind] at h
      obtain ⟨first,t₁,tail,hfirst,htail,htrace⟩ := Executes.split_bind _ _ h
      obtain ⟨rest,t₂,empty,hrest,hreturn,htailtrace⟩ := Executes.split_bind _ _ htail
      cases hreturn
      simp only [List.append_nil] at htailtrace
      subst tail
      subst trace
      obtain ⟨hknown₁,hcache₁,hscope₁⟩ := generate_known hn cost oracle hpolicy U cache hc points
        hcache hzero hone (entries t).observer blockLength prior first t₁ hfirst
      have hchain := generate_chain_of_executes hn cost oracle hpolicy U cache hc (entries t).observer
        blockLength prior first t₁ hfirst
      obtain ⟨hknown₂,hcache₂,hscope₂⟩ := ih (pending.erase t) (material first.residue)
        first.residue hchain.final_cache (Known points t₁) hcache₁ (Or.inl hzero) (Or.inl hone)
        (prior++t₁) rest t₂ hrest
      refine ⟨?_,?_,(scoped_append points t₁ t₂).mpr ⟨hscope₁,hscope₂⟩⟩
      · intro out hout
        rcases List.mem_append.mp hout with hout | hout
        · exact (hknown₁ out hout).mono (known_mono points t₁ t₂)
        · simpa only [known_append] using hknown₂ out hout
      · simpa only [known_append] using hcache₂

end EnvyFreeResearch.Full.Chores.Boundary
