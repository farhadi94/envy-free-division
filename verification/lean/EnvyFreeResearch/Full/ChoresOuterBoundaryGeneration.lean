import EnvyFreeResearch.Full.ChoresOuterBoundarySnapshot

/-! Sequential snapshot generation retains a single parametric set of
inherited coordinates, enlarged only by physical Cut replies. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Equalizers Snapshot
open scoped Classical

variable {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)

include hn hpolicy

theorem snapshot_sound_of_executes (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (c : Fin n)
    (prior : History (Query (Fin n)) ℝ) (out : Snapshot.Output n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Snapshot.program c cache) prior out trace) : Snapshot.Sound cost U c out := by
  obtain ⟨actual,t,hexec,_,_,hsound⟩ := Snapshot.sound_program_correct hn cost oracle hpolicy U cache hc c prior
  have hout := (hexec.deterministic h).1
  exact hout ▸ hsound

theorem generate_known (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache)
    (points : Set ℝ) (hcache : CacheKnown points cache) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (c : Fin n) (count : ℕ) (prior : History (Query (Fin n)) ℝ)
    (batch : Snapshot.Batch n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Snapshot.generate c count cache) prior batch trace) :
    (∀ out ∈ batch.snapshots, SnapshotKnown (Known points trace) out) ∧
      CacheKnown (Known points trace) batch.residue ∧ Scoped points trace := by
  induction count generalizing U cache points prior batch trace with
  | zero =>
    cases h
    exact ⟨by simp,by simpa only [known_nil] using hcache,trivial⟩
  | succ count ih =>
    obtain ⟨first,t₁,tail,hfirst,htail,htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨rest,t₂,empty,hrest,hreturn,htailtrace⟩ := Executes.split_bind _ _ htail
    cases hreturn
    simp only [List.append_nil] at htailtrace
    subst tail
    subst trace
    obtain ⟨hknown₁,hscope₁⟩ := snapshot_known cost oracle hpolicy U cache hc points hcache hzero hone
      c prior first t₁ hfirst
    have hsound := snapshot_sound_of_executes hn cost oracle hpolicy U cache hc c prior first t₁ hfirst
    obtain ⟨hknown₂,hcache₂,hscope₂⟩ := ih (domainResidue U first.outcome) first.residue hsound.residue_cache
      (Known points t₁) hknown₁.residue (Or.inl hzero) (Or.inl hone) (prior++t₁) rest t₂ hrest
    refine ⟨?_,?_,(scoped_append points t₁ t₂).mpr ⟨hscope₁,hscope₂⟩⟩
    · intro out hout
      rcases List.mem_cons.mp hout with rfl | hout
      · exact hknown₁.mono (known_mono points t₁ t₂)
      · simpa only [known_append] using hknown₂ out hout
    · simpa only [known_append] using hcache₂

end EnvyFreeResearch.Full.Chores.Boundary
