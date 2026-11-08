import EnvyFreeResearch.Full.ChoresOuterBoundaryClearance
import EnvyFreeResearch.Full.ChoresOuterPreprocessingProgram
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryState
import EnvyFreeResearch.Full.ChoresComponentBoundaryAssembly

/-! All preprocessing queries and retained immutable records share the
same inherited-or-Cut coordinate ledger, including clearance allocations. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Boundary
open scoped Classical
variable {n : ℕ}

structure PreprocessingKnown (points : Set ℝ) (out : Preprocessing.Output n) : Prop where
  originals : ∀ x ∈ out.originals, SnapshotKnown points x
  clearance : ∀ x ∈ out.clearance, SnapshotKnown points x
  middle : CacheKnown points out.middle
  residue : CacheKnown points out.residue

theorem preprocessing_known (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (points : Set ℝ) (hcache : CacheKnown points cache) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (c : Fin n) (J : ℕ) (H : ℝ) (L : ℕ) (prior trace : History (Query (Fin n)) ℝ)
    (out : Preprocessing.Output n)
    (h : Executes oracle (Preprocessing.program c J H L cache) prior out trace) :
    PreprocessingKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨original,t₁,tail,hfirst,htail,htrace⟩ := Executes.split_bind _ _ h
  obtain ⟨cleared,t₂,empty,hsecond,hreturn,htailtrace⟩ := Executes.split_bind _ _ htail
  cases hreturn
  simp only [List.append_nil] at htailtrace
  subst tail
  subst trace
  obtain ⟨hknown₁,hcache₁,hscope₁⟩ := generate_known hn cost oracle hpolicy U cache hc points
    hcache hzero hone c J prior original t₁ hfirst
  have hchain := generate_chain_of_executes hn cost oracle hpolicy U cache hc c J prior original t₁ hfirst
  obtain ⟨hknown₂,hcache₂,hscope₂⟩ := clearance_known hn cost oracle hpolicy
    (Clearance.entries original.snapshots) H L _ Finset.univ.toList
    (material original.residue) original.residue hchain.final_cache
    (Known points t₁) hcache₁ (Or.inl hzero) (Or.inl hone) (prior++t₁) cleared t₂ hsecond
  refine ⟨⟨?_,?_,hcache₁.mono (known_mono points t₁ t₂),?_⟩,
    (scoped_append points t₁ t₂).mpr ⟨hscope₁,hscope₂⟩⟩
  · exact fun x hx => (hknown₁ x hx).mono (known_mono points t₁ t₂)
  · intro x hx
    simpa only [known_append] using hknown₂ x hx
  · simpa only [known_append] using hcache₂

theorem batch_allocation_known (points : Set ℝ) (xs : List (Snapshot.Output n))
    (hknown : ∀ x ∈ xs, SnapshotKnown points x) : AllocationKnown points (batchAllocation xs) := by
  induction xs with
  | nil => intro i; simp [batchAllocation,CacheKnown]
  | cons x xs ih =>
    exact join_known (fun i => (hknown x (List.mem_cons_self)).parents i)
      (ih (fun y hy => hknown y (List.mem_cons_of_mem _ hy)))

def PreparedKnown (points : Set ℝ) : Prepared n → Prop
  | .complete allocation => AllocationKnown points allocation
  | .failed => True
  | .continuing out a => PreprocessingKnown points out ∧
      DataKnown points out.originals.get (a.data out.originals.get)

theorem prepare_finish_known (points : Set ℝ) (c : Fin n) (H : ℝ) (S : ℕ)
    (out : Preprocessing.Output n) (ho : PreprocessingKnown points out) :
    PreparedKnown points (prepareFinish c H S out) := by
  unfold prepareFinish
  split
  · apply join_known
    · apply batch_allocation_known
      intro x hx
      exact (List.mem_append.mp hx).elim (ho.originals x) (ho.clearance x)
    · exact zero_allocation_known points _ _ ho.residue
  · split
    · trivial
    · exact ⟨ho,(initial_data_known points out.originals.get
        (fun s => ho.originals _ (List.get_mem _ _))).filter _⟩

theorem prepare_program_known (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (points : Set ℝ) (hcache : CacheKnown points cache) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (c : Fin n) (J : ℕ) (H : ℝ) (L S : ℕ) (prior trace : History (Query (Fin n)) ℝ)
    (out : Prepared n)
    (h : Executes oracle (prepareProgram c J H L S cache) prior out trace) :
    PreparedKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨raw,first,empty,hfirst,hreturn,htrace⟩ := Executes.split_bind _ _ h
  cases hreturn
  simp only [List.append_nil] at htrace
  subst trace
  obtain ⟨ho,hs⟩ := preprocessing_known hn cost oracle hpolicy U cache hc points hcache hzero hone
    c J H L prior first raw hfirst
  exact ⟨prepare_finish_known _ c H S raw ho,hs⟩
end EnvyFreeResearch.Full.Chores.Outer
