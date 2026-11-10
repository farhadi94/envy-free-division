import EnvyFreeResearch.Full.RefinedChoresGroupPrivate
import EnvyFreeResearch.Full.RefinedChoresGroupBoundary
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryPrivate

/-! An ordinary step carries both allocated caches and literal private
complements. They are assembled from the same recorded SubCore output. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.QueryProgram
open Chores.InitialPartition Chores.OrderedUnion Chores.Boundary Chores.Suffix
open RefinedChoresPhysicalPayment
open scoped Classical
variable {n : ℕ} {RootId : Type*}

structure PoolState (n : ℕ) (RootId : Type*) where
  data : Data n RootId
  privateCache : RootId → Fin n → List (Parent n)

variable [Fintype RootId] (state : PoolState n RootId) (normal : state.data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group state.data normal original r H)

def Group.resultState (out : Result (Root := group.Root) group.component) : PoolState n RootId :=
  ⟨Group.commit state.data normal original r H group out,
    Group.poolPrivate state.data normal original r H group out state.privateCache⟩

def Group.physicalStep : Program (Query (Fin n)) ℝ (Option (PoolState n RootId)) :=
  (Group.program state.data normal original r H group).bind (fun result =>
    .returned (result.map (fun result => Group.resultState state normal original r H group result.1)))

variable (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
include hknown

theorem Group.private_known (out : Result (Root := group.Root) group.component)
    (hout : RecordedKnown ClippedRecord.record points out)
    (hold : ∀ root a, CacheKnown points (state.privateCache root a)) (root : RootId) (a : Fin n) :
    CacheKnown points ((Group.resultState state normal original r H group out).privateCache root a) := by
  change CacheKnown points (ComponentPhysical.patchCache _ _ _ root a)
  unfold ComponentPhysical.patchCache
  split
  · unfold Group.nextPrivate ComponentAssignment.dispatch
    split
    · apply Outer.proposal_private_known points
      · intro q j parent hp
        exact ((hknown _).table (q,j)).2 parent (List.mem_append_right _ hp)
      · intro parent hp
        exact (hout.2.2.2 _) parent (List.mem_append_right _ hp)
    · intro parent hp
      exact ((hknown _).table _).2 parent (List.mem_append_right _ hp)
  · exact hold root a

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
    (good : state.data.Good original cost r H)
    (hprivate : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
      state.data.cache state.privateCache)
include hsound horiginal hsep hr hH hscale hr_eq good hprivate
omit hknown in
theorem Group.physical_step_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ after : PoolState n RootId, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (Group.physicalStep state normal original r H group) prior (some after) trace ∧
      after.data.Good original cost r H ∧
      Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) after.data.cache after.privateCache ∧
      after.data.size < state.data.size ∧ after.data.closed = state.data.closed ∧
      after.data.protectedLabel = state.data.protectedLabel ∧
      (state.data.Omitted original c r H → after.data.Omitted original c r H) ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card ↥group.component) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ SubCore.sourceBudget (Fintype.card ↥group.component) := by
  obtain ⟨out,trace,he,hvalid,hphysical,hparts,hqueries,hcuts,hcache⟩ :=
    Group.program_correct state.data normal original r H group cost xs index c hsound horiginal R
      hsep hr hH hscale hr_eq good oracle hpolicy prior
  refine ⟨Group.resultState state normal original r H group out,trace,?_,?_,?_,
    Group.commit_decreases state.data normal original r H group out,rfl,rfl,
    Group.commit_omitted state.data original r H normal group out c,hqueries,hcuts⟩
  · have h := he.bind (fun result => .returned (result.map
      (fun result => Group.resultState state normal original r H group result.1))) (Executes.returned _ _)
    simpa only [List.append_nil,Group.physicalStep,Option.map_some] using h
  · apply Group.commit_good state.data normal original r H group out cost c hsound good hparts hvalid
    · intro i; rw [hr_eq]; exact (hr i).le
    · linarith
    · exact Group.offer_small state.data normal original r H group cost xs index c hsound horiginal R
        hsep hr hH hscale hr_eq
  · exact Group.pool_private_correct state.data normal original r H group out cost c hsound good hparts
      state.privateCache hprivate

omit horiginal hsep hr hH hscale hr_eq good hprivate in
theorem Group.physical_step_known (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
    (hold : ∀ root a, CacheKnown points (state.data.cache root a))
    (hpriv : ∀ root a, CacheKnown points (state.privateCache root a))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) (after : PoolState n RootId) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Group.physicalStep state normal original r H group) prior (some after) trace) :
    (∀ root a, CacheKnown (Known points trace) (after.data.cache root a)) ∧
    (∀ root a, CacheKnown (Known points trace) (after.privateCache root a)) ∧ Scoped points trace := by
  obtain ⟨source,first,second,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
  cases source with
  | none => cases hsecond
  | some pair =>
    obtain ⟨out,package⟩ := pair
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    obtain ⟨hout,hscope⟩ := Group.program_known state.data normal original r H group points hknown
      cost c hsound hzero hone oracle hpolicy prior out package first hfirst
    exact ⟨Group.commit_known state.data normal original r H group (Known points first)
      (fun root => (hknown root).mono subset_union_left) out hout
      (fun root a => (hold root a).mono subset_union_left),
      Group.private_known state normal original r H group (Known points first)
        (fun root => (hknown root).mono subset_union_left) out hout
        (fun root a => (hpriv root a).mono subset_union_left),hscope⟩

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.physical_step_correct
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.physical_step_known
