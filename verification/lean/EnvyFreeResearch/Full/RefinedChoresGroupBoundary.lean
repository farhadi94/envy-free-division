import EnvyFreeResearch.Full.RefinedChoresGroupExecution
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryCache

/-! Every ordinary-step query and physical output endpoint comes from the
recorded history or the incoming finite-union caches. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.QueryProgram
open Chores.InitialPartition Chores.OrderedUnion Chores.Boundary Chores.Suffix
open Chores.ComponentRecording Chores.ComponentPayments
open RefinedChoresPhysicalPayment RefinedChoresDonorCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group data normal original r H)
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
include hknown

theorem Group.masked_known : MaskedCacheKnown points (Group.masked data normal original r H group) := by
  intro s i parent hp
  exact ((hknown _).table _).2 parent (List.mem_append_right _ hp)

theorem Group.next_known (out : Result (Root := group.Root) group.component)
    (hout : RecordedKnown ClippedRecord.record points out) (s : group.Root) (a : Fin n) :
    CacheKnown points (Group.next data normal original r H group out s a) := by
  unfold Group.next nextCache ComponentAssignment.dispatch
  split
  · unfold donorCache
    apply Outer.proposal_cache_known points
    · intro q j parent hp
      exact ((hknown _).table (q,j)).2 parent (List.mem_append_left _ hp)
    · intro parent hp
      exact ((hknown _).table _).2 parent (List.mem_append_left _ hp)
    · intro parent hp
      exact (hout.2.2.2 _) parent (List.mem_append_left _ hp)
  · intro parent hp
    exact ((hknown _).table _).2 parent (List.mem_append_left _ hp)

theorem Group.commit_known (out : Result (Root := group.Root) group.component)
    (hout : RecordedKnown ClippedRecord.record points out)
    (hold : ∀ root a, CacheKnown points (data.cache root a)) (root : RootId) (a : Fin n) :
    CacheKnown points ((Group.commit data normal original r H group out).cache root a) := by
  change CacheKnown points (ComponentPhysical.patchCache _ _ _ root a)
  unfold ComponentPhysical.patchCache
  split
  · exact Group.next_known data normal original r H group points hknown out hout _ a
  · exact hold root a

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
include hsound hzero hone

theorem Group.program_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ)
    (out : Result (Root := group.Root) group.component) (package : ChoreComposition.Package (Fin n) RootId)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Group.program data normal original r H group) prior (some (out,package)) trace) :
    RecordedKnown ClippedRecord.record (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨source,first,second,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
  cases source with
  | none => cases hsecond
  | some result =>
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    apply clipped_recorded_known cost
      (domains (Group.blocks data normal original r H group) (fun _ => group.label))
      (Group.masked data normal original r H group)
      (Group.cache_correct data normal original r H group cost c hsound) Subtype.val
      (offsets (Group.gaps data normal original r H group) (fun _ => group.label)) _
      (by simpa using Finset.card_pos.mpr (Group.nonempty data normal original r H group))
      (by simp [Group.Root]) oracle hpolicy points
      (Group.masked_known data normal original r H group points hknown) hzero hone prior out first hfirst
    intro s i
    exact Clearance.gap_nonnegative (hsound (data.source (group.roots s))).choose_spec i group.label

theorem Group.step_known
    (hold : ∀ root a, CacheKnown points (data.cache root a))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) (after : Data n RootId) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Group.step data normal original r H group) prior (some after) trace) :
    (∀ root a, CacheKnown (Known points trace) (after.cache root a)) ∧ Scoped points trace := by
  obtain ⟨source,first,second,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
  cases source with
  | none => cases hsecond
  | some pair =>
    obtain ⟨out,package⟩ := pair
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    obtain ⟨hout,hscope⟩ := Group.program_known data normal original r H group points hknown
      cost c hsound hzero hone oracle hpolicy prior out package first hfirst
    exact ⟨Group.commit_known data normal original r H group (Known points first)
      (fun root => (hknown root).mono subset_union_left) out hout
      (fun root a => (hold root a).mono subset_union_left),hscope⟩

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.step_known
