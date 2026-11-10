import EnvyFreeResearch.Full.RefinedChoresPhysicalStep
import EnvyFreeResearch.Full.RefinedChoresDriverChoice

/-! Complete physical prefix: allocated and private caches, query trace,
and endpoint provenance are maintained until a terminal cohort is reached. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.QueryProgram
open Chores.InitialPartition Chores.OrderedUnion Chores.Boundary
open scoped Classical
variable {n : ℕ} {RootId : Type*}

structure PhysicalTerminalEntry (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ) where
  state : PoolState n RootId
  normal : state.data.Normal
  group : TerminalGroup state.data normal original r H

variable [Fintype RootId] (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)

def physicalPrefix : ℕ → PoolState n RootId → Program (Query (Fin n)) ℝ (Option (PhysicalTerminalEntry original r H))
  | 0, _ => .failed
  | fuel+1, state =>
    let current : PoolState n RootId := { state with data := state.data.normalize }
    match chooseCohort current.data (normalized_normal state.data) original r H with
    | none => .failed
    | some (.inr terminal) => .returned (some ⟨current,normalized_normal state.data,terminal⟩)
    | some (.inl ordinary) =>
      (Group.physicalStep current (normalized_normal state.data) original r H ordinary).bind (fun result =>
        match result with
        | none => .failed
        | some after => physicalPrefix fuel after)

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
include hsound horiginal hsep hr hH hscale hr_eq

theorem physicalPrefix_correct (fuel : ℕ) (state : PoolState n RootId)
    (good : state.data.Good original cost r H)
    (hprivate : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
      state.data.cache state.privateCache)
    (hmass : state.data.activeMass = RefinedChoresPool.poolSize n)
    (homitted : state.data.Omitted original c r H) (hfuel : state.data.size ≤ fuel)
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
    (hold : ∀ root a, CacheKnown points (state.data.cache root a))
    (hpriv : ∀ root a, CacheKnown points (state.privateCache root a))
    (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ entry : PhysicalTerminalEntry original r H, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (physicalPrefix original r H fuel state) prior (some entry) trace ∧
      entry.state.data.Good original cost r H ∧
      Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
        entry.state.data.cache entry.state.privateCache ∧
      entry.state.data.closed = state.data.closed ∧ entry.state.data.Omitted original c r H ∧
      entry.state.data.protectedLabel = state.data.protectedLabel ∧
      trace.length ≤ fuel*ComponentRecording.budget n n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ fuel*SubCore.sourceBudget n ∧
      (∀ root a, CacheKnown (Known points trace) (entry.state.data.cache root a)) ∧
      (∀ root a, CacheKnown (Known points trace) (entry.state.privateCache root a)) ∧
      Scoped points trace := by
  induction fuel generalizing state prior points with
  | zero =>
    have hz : (∑ s : Fin state.data.size, (state.data.packages s).ids.length) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      have := s.isLt
      omega
    change (∑ s : Fin state.data.size, (state.data.packages s).ids.length) = _ at hmass
    rw [hz] at hmass
    unfold RefinedChoresPool.poolSize at hmass
    omega
  | succ fuel ih =>
    let current : PoolState n RootId := { state with data := state.data.normalize }
    have hn : current.data.Normal := normalized_normal state.data
    have hg : current.data.Good original cost r H := normalized_good state.data original cost r H good
    have hm : current.data.activeMass = RefinedChoresPool.poolSize n := hmass
    have ho : current.data.Omitted original c r H := homitted
    obtain ⟨choice,hchoice⟩ := chooseCohort_some_mass current.data hn original r H cost hg hm
      (fun i => by rw [hr_eq]; exact (hr i).le) (by linarith)
    dsimp only [current,hn] at hchoice
    cases choice with
    | inr terminal =>
      refine ⟨⟨current,hn,terminal⟩,[],?_,hg,hprivate,rfl,ho,rfl,by simp,by simp,?_,?_,trivial⟩
      · simpa only [physicalPrefix,hchoice,current,hn] using
          (Executes.returned (some (⟨current,hn,terminal⟩ : PhysicalTerminalEntry original r H)) prior)
      · simpa only [known_nil,current,Data.normalize] using hold
      · simpa only [known_nil] using hpriv
    | inl ordinary =>
      obtain ⟨after,first,he,hg',hprivate',hd,hclosed',hp,homit,hq,hcuts⟩ :=
        Group.physical_step_correct current hn original r H ordinary cost xs index c hsound horiginal R
          hsep hr hH hscale hr_eq hg hprivate oracle hpolicy prior
      have hf : after.data.size ≤ fuel := by change after.data.size < state.data.size at hd; omega
      have hm' : after.data.activeMass = RefinedChoresPool.poolSize n :=
        (active_mass_preserved current.data original cost r H hg after.data hg' hclosed').trans hm
      obtain ⟨hk,hpvt,hscope⟩ := Group.physical_step_known current hn original r H ordinary points hknown
        cost c hsound hzero hone hold hpriv oracle hpolicy prior after first he
      obtain ⟨entry,second,he',hg'',hprivate'',hc'',ho'',hp',hq',hcuts',hk',hpvt',hscope'⟩ :=
        ih after hg' hprivate' hm' (homit ho) hf (Known points first)
          (fun root => (hknown root).mono subset_union_left) hk hpvt (Or.inl hzero) (Or.inl hone) (prior++first)
      refine ⟨entry,first++second,?_,hg'',hprivate'',hc''.trans hclosed',ho'',hp'.trans hp,?_,?_,?_,?_,?_⟩
      · have h := he.bind (fun result => match result with
          | none => Program.failed
          | some after => physicalPrefix original r H fuel after) he'
        simpa only [physicalPrefix,hchoice,current,hn] using h
      · have hcard : Fintype.card ↥ordinary.component ≤ n := by
          simpa only [Fintype.card_coe,Fintype.card_fin] using Finset.card_le_univ ordinary.component
        have hunit := hq.trans (Outer.recorded_budget_mono n hcard)
        rw [List.length_append]
        nlinarith
      · have hcard : Fintype.card ↥ordinary.component ≤ n := by
          simpa only [Fintype.card_coe,Fintype.card_fin] using Finset.card_le_univ ordinary.component
        have hunit := hcuts.trans (Outer.source_budget_mono hcard)
        rw [List.countP_append]
        nlinarith
      · simpa only [known_append] using hk'
      · simpa only [known_append] using hpvt'
      · exact (scoped_append points first second).mpr ⟨hscope,hscope'⟩

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.physicalPrefix_correct
