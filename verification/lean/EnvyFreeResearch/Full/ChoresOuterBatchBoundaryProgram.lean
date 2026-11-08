import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryGroup

/-! A sequential batch keeps every original cohort's boundary ledger in
one cumulative history. In particular, later groups may depend on all
previous oracle replies without being supplied fresh free endpoints. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition Boundary SubCoreEntry Persistent Suffix SubCorePhysical
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
include hsound

theorem batch_known (groups : List (Cohort data hall cycle))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (xs.get (index root)))
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (prior : History (Query (Fin n)) ℝ) (outputs : List (GroupResult data hall cycle))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (batchProgram data hall cycle (fun root => xs.get (index root)) groups)
      prior (some outputs) trace) :
    (∀ out ∈ outputs, RecordedKnown ClippedRecord.record (Known points trace) out.result) ∧
      Scoped points trace := by
  induction groups generalizing points prior outputs trace with
  | nil =>
    cases h
    exact ⟨by simp,trivial⟩
  | cons group rest ih =>
    obtain ⟨first,t₁,tail,hfirst,htail,htrace⟩ := Executes.split_bind _ _ h
    cases first with
    | none => cases htail
    | some result =>
      obtain ⟨second,t₂,empty,hsecond,hreturn,htailtrace⟩ := Executes.split_bind _ _ htail
      cases second with
      | none => cases hreturn
      | some remaining =>
        cases hreturn
        simp only [List.append_nil] at htailtrace
        subst tail
        subst trace
        obtain ⟨hresult,hscope₁⟩ := cohort_known cost xs index c hsound points hknown hzero hone
          data hall cycle group oracle hpolicy prior result t₁ hfirst
        obtain ⟨hremaining,hscope₂⟩ := ih (Known points t₁)
          (fun root => (hknown root).mono subset_union_left) (Or.inl hzero) (Or.inl hone)
          (prior++t₁) remaining t₂ hsecond
        refine ⟨?_,(scoped_append points t₁ t₂).mpr ⟨hscope₁,hscope₂⟩⟩
        intro out hout
        rcases List.mem_cons.mp hout with rfl | hout
        · exact hresult.mono (known_mono points t₁ t₂)
        · simpa only [known_append] using hremaining out hout

end EnvyFreeResearch.Full.Chores.Outer
