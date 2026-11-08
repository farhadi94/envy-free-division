import EnvyFreeResearch.Full.ChoresOuterDriverProgram
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryBatch
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryOutside
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryPrivatePatch

/-! Every actual successful outer execution preserves original/Cut boundary
provenance for both the retained allocation and its private complements. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition Boundary SubCoreEntry Persistent Suffix
open scoped Classical
variable {n : ℕ} [NeZero n] {RootId : Type*} [Fintype RootId]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (pivot : Fin n) (r : Fin n → ℝ) (H : ℝ)
include hsound

theorem driver_known (fuel : ℕ) (data : Data n RootId)
    (privateCache : RootId → Fin n → List (Parent n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hold : DataKnown points (fun root => xs.get (index root)) data)
    (hprivate : ∀ root p, CacheKnown points (privateCache root p))
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (prior trace : History (Query (Fin n)) ℝ)
    (out : TerminalEntrance (fun root => xs.get (index root)) r H)
    (h : Executes oracle (driverProgram (fun root => xs.get (index root)) pivot r H fuel data privateCache)
      prior (some out) trace) :
    DataKnown (Known points trace) (fun root => xs.get (index root)) out.data ∧
      (∀ root p, CacheKnown (Known points trace) (out.privateCache root p)) ∧ Scoped points trace := by
  induction fuel generalizing data privateCache points prior trace out with
  | zero => cases h
  | succ fuel ih =>
    cases ha : nextAction data with
    | reveal p hp hf =>
      simp only [driverProgram,ha] at h
      split at h
      next t roots hc =>
        cases h
        simp only [known_nil]
        exact ⟨hold,hprivate,trivial⟩
      next target roots hc =>
        split at h
        next hc' => cases h
        next updated hc' =>
          exact ih updated privateCache points
            (outside_commit_known data _ points hold p hp r H roots target updated hc')
            hprivate hzero hone prior trace out h
    | merge hall cycle =>
      simp only [driverProgram,ha] at h
      obtain ⟨results,t₁,t₂,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
      cases results with
      | none => cases hsecond
      | some outputs =>
        subst trace
        obtain ⟨hout,hscope₁⟩ := batch_known cost xs index c hsound data hall cycle
          (cohorts data hall cycle) oracle hpolicy points hold.snapshots hzero hone prior outputs t₁ hfirst
        obtain ⟨hfinal,hprivateFinal,hscope₂⟩ := ih _ _ (Known points t₁)
          (commit_batch_known data hall cycle _ outputs _ _ _ (hold.mono subset_union_left) hout)
          (batch_private_known data hall cycle _ _
            (fun root => (hold.snapshots root).mono subset_union_left) privateCache outputs hout
            (fun root p => (hprivate root p).mono subset_union_left))
          (Or.inl hzero) (Or.inl hone) (prior++t₁) t₂ out hsecond
        refine ⟨?_,?_,(scoped_append points t₁ t₂).mpr ⟨hscope₁,hscope₂⟩⟩
        · simpa only [known_append] using hfinal
        · simpa only [known_append] using hprivateFinal
end EnvyFreeResearch.Full.Chores.Outer
