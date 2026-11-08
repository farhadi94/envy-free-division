import EnvyFreeResearch.Full.ChoresComponentClosedProgram
import EnvyFreeResearch.Full.ChoresComponentBoundaryRecorded

/-! Boundary contract for the actual affine closed-group wrapper. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition Boundary SubCoreEntry Persistent Suffix SubCorePhysical
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]

theorem closed_group_known
    (state : PendingState Root (Fin n)) (visited : Visited state)
    (participants : Finset (Fin n)) (label : Fin n)
    (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ)
    (hmany : Fintype.card participants < Fintype.card Root)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
    (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
    (hgap : ∀ s p i, 0 ≤ gap s p i) (hpositive : participants.Nonempty)
    (hwhole : ∀ s (i : participants), 0 ≤ SubCoreEntry.cachedTotals cache s i -
      ComponentPayments.offsets gap state.partition.representative s i)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hcache : MaskedCacheKnown points cache)
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (prior trace : History (Query (Fin n)) ℝ)
    (out : ComponentClosed.Result (Root := Root) participants) (package : Package (Fin n) RootId)
    (h : Executes oracle (ComponentClosed.program state visited participants label packages frames gap hmany cache)
      prior (some (out,package)) trace) :
    RecordedKnown id (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨source,first,second,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
  cases source with
  | none => cases hsecond
  | some result =>
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    exact affine_recorded_known cost domains cache hc Subtype.val
      (ComponentPayments.offsets gap state.partition.representative) (fun s i => hgap s _ i)
      (by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hpositive)
      hmany hwhole oracle hpolicy points hcache hzero hone prior out first hfirst
end EnvyFreeResearch.Full.Chores.Outer
