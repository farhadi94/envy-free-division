import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryClosed
import EnvyFreeResearch.Full.ChoresOuterBoundarySnapshot
import EnvyFreeResearch.Full.ChoresTerminalProgram

/-! Terminal scan fronts and offers are literal recorded prefixes/suffixes,
including the initial atomic boundary and zero-length table entries. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Boundary Frontier
open Equalizers Scheduler Components ChoreComposition SubCoreEntry
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem outcome_front_known (points : Set ℝ) (table : Table n)
    (ht : TableKnown points table) (p : Fin n) (out : Frontier.Outcome n) :
    CacheKnown points (out.front table p) := by
  cases out with
  | outside q | exhausted q =>
    intro parent hp
    exact (ht (p,q)).2 parent (List.mem_append_left _ hp)
  | atomic a =>
    change CacheKnown points (boundaryPrefix table p a.castSucc)
    unfold boundaryPrefix
    split
    · simp [CacheKnown]
    · intro parent hp
      exact (ht _).2 parent (List.mem_append_left _ hp)

theorem outcome_offer_known (points : Set ℝ) (table : Table n)
    (ht : TableKnown points table) (p : Fin n) (cache : List (Parent n))
    (hc : CacheKnown points cache) (out : Frontier.Outcome n) :
    CacheKnown points (out.offer table p cache) := by
  cases out with
  | outside q | exhausted q =>
    intro parent hp
    exact (ht (p,q)).2 parent (List.mem_append_right _ hp)
  | atomic a =>
    change CacheKnown points (boundaryCache table p cache a.castSucc)
    unfold boundaryCache
    split
    · exact hc
    · intro parent hp
      exact (ht _).2 parent (List.mem_append_right _ hp)

variable (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (r : Fin n → ℝ) (H : ℝ) (points : Set ℝ)
    (hknown : ∀ root, SnapshotKnown points (original root))
include hknown

theorem terminal_fronts_known (s : Fin data.size) (p : Fin n) :
    CacheKnown points (Terminal.fronts data original r H s p) :=
  outcome_front_known points _ (hknown _).table p _

theorem terminal_offers_known (s : Fin data.size) (p : Fin n) :
    CacheKnown points (Terminal.offers data original r H s p) :=
  outcome_offer_known points _ (hknown _).table p _ ((hknown _).parents p) _

theorem terminal_masked_known : MaskedCacheKnown points (Terminal.masked data original r H) :=
  fun s i => terminal_offers_known data original r H points hknown s _
end EnvyFreeResearch.Full.Chores.Outer
