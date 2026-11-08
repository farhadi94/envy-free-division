import EnvyFreeResearch.Full.ChoresTerminalCohort
import EnvyFreeResearch.Full.ChoresOuterOffers

/-! Terminal offers and their complementary prefixes are read from the
immutable equalizer table, without additional oracle calls. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical

variable {n : ℕ} {RootId : Type*}
  (data : Outer.Data n RootId) (original : RootId → Snapshot.Output n)
  (r : Fin n → ℝ) (H : ℝ)

def fronts (s : Fin data.size) (p : Fin n) : List (Parent n) :=
  front (original (data.source s)) p r H (data.pending.partition.component p)

def offers (s : Fin data.size) (p : Fin n) : List (Parent n) :=
  offer (original (data.source s)) p r H (data.pending.partition.component p)

def blocks (s : Fin data.size) (p : Fin n) : Set ℝ := material (offers data original r H s p)

def masked : Masked.Cache (Fin data.size) n :=
  fun s i => offers data original r H s (data.pending.partition.representative i)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))

include hsound

theorem fronts_valid (s : Fin data.size) (p : Fin n) :
    CacheValid (measureProfile cost) (material (fronts data original r H s p))
      (fronts data original r H s p) := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact Frontier.front_cache_valid cost _ _ (snapshot_parent_cache hs p) _ p _
    (snapshot_equalizers hs p) (hs.own_equalizers p).1 _

theorem offers_valid (s : Fin data.size) (p : Fin n) :
    CacheValid (measureProfile cost) (blocks data original r H s p)
      (offers data original r H s p) := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact Frontier.offer_cache_valid cost _ _ (snapshot_parent_cache hs p) _ p _
    (snapshot_equalizers hs p) (hs.own_equalizers p).1 _

theorem blocks_complement (s : Fin data.size) (p : Fin n) :
    blocks data original r H s p=(original (data.source s)).piece p \
      material (fronts data original r H s p) := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact Frontier.offer_complement cost _ _ (snapshot_parent_cache hs p) _ p _
    (snapshot_equalizers hs p) (hs.own_equalizers p).1 _

theorem fronts_subset (s : Fin data.size) (p : Fin n) :
    material (fronts data original r H s p) ⊆ (original (data.source s)).piece p := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact Frontier.front_subset cost _ _ (snapshot_parent_cache hs p) _ p _
    (snapshot_equalizers hs p) (hs.own_equalizers p).1 _

theorem masked_correct : Masked.CacheCorrect (measureProfile cost)
    (ComponentPayments.domains (blocks data original r H) data.pending.partition.representative)
    (masked data original r H) := by
  intro s i
  exact offers_valid data original r H cost c hsound s _

end EnvyFreeResearch.Full.Chores.Terminal
