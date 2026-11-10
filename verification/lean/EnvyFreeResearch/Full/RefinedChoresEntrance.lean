import EnvyFreeResearch.Full.RefinedChoresDataFilter
import EnvyFreeResearch.Full.ChoresOuterEntrance

/-! The actual protected preprocessing choice initializes the new pool.
All J original roots remain present; exactly S are live and the rest are frozen. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open ChoreComposition
open scoped Classical
variable {n J : ℕ}

def entranceData (a : Outer.EntranceChoice n J) (original : Fin J → Snapshot.Output n) : Data n (Fin J) :=
  filterData (initialData original a.pivot) (a.roots.orderEmbOfFin rfl).toEmbedding

theorem entrance_mass (a : Outer.EntranceChoice n J) (original : Fin J → Snapshot.Output n) :
    (entranceData a original).activeMass = a.roots.card := by
  change (∑ _s : Fin a.roots.card, 1) = a.roots.card
  simp

theorem entrance_omitted (a : Outer.EntranceChoice n J) (original : Fin J → Snapshot.Output n)
    (c : Fin n) (r : Fin n → ℝ) (H : ℝ) (S : ℕ) (ha : a.Admissible original c r H S) :
    (entranceData a original).Omitted original c r H := by
  intro s
  exact ha.2.2 _ (a.roots.orderEmbOfFin_mem rfl s)

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (original : Fin J → Snapshot.Output n) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (r : Fin n → ℝ) (H : ℝ) (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
include hsound hr hH

theorem entrance_good (a : Outer.EntranceChoice n J) :
    (entranceData a original).Good original cost r H :=
  filter_good (initialData original a.pivot) (a.roots.orderEmbOfFin rfl).toEmbedding
    original cost r H (initial_good cost original a.pivot c hsound r H hr hH)

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.entrance_good
