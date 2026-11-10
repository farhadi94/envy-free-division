import EnvyFreeResearch.Full.RefinedChoresEntrance
import EnvyFreeResearch.Full.RefinedChoresPhysicalPrefix

/-! The protected preprocessing selection supplies the complete physical
prefix state, including empty original private complements. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.QueryProgram
open Chores.InitialPartition Chores.OrderedUnion Chores.Boundary
open scoped Classical
variable {n J : ℕ}

def entranceState (a : Outer.EntranceChoice n J) (original : Fin J → Snapshot.Output n) : PoolState n (Fin J) :=
  ⟨entranceData a original,fun _ _ => []⟩

def entranceProgram (a : Outer.EntranceChoice n J) (original : Fin J → Snapshot.Output n)
    (r : Fin n → ℝ) (H : ℝ) :=
  physicalPrefix original r H a.roots.card (entranceState a original)

variable (original : Fin J → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : Fin J → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root=xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n:ℝ)<H*H)
    (hr_eq : r=fun i => (cost i).real R)
    (a : Outer.EntranceChoice n J)
    (ha : a.Admissible original c r H (RefinedChoresPool.poolSize n))
include hsound horiginal hsep hr hH hscale hr_eq ha

theorem entrance_program_correct
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
    (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ entry : PhysicalTerminalEntry original r H, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (entranceProgram a original r H) prior (some entry) trace ∧
      entry.state.data.Good original cost r H ∧
      Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
        entry.state.data.cache entry.state.privateCache ∧
      entry.state.data.closed = (entranceData a original).closed ∧
      entry.state.data.Omitted original c r H ∧ entry.state.data.protectedLabel=a.pivot ∧
      trace.length ≤ RefinedChoresPool.poolSize n*ComponentRecording.budget n n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ RefinedChoresPool.poolSize n*SubCore.sourceBudget n ∧
      (∀ root p, CacheKnown (Known points trace) (entry.state.data.cache root p)) ∧
      (∀ root p, CacheKnown (Known points trace) (entry.state.privateCache root p)) ∧ Scoped points trace := by
  have hr0 : ∀ i, 0 ≤ r i := by intro i; rw [hr_eq]; exact (hr i).le
  have hH0 : 0 < H := by linarith
  have hg := entrance_good cost original c hsound r H hr0 hH0 a
  have hp : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
      (entranceState a original).data.cache (entranceState a original).privateCache :=
    Outer.private_initial (measureProfile cost) original
  have hm : (entranceState a original).data.activeMass=RefinedChoresPool.poolSize n :=
    (entrance_mass a original).trans ha.2.1
  have ho := entrance_omitted a original c r H (RefinedChoresPool.poolSize n) ha
  have hcache : ∀ root p, CacheKnown points ((entranceState a original).data.cache root p) :=
    fun root p => (hknown root).parents p
  have hprivate : ∀ root p, CacheKnown points ((entranceState a original).privateCache root p) := by
    intro root p parent hp
    exact (List.not_mem_nil hp).elim
  have h := physicalPrefix_correct original r H cost xs index c hsound horiginal R hsep hr hH hscale hr_eq
    a.roots.card (entranceState a original) hg hp hm ho le_rfl points hknown hcache hprivate
    hzero hone oracle hpolicy prior
  simpa only [entranceProgram,ha.2.1,entranceState,entranceData,filterData,initialData] using h

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.entrance_program_correct
