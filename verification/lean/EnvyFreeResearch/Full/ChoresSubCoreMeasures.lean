import EnvyFreeResearch.Full.ChoresSubCorePhysicalEndpoint

/-! Exact original-measure guarantees of the completed physical SubCore
programs. Parent-dependent observer masks and offsets are explicit, and
zero-affine whole outputs remain assigned physical records. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCoreEntry
open Set MeasureTheory QueryProgram Persistent SubCore SubCorePhysical SubCoreLeaves Suffix IntervalOracle
open scoped Classical
variable {n : ℕ} {Agent Root : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Root] [Nonempty Root]

def affineUtility (cost : Fin n → Measure ℝ) (domains : Root → Fin n → Set ℝ)
    (offset : Root → Fin n → ℝ) (p : Root) (i : Fin n) (x : ℝ) : ℝ :=
  (cost i).real (physicalSuffix domains p i x)-offset p i

def clippedUtility (cost : Fin n → Measure ℝ) (domains : Root → Fin n → Set ℝ)
    (offset : Root → Fin n → ℝ) (p : Root) (i : Fin n) (x : ℝ) : ℝ :=
  max 0 (affineUtility cost domains offset p i x)

structure PhysicalCorrect (utility : Root → Fin n → ℝ → ℝ) (agent : Agent → Fin n)
    (out : Allocation Agent Root (OrderedRecord n)) : Prop where
  point : ∀ p, (out.point p).record.point ∈ Icc (0 : ℝ) 1
  best : ∀ i p, utility p (agent i) (out.point p).record.point ≤
    utility (out.assigned i) (agent i) (out.point (out.assigned i)).record.point
  unused : ∀ p, (∀ i, out.assigned i ≠ p) → (out.point p).record.point = 1
  whole : ∃ i, (out.point (out.assigned i)).record.point = 1
  nonnegative : ∀ i, 0 ≤ utility (out.assigned i) (agent i) (out.point (out.assigned i)).record.point

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (domains : Root → Fin n → Set ℝ) (offset total : Root → Fin n → ℝ)

theorem affine_record_values (store : Store Root (Record n))
    (point : Root → OrderedRecord n) :
    letI := affineValidity (fun p => Masked.rowProfile cost (domains p)) offset total
    WellFormed id (affineBaseline offset) store → Records id store id point →
      ∀ p, (point p).record.point ∈ Icc (0 : ℝ) 1 ∧
        ∀ i, ((point p).record.formal i).1 = affineUtility cost domains offset p i (point p).record.point := by
  letI := affineValidity (fun p => Masked.rowProfile cost (domains p)) offset total
  intro hs hr p
  obtain ⟨r,hm,heq⟩ := hr p
  have hv := hs.valid p r hm
  change AffineSound (Masked.rowProfile cost (domains p)) (offset p) r ∧ r.point ∈ Icc (0 : ℝ) 1 at hv
  change r = (point p).record at heq
  rw [heq] at hv
  exact ⟨hv.2,fun i => affine_primary_physical cost domains offset p (point p).record hv.1 hv.2 i⟩

theorem clipped_record_values (store : Store Root (ClippedRecord n))
    (point : Root → OrderedRecord n) :
    letI := clippedValidity (fun p => Masked.rowProfile cost (domains p)) offset total
    WellFormed ClippedRecord.record clippedBaseline store → Records ClippedRecord.record store id point →
      ∀ p, (point p).record.point ∈ Icc (0 : ℝ) 1 ∧
        ∀ i, ((point p).record.formal i).1 = clippedUtility cost domains offset p i (point p).record.point := by
  letI := clippedValidity (fun p => Masked.rowProfile cost (domains p)) offset total
  intro hs hr p
  obtain ⟨r,hm,heq⟩ := hr p
  have hv := hs.valid p r hm
  change ClippedSound (Masked.rowProfile cost (domains p)) (offset p) r ∧ r.record.point ∈ Icc (0 : ℝ) 1 at hv
  refine ⟨heq ▸ hv.2,?_⟩
  intro i
  have h := clipped_primary_physical cost domains offset p r hv.1 hv.2 i
  rw [heq] at h
  exact h

theorem affine_allocation_physical (agent : Agent → Fin n) (store : Store Root (Record n))
    (out : Allocation Agent Root (OrderedRecord n)) :
    letI := affineValidity (fun p => Masked.rowProfile cost (domains p)) offset total
    WellFormed id (affineBaseline offset) store → Records id store id out.point →
    SubCore.AllocationCorrect (cachedValue agent) univ (affineWholeRecords offset total)
      (fun i => affineBaseline offset (agent i)) out →
    (∀ i, 0 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1) →
    PhysicalCorrect (affineUtility cost domains offset) agent out := by
  letI := affineValidity (fun p => Masked.rowProfile cost (domains p)) offset total
  intro hs hr ha hn
  have hv := affine_record_values cost domains offset total store out.point hs hr
  refine ⟨fun p => (hv p).1,?_,?_,?_,?_⟩
  · intro i p
    have h := primary_mono (ha.2.1 i p)
    change ((out.point p).record.formal (agent i)).1 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1 at h
    rwa [(hv p).2 (agent i),(hv (out.assigned i)).2 (agent i)] at h
  · intro p hp
    have h := congrArg (fun r : OrderedRecord n => r.record.point) (ha.2.2.2.1 p hp)
    exact h
  · obtain ⟨i,hi⟩ := ha.2.2.2.2
    exact ⟨i,congrArg (fun r : OrderedRecord n => r.record.point) hi⟩
  · intro i
    rw [← (hv (out.assigned i)).2 (agent i)]
    exact hn i

theorem clipped_allocation_physical (agent : Agent → Fin n) (store : Store Root (ClippedRecord n))
    (out : Allocation Agent Root (OrderedRecord n)) :
    letI := clippedValidity (fun p => Masked.rowProfile cost (domains p)) offset total
    WellFormed ClippedRecord.record clippedBaseline store → Records ClippedRecord.record store id out.point →
    SubCore.AllocationCorrect (cachedValue agent) univ (clippedWholeRecords offset total)
      (fun i => clippedBaseline (agent i)) out →
    PhysicalCorrect (clippedUtility cost domains offset) agent out := by
  letI := clippedValidity (fun p => Masked.rowProfile cost (domains p)) offset total
  intro hs hr ha
  have hv := clipped_record_values cost domains offset total store out.point hs hr
  refine ⟨fun p => (hv p).1,?_,?_,?_,fun _ => le_max_left _ _⟩
  · intro i p
    have h := primary_mono (ha.2.1 i p)
    change ((out.point p).record.formal (agent i)).1 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1 at h
    rwa [(hv p).2 (agent i),(hv (out.assigned i)).2 (agent i)] at h
  · intro p hp
    exact congrArg (fun r : OrderedRecord n => r.record.point) (ha.2.2.2.1 p hp)
  · obtain ⟨i,hi⟩ := ha.2.2.2.2
    exact ⟨i,congrArg (fun r : OrderedRecord n => r.record.point) hi⟩

variable (cache : Masked.Cache Root n) (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
    (agent : Agent → Fin n) (hoffset : ∀ p i, 0 ≤ offset p i)
    (hpositive : 0 < Fintype.card Agent) (hmany : Fintype.card Agent < Fintype.card Root)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
include hc hoffset hpositive hpolicy

theorem affine_measures_protocol
    (hwholeNonneg : ∀ p i, 0 ≤ (cost (agent i)).real (domains p (agent i))-offset p (agent i)) :
    ∃ store out next trace,
      AdaptiveOracle.run (affinePhysicalProgram agent offset cache hmany.le).protocol oracle ()
        (physicalBudget n (Fintype.card Agent)) [] = ⟨trace,OracleProtocol.Stop.returned ((store,some out),next)⟩ ∧
      PhysicalCorrect (affineUtility cost domains offset) agent out ∧
      trace.length ≤ physicalBudget n (Fintype.card Agent) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card Agent) ∧
      Masked.CacheCorrect (measureProfile cost) domains next := by
  have hn : ∀ p i, 0 ≤ cachedTotals cache p (agent i)-offset p (agent i) := by
    intro p i
    rw [cached_totals_measure cost domains cache hc]
    exact hwholeNonneg p i
  obtain ⟨store,out,next,trace,hexec,hs,_,hr,ha,hown,hQ,hC,hcache⟩ := affine_physical_correct
    cost domains cache hc agent offset hoffset hpositive hmany oracle hpolicy hn []
  exact ⟨store,out,next,trace,hexec.run _ hQ,
    affine_allocation_physical cost domains offset (cachedTotals cache) agent store out hs hr ha hown,hQ,hC,hcache⟩

theorem clipped_measures_protocol :
    ∃ store out next trace,
      AdaptiveOracle.run (clippedPhysicalProgram agent offset cache hmany.le).protocol oracle ()
        (physicalBudget n (Fintype.card Agent)) [] = ⟨trace,OracleProtocol.Stop.returned ((store,some out),next)⟩ ∧
      PhysicalCorrect (clippedUtility cost domains offset) agent out ∧
      trace.length ≤ physicalBudget n (Fintype.card Agent) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card Agent) ∧
      Masked.CacheCorrect (measureProfile cost) domains next := by
  obtain ⟨store,out,next,trace,hexec,hs,_,hr,ha,_,hQ,hC,hcache⟩ := clipped_physical_correct
    cost domains cache hc agent offset hoffset hpositive hmany oracle hpolicy []
  exact ⟨store,out,next,trace,hexec.run _ hQ,
    clipped_allocation_physical cost domains offset (cachedTotals cache) agent store out hs hr ha,hQ,hC,hcache⟩

end EnvyFreeResearch.Full.Chores.SubCoreEntry
