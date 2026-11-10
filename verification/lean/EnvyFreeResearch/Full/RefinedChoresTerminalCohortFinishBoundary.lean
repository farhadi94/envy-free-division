import EnvyFreeResearch.Full.RefinedChoresTerminalCohortDispatch
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortBoundary
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryRemainder
import EnvyFreeResearch.Full.ChoresComponentPopulationFinishCoordinates

/-! Coordinate provenance through both actual recursive terminal branches. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open QueryProgram Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentExtraction Chores.SubCoreEntry ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (oldPrivate : RootId → Fin n → List (Parent n)) (R0 : List (Parent n))

variable (cost : Population.Costs n)
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost.measure U c (original root))
    (good : data.Good original cost.measure r H)
    (hparts : PartsCorrect cost.measure
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
    (hcorrect : PhysicalCorrect (affineUtility cost.measure
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label)))
      Subtype.val out.allocation)
    (hvalid : (TerminalGroup.output data normal original r H group hr0 hH0 out).Valid)
    (hold : Outer.PrivateCorrect (measureProfile cost.measure) (fun root => (original root).piece) data.cache oldPrivate)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root a, G.piece root a = (original root).piece a)
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length)
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hR : CacheValid (measureProfile cost.measure) R R0) (hd : ∀ root a, Disjoint R (G.piece root a))
    (hsep : Clearance.Separated (Clearance.entries xs) cost.measure H R)
    (hr : ∀ i, 0 < (cost.measure i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost.measure i).real R)
    (J : ℕ) (hroots : Fintype.card RootId ≤ J) (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (children : Population.ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Population.CoordinateSpec cost (children k hkpos hklt agent))
include hsound good hparts hold hG horiginal hR hd hsep hr hH hscale hr_eq hroots hreserve hpolicy hchildren


open Chores.Boundary
variable (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
    (hcache : ∀ root a, CacheKnown points (data.cache root a))
    (hpriv : ∀ root a, CacheKnown points (oldPrivate root a)) (hR0 : CacheKnown points R0)
    (hout : RecordedKnown id points out)
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (homitted : ∀ s : Fin data.size, c ∉ ProtectedPivot.eligible
      (original (data.source s)) H r data.protectedLabel)
    (hwhole : ∃ j : group.terminalClass.participants, material (out.parts j).suffixParts =
      TerminalGroup.blocks data normal original r H group (out.allocation.assigned j) group.label)
    (hlarge : 2*(2 : ℝ)^(n+2) ≤ H) (hsmall : (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ H)
include hknown hcache hpriv hR0 hout hzero hone homitted hwhole hlarge hsmall

theorem TerminalGroup.finish_class_known
    (prior trace : History (Query (Fin n)) ℝ) (result : Completion.Allocation n (Fin n))
    (hex : Executes oracle
      (TerminalGroup.finishClass data normal original r H group hr0 hH0 out oldPrivate R0 children) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  have hbase : AllocationKnown points (TerminalGroup.base data normal original r H group hr0 hH0 out) :=
    Outer.pool_allocation_known points _ _
      (TerminalGroup.pool_cache_known data normal original r H group hr0 hH0 points hknown out hout hcache)
  have hprivate := TerminalGroup.pool_private_known data normal original r H group hr0 hH0 points hknown out hout oldPrivate hpriv
  cases ht : group.terminalClass with
  | inl pair =>
    rcases pair with ⟨A,B⟩
    have hpa : group.terminalClass.participants = A := by rw [ht]; rfl
    have htype : group.terminalClass = .inl (group.terminalClass.participants,B) := by rw [hpa]; exact ht
    have hb := TerminalGroup.atomic_extracted_bounds data normal original r H group out cost.measure c hsound hparts
      xs index horiginal R hsep hr hH hscale hr_eq B htype hwhole
    rw [TerminalGroup.finish_class_atomic data normal original r H group hr0 hH0 out oldPrivate R0 B hb.1 hb.2.1 htype children] at hex
    have hX := TerminalGroup.extracted_cache_correct data normal original r H group out cost.measure c hsound good hparts G hG
    have hrem := TerminalGroup.remainder_cache_correct data normal original r H group hr0 hH0 out oldPrivate cost.measure c hsound good hparts hold G hG R R0 hR hd
    have heq := Outer.full_removed_exact G
      (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
      (TerminalGroup.marked data normal original r H group out)
      (TerminalGroup.private_subset data normal original r H group hr0 hH0 out oldPrivate cost.measure c hsound good hparts hold G hG) R hd
    rw [TerminalGroup.marked_exact data normal original r H group hr0 hH0 out oldPrivate cost.measure good] at heq
    rw [← heq] at hrem
    have hu := TerminalGroup.remaining_bounds data normal original r H group hr0 hH0 out oldPrivate cost.measure c hsound good hparts hold G hG R hr_eq J hroots
    apply Population.atomic_program_known cost oracle hpolicy B hb.1 hb.2.1 _ (extracted out) _ _ _ hX hrem
      (fun i => Terminal.atomic_large_separation n J H ((2 : ℝ)^(n+2)) _ _ _ hH0 (by positivity)
        (hr _).le hreserve hlarge (hb.2.2.1 _ (Population.group_embedding_mem B i)) (hu _).2)
      (fun i => Terminal.atomic_small_separation n H ((2 : ℝ)^(n+2)) _ _ _ hH0 (by positivity)
        (hr _).le hsmall (hb.2.2.2 _ (Finset.mem_compl.mp (Population.group_embedding_mem Bᶜ i))) (hu _).1)
      children hchildren points hbase (Outer.extracted_cache_known points out id hout) _ hzero hone prior result trace hex
    apply Outer.full_residue_known points R0 _ hR0
    exact Outer.remove_private_known points _ _ hprivate
  | inr A =>
    have hpa : group.terminalClass.participants = A := by rw [ht]; rfl
    have htype : group.terminalClass = .inr group.terminalClass.participants := by rw [hpa]; exact ht
    have ha := TerminalGroup.admissible data normal original r H group cost.measure xs index c hsound horiginal R
      hsep hr hH hscale hr_eq homitted
    rw [TerminalGroup.finish_class_exhausted data normal original r H group hr0 hH0 out oldPrivate R0 ha.1 ha.2 htype children] at hex
    have hc := TerminalGroup.full_cache_correct data normal original r H group hr0 hH0 out cost.measure c hsound good hparts G hG oldPrivate hold R R0 hR hd
    exact Population.exhausted_program_known cost oracle hpolicy _ ha.1 ha.2 _ _ _ hc children hchildren
      points hbase (Outer.full_residue_known points R0 _ hR0 hprivate) hzero hone prior result trace hex

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.finish_class_known
