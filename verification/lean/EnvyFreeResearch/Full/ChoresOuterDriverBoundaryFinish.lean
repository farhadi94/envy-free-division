import EnvyFreeResearch.Full.ChoresOuterLocalProgram
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryRemainder
import EnvyFreeResearch.Full.ChoresComponentPopulationFinishCoordinates

/-! Coordinate composition for the concrete terminal recursive branches.
The physical domain/cache and separation premises are explicit obligations
of the terminal geometry proof, while child provenance is the population IH. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Completion Population Boundary ComponentExtraction
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

variable (cost : Costs n) (data : Data n RootId) [Nonempty (Fin data.size)]
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ) (p : Fin n)
    (oldPrivate : RootId → Fin n → List (Parent n)) (R0 : List (Parent n))
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n), CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hold : DataKnown points original data)
    (hpriv : ∀ root q, CacheKnown points (oldPrivate root q)) (hR0 : CacheKnown points R0)
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
include hchildren hold hpriv hR0 hzero hone hpolicy

theorem finish_atomic_known (A B : Finset (Fin n))
    (hB : B.Nonempty ∧ B ≠ Finset.univ)
    (hmany : Fintype.card A < Fintype.card (Fin data.size))
    (out : ComponentClosed.Result (Root := Fin data.size) A)
    (hout : RecordedKnown id points out)
    (X R : Set ℝ)
    (hX : CacheValid (measureProfile cost.measure) X (extractedCache out))
    (hR : CacheValid (measureProfile cost.measure) R
      (fullResidueCache R0 (removePrivate (terminalPrivateCache data original A out oldPrivate)
        (Terminal.extractedSlots data A out))))
    (hsepB : ∀ i, (2 : ℝ)^(n+2)*(cost.measure (groupEmbedding B i)).real R ≤
      (cost.measure (groupEmbedding B i)).real X)
    (hsepD : ∀ i, (2 : ℝ)^(n+2)*(cost.measure (groupEmbedding Bᶜ i)).real X ≤
      (cost.measure (groupEmbedding Bᶜ i)).real R)
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (h : Executes oracle (finishClass data original r H p oldPrivate R0 children (.inl (A,B)) hmany out)
      prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  simp only [finishClass,dif_pos hB] at h
  apply atomic_program_known cost oracle hpolicy B hB.1 hB.2 _ X R _ _ hX hR hsepB hsepD
    children hchildren points _ _ _ hzero hone prior result trace h
  · exact terminal_full_allocation_known data original r H points hold p (.inl (A,B)) hmany out hout
  · exact extracted_cache_known points out id hout
  · apply full_residue_known points R0 _ hR0
    apply remove_private_known
    exact terminal_private_known data original A out points hold.snapshots hout oldPrivate hpriv

theorem finish_exhausted_known (A : Finset (Fin n))
    (hA : A.Nonempty ∧ A ≠ Finset.univ)
    (hmany : Fintype.card A < Fintype.card (Fin data.size))
    (out : ComponentClosed.Result (Root := Fin data.size) A)
    (hout : RecordedKnown id points out)
    (R : Set ℝ)
    (hR : CacheValid (measureProfile cost.measure) R
      (fullResidueCache R0 (terminalPrivateCache data original A out oldPrivate)))
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (h : Executes oracle (finishClass data original r H p oldPrivate R0 children (.inr A) hmany out)
      prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  simp only [finishClass,dif_pos hA] at h
  apply exhausted_program_known cost oracle hpolicy A hA.1 hA.2 _ R _ hR children hchildren
    points _ _ hzero hone prior result trace h
  · exact terminal_full_allocation_known data original r H points hold p (.inr A) hmany out hout
  · exact full_residue_known points R0 _ hR0
      (terminal_private_known data original A out points hold.snapshots hout oldPrivate hpriv)
end EnvyFreeResearch.Full.Chores.Outer
