import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationSupported
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationNear
import EnvyFreeResearch.Full.UpperSnapshotSmallActualRows

/-! Deterministic interpolation consequences for the actual candidate.
The simultaneous supported event remains an explicit hypothesis here. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity
variable {n m J : ℕ} {Row Generated : Type*} [Fintype Row] [Nonempty Row]

theorem estimate_eq_signed (a : Row → Fin (m+1) → ℝ) (cells : Fin (m+1) → Set ℝ)
    (i j : Row) (piece : Set ℝ) (hpiece : MeasurableSet piece) :
    UpperEnvelope.estimate a (UpperEnvelope.uniformCells cells) i j piece =
      signedEstimate (fun e => a i e-a j e) cells piece := by
  rw [signedEstimate_apply _ _ _ hpiece]
  rfl

theorem supported_interpolation_error (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (origin : State n) (cuts : Fin (m+2) → ℝ) (points : Generated → ℝ) (eps : ℝ)
    (hgood : ¬ BadSupportedRecordedUnion μ normalizer origin.cells cuts points eps)
    (piece : List Component)
    (hsupported : ∃ virtual, RecordedEndpoints cuts points virtual ∧
      domain piece=domain origin.cells ∩ domain virtual) (i j : Row) :
    |(μ i).real (domain piece)/normalizer i-(μ j).real (domain piece)/normalizer j-
      signedEstimate (fun e => physicalRows μ normalizer origin.cells cuts i e-
        physicalRows μ normalizer origin.cells cuts j e)
        (cell (domain origin.cells) cuts) (domain piece)| ≤
      eps*distance (physicalRows μ normalizer origin.cells cuts) i j := by
  obtain ⟨virtual,hv,hp⟩ := hsupported
  have hh : |(μ i).real (domain piece)/normalizer i-(μ j).real (domain piece)/normalizer j-
      UpperEnvelope.estimate (physicalRows μ normalizer origin.cells cuts)
        (UpperEnvelope.uniformCells (cell (domain origin.cells) cuts)) i j (domain piece)| ≤
      eps*distance (physicalRows μ normalizer origin.cells cuts) i j := by
    by_contra h
    exact hgood ⟨i,j,virtual,domain piece,hv,hp,lt_of_not_ge h⟩
  rwa [estimate_eq_signed _ _ i j _ (domain_measurable piece)] at hh

theorem supported_normalized_error (μ : Row → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (origin : State n) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (points : Generated → ℝ) (eps : ℝ)
    (hgood : ¬ BadSupportedRecordedUnion μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts points eps)
    (piece : List Component)
    (hsupported : ∃ virtual, RecordedEndpoints cuts points virtual ∧
      domain piece=domain origin.cells ∩ domain virtual) (i j : Row)
    (hi : 0 < (μ i).real (domain origin.cells)) (hj : 0 < (μ j).real (domain origin.cells)) :
    |(μ i).real (domain piece)/(μ i).real (domain origin.cells)-
      (μ j).real (domain piece)/(μ j).real (domain origin.cells)| ≤
      (1/2+eps)*distance (physicalRows μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts) i j := by
  have he := supported_interpolation_error μ (fun i => (μ i).real (domain origin.cells))
    origin cuts points eps hgood piece hsupported i j
  have hz := (normalized_physical_scores (μ i) (μ j) origin cuts hzero hone hmono hi hj).1
  exact normalized_error_of_interpolation _ _ hz _ (domain_measurable piece) _ _ eps he

variable (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (origin : State n) (hdis : DisjointComponents origin.cells)
    (cutter : Fin n) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (points : Generated → ℝ)
    (hfirst : ∀ j, ∃ e, points e=(firstRun policy origin cutter cuts selected t first).1 j)
    (hsecond : ∀ j, ∃ e, points e=(secondRun (J:=J) policy origin cutter cuts selected t first second).1 j)
    (eps : ℝ)
    (hgood : ¬ BadSupportedRecordedUnion μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts points eps)
include hdis hzero hone hmono hsep hfirst hsecond hgood

theorem actualAllocation_normalized_errors (hJ : 0 < J) (i j : Row)
    (hi : 0 < (μ i).real (domain origin.cells)) (hj : 0 < (μ j).real (domain origin.cells)) :
    (∀ a, |(μ i).real (domain ((actualAllocation hJ policy origin cutter cuts selected t first second).1 a).cells)/(μ i).real (domain origin.cells)-
      (μ j).real (domain ((actualAllocation hJ policy origin cutter cuts selected t first second).1 a).cells)/(μ j).real (domain origin.cells)| ≤
      (1/2+eps)*distance (physicalRows μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts) i j) ∧
    (|(μ i).real (domain (actualAllocation hJ policy origin cutter cuts selected t first second).2.1.cells)/(μ i).real (domain origin.cells)-
      (μ j).real (domain (actualAllocation hJ policy origin cutter cuts selected t first second).2.1.cells)/(μ j).real (domain origin.cells)| ≤
      (1/2+eps)*distance (physicalRows μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts) i j) := by
  have hs := actualAllocation_supported policy origin hdis cutter cuts hzero hone hmono hsep selected t first second points hfirst hsecond hJ
  exact ⟨fun a => supported_normalized_error μ origin cuts hzero hone hmono points eps hgood _ (hs.1 a) i j hi hj,
    supported_normalized_error μ origin cuts hzero hone hmono points eps hgood _ hs.2 i j hi hj⟩

end EnvyFreeResearch.Full.UpperSnapshotSmall
