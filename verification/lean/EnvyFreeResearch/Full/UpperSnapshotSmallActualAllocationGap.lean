import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationInterpolation
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationWitness

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity
variable {n m J : ℕ} {Row Generated : Type*} [Fintype Row] [Nonempty Row]

theorem contrast_transfer (x₁ x₂ y₁ y₂ z₁ z₂ error gap : ℝ)
    (h₁ : |x₁-y₁-z₁| ≤ error) (h₂ : |x₂-y₂-z₂| ≤ error)
    (hy : y₁=y₂) (hz : gap ≤ z₁-z₂) : gap-2*error ≤ x₁-x₂ := by
  have h₁ := (abs_le.mp h₁).1
  have h₂ := (abs_le.mp h₂).2
  linarith

variable (μ : Row → Measure ℝ)
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

theorem actualAllocation_physical_gap (hJ : 2 ≤ J) (i j : Row) (gap : ℝ)
    (hequal : (μ j).real (domain ((actualAllocation (J:=J) (by omega) policy origin cutter cuts selected t first second).1 ⟨0,by omega⟩).cells)=
      (μ j).real (domain ((actualAllocation (J:=J) (by omega) policy origin cutter cuts selected t first second).1 ⟨1,by omega⟩).cells))
    (hwitness : gap ≤ candidateContrast hJ policy origin cutter cuts selected t
      (signedEstimate (fun e => physicalRows μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts i e-
        physicalRows μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts j e)
        (cell (domain origin.cells) cuts)) (first,second)) :
    gap-2*eps*distance (physicalRows μ (fun i => (μ i).real (domain origin.cells)) origin.cells cuts) i j ≤
      (μ i).real (domain ((actualAllocation (J:=J) (by omega) policy origin cutter cuts selected t first second).1 ⟨0,by omega⟩).cells)/(μ i).real (domain origin.cells)-
      (μ i).real (domain ((actualAllocation (J:=J) (by omega) policy origin cutter cuts selected t first second).1 ⟨1,by omega⟩).cells)/(μ i).real (domain origin.cells) := by
  have hs := (actualAllocation_supported policy origin hdis cutter cuts hzero hone hmono hsep selected t first second points hfirst hsecond (by omega : 0<J)).1
  have h₁ := supported_interpolation_error μ (fun i => (μ i).real (domain origin.cells)) origin cuts points eps hgood _ (hs ⟨0,by omega⟩) i j
  have h₂ := supported_interpolation_error μ (fun i => (μ i).real (domain origin.cells)) origin cuts points eps hgood _ (hs ⟨1,by omega⟩) i j
  rw [actual_witness_pair] at hwitness
  have hh := contrast_transfer _ _ _ _ _ _ _ gap h₁ h₂ (congrArg (fun x => x/(μ j).real (domain origin.cells)) hequal) hwitness
  nlinarith

omit [Fintype Row] [Nonempty Row] hdis hzero hone hmono hsep hfirst hsecond hgood in
theorem witness_margin_arithmetic (hJ : 0 < J) (D eps : ℝ) (hD : 0 ≤ D)
    (heps : eps ≤ 3/(64*(J:ℝ))) : D/(32*(J:ℝ)) ≤ D/(8*(J:ℝ))-2*eps*D := by
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  have he := mul_le_mul_of_nonneg_right heps hD
  have hid : D/(8*(J:ℝ))-2*(3/(64*(J:ℝ))*D)=D/(32*(J:ℝ)) := by field_simp; ring
  linarith

end EnvyFreeResearch.Full.UpperSnapshotSmall
