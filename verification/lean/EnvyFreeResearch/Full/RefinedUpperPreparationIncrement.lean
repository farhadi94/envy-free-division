import EnvyFreeResearch.Full.RefinedUpperStabilityRecordedProcedure
import EnvyFreeResearch.Full.RefinedUpperStabilityPointTransport

/-! The universal linear-functional stability bound applies to physical
partial-cell measures normalized by the realized retained buffer. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperGridInterpolation RefinedUpperPeeling
variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

lemma domainCumulative_sub (μ : Measure ℝ) [IsFiniteMeasure μ]
    (buffer : List Component) (l r : ℝ) (hlr : l ≤ r) :
    domainCumulative μ buffer r-domainCumulative μ buffer l =
      μ.real (domain buffer ∩ Ioc l r) := by
  have he : (domain buffer ∩ Iic r) \ (domain buffer ∩ Iic l) = domain buffer ∩ Ioc l r := by
    ext x
    simp only [mem_sdiff,mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · rintro ⟨⟨hb,hr⟩,hn⟩
      exact ⟨hb,lt_of_not_ge (fun h => hn ⟨hb,h⟩),hr⟩
    · rintro ⟨hb,hl,hr⟩
      exact ⟨⟨hb,hr⟩,fun h => (not_le_of_gt hl) h.2⟩
  rw [← he,measureReal_sdiff (inter_subset_inter_right _ (Iic_subset_Iic.mpr hlr))
    ((domain_measurable buffer).inter measurableSet_Iic)]
  rfl

/-- Normalizers may depend on the entire realized grid; stability was proved
for every linear functional simultaneously. -/
theorem intervalValues_renormalized (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (active : Agent → Fin n) (origin : UpperCorrectionExecution.State n)
    (a : Agent) (hpositive : 0 < (μ (active a)).real (domain origin.cells))
    (l r : ℝ) (hlr : l ≤ r) (normalizer : ℝ) :
    ((μ (active a)).real (domain origin.cells)/normalizer) *
      intervalValues (physicalCumulative μ active origin) a (l,r) =
        (μ (active a)).real (domain origin.cells ∩ Ioc l r)/normalizer := by
  have hn : 0 ≤ physicalCumulative μ active origin a r-physicalCumulative μ active origin a l :=
    sub_nonneg.mpr (physicalCumulative_monotone μ active origin a hlr)
  rw [intervalValues,max_eq_right hn]
  unfold physicalCumulative
  rw [← sub_div,domainCumulative_sub _ _ l r hlr]
  field_simp

end EnvyFreeResearch.Full.RefinedUpperPreparation
