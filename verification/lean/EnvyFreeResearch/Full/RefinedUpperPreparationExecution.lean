import EnvyFreeResearch.Full.RefinedUpperPreparationData
import EnvyFreeResearch.Full.RefinedUpperPreparationLogical
import EnvyFreeResearch.Full.RefinedUpperPreparationMass

/-! Completion and deterministic supply of the actual new preparation. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRepairJobs UpperRecordedQuantiles UpperLogicalIsolation Chores
open scoped Classical unitInterval
variable {n k : ℕ} [Nonempty (Fin k)]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

/-- The total fallback is never used under the stated parent supply. -/
theorem dataResult_spec (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2*(jobCount k*L) < q+1) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    dataRun active origin data L = some (dataResult active origin data L) ∧
      (dataResult active origin data L).1.length = Fintype.card (Job k × Fin L) ∧
      (dataResult active origin data L).2.card ≤ 2*(jobCount k*L) := by
  have hb : (((∅ : Finset (Parent k q)).card+2*(requests k L).length : ℕ) : ℝ) * (1/(q+1 : ℝ)) < 1 := by
    simp only [Finset.card_empty,zero_add,requests_length,mul_one_div]
    apply (div_lt_one (by positivity : (0 : ℝ) < q+1)).mpr
    exact_mod_cast hbudget
  obtain ⟨pairs,final,hexec,hlen,_,hcard⟩ := RefinedUpperPeeling.recorded_run_completes
    μ policy hpolicy active origin hgood hpositive q m draw (requests k L) ∅ hb
  have he : dataRun active origin (UpperGridMerge.prepare policy active origin q m draw) L = some (pairs,final) := hexec
  simp only [dataResult,he,Option.getD_some,Prod.fst,Prod.snd]
  refine ⟨trivial,?_,?_⟩
  · simpa only [requests,UpperWitnessExtraction.roundJobs,List.length_ofFn] using hlen
  · simpa only [Finset.card_empty,zero_add,requests_length] using hcard

omit hpolicy hgood hpositive in
/-- Actual returned reserve equals the deterministic physical mask. -/
theorem dataRetained_execute (q m L : ℕ) (draw : Fin m → Fin k × I) :
    dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L =
      retainedState policy active origin q m draw
        (dataResult active origin (UpperGridMerge.prepare policy active origin q m draw) L).2 := rfl

theorem dataRetained_half (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 4*(jobCount k*L) ≤ q+1) (i : Fin k) :
    (μ (active i)).real (domain origin.cells)/2 ≤
      (μ (active i)).real (domain (dataRetained active origin
        (UpperGridMerge.prepare policy active origin q m draw) L).cells) := by
  have hb : 2*(jobCount k*L) < q+1 := by omega
  have hs := (dataResult_spec μ policy hpolicy active origin hgood hpositive q m L draw hb).2.2
  rw [dataRetained_execute]
  exact retainedState_half μ policy hpolicy active origin hgood hpositive q m draw _ (by omega) i

end EnvyFreeResearch.Full.RefinedUpperPreparation
