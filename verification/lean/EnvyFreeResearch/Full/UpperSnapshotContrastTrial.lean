import EnvyFreeResearch.Full.UpperSnapshotContrastProbability

/-! Whole-trial probability accounting with an arbitrary full history and
later randomness. A projection law retains the independent fresh seed tape. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
open UpperLogicalIsolation UpperRepairJobs
variable {k L : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

theorem intersection_lower (Q : Measure Ω) [IsProbabilityMeasure Q] (S G : Set Ω)
    (a delta : ℝ) (hS : a ≤ Q.real S) (hfailure : Q.real Gᶜ ≤ delta) :
    a - delta ≤ Q.real (S ∩ G) := by
  have hsub : S ⊆ (S ∩ G) ∪ Gᶜ := by
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inl ⟨hx, hg⟩
    · exact Or.inr hg
  have hm := measureReal_mono (μ := Q) hsub
  have hu := measureReal_union_le (μ := Q) (S ∩ G) Gᶜ
  linarith

/-- Arbitrary additional tape/history is allowed, provided its preparation
and fresh seed projection has the original product law. Repair failure is
subtracted once from the unconditional preservation event. -/
theorem original_trial_preservation (hk : 2 ≤ k) (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (projection : Ω → X × IsolationDraw k L)
    (hprojection : MeasurePreserving projection Q (P.prod (isolationLaw k L)))
    (w : X → Job k → Fin L → Fin k → ℝ) (old : X → Fin k → Fin k → ℝ)
    (chosen : X → Selection k) (hw : ∀ j a i, Measurable (fun x => w x j a i))
    (hchosen : Measurable chosen) (G : Set Ω) (delta : ℝ) (hfailure : Q.real Gᶜ ≤ delta) :
    1 / 2 - delta ≤ Q.real {z | z ∈ G ∧
      contrast (old (projection z).1) (chosen (projection z).1).1.1 (chosen (projection z).1).1.2
        (chosen (projection z).1).2.1 (chosen (projection z).1).2.2 ≤
      contrast (coreMatrix hk (w (projection z).1) (old (projection z).1) (projection z).2.1 (projection z).2.2)
        (chosen (projection z).1).1.1 (chosen (projection z).1).1.2
        (chosen (projection z).1).2.1 (chosen (projection z).1).2.2} := by
  let S : Set (X × IsolationDraw k L) := {p | 0 ≤ selectedSeed hk w chosen p}
  have hm : MeasurableSet S := measurableSet_le measurable_const (selectedSeed_measurable hk w chosen hw hchosen)
  have hhalf := ENNReal.toReal_mono (measure_ne_top (P.prod (isolationLaw k L)) S)
    (family_half hk P w chosen hw hchosen)
  have hreal : (1 / 2 : ℝ) ≤ Q.real (projection ⁻¹' S) := by
    rw [hprojection.measureReal_preimage hm.nullMeasurableSet]
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hhalf
  have hb := intersection_lower Q (projection ⁻¹' S) G (1 / 2) delta hreal hfailure
  apply hb.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  refine ⟨hz.2, ?_⟩
  exact contrast_preserved hk (w (projection z).1) (old (projection z).1)
    (chosen (projection z).1).1.1 (chosen (projection z).1).1.2
    (chosen (projection z).1).2.1 (chosen (projection z).1).2.2 (projection z).2 hz.1

/-- The displayed manuscript constant follows from a whole-trial failure
probability strictly below one sixty-fourth, without conditioning on return. -/
theorem original_trial_preservation_strict (hk : 2 ≤ k) (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (projection : Ω → X × IsolationDraw k L)
    (hprojection : MeasurePreserving projection Q (P.prod (isolationLaw k L)))
    (w : X → Job k → Fin L → Fin k → ℝ) (old : X → Fin k → Fin k → ℝ)
    (chosen : X → Selection k) (hw : ∀ j a i, Measurable (fun x => w x j a i))
    (hchosen : Measurable chosen) (G : Set Ω) (hfailure : Q.real Gᶜ < 1 / 64) :
    31 / 64 < Q.real {z | z ∈ G ∧
      contrast (old (projection z).1) (chosen (projection z).1).1.1 (chosen (projection z).1).1.2
        (chosen (projection z).1).2.1 (chosen (projection z).1).2.2 ≤
      contrast (coreMatrix hk (w (projection z).1) (old (projection z).1) (projection z).2.1 (projection z).2.2)
        (chosen (projection z).1).1.1 (chosen (projection z).1).1.2
        (chosen (projection z).1).2.1 (chosen (projection z).1).2.2} := by
  have hb := original_trial_preservation hk P Q projection hprojection w old chosen hw hchosen G
    (Q.real Gᶜ) le_rfl
  linarith

end EnvyFreeResearch.Full.UpperSnapshotContrast
