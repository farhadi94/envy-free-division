import EnvyFreeResearch.Full.UpperSnapshotContrastMatrix

/-! Symmetry, including ties, is averaged on the original independent
preparation and seed tape. No successful-table conditional law is used. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
open UpperLogicalIsolation UpperRepairJobs
variable {k L : ℕ}

/-- Negation symmetry puts at least half the probability on the closed
nonnegative half-line; atoms at zero are retained. -/
theorem nonnegative_half {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (score : X → ℝ) (hscore : Measurable score)
    (flip : X → X) (hflip : MeasurePreserving flip P P)
    (hneg : ∀ x, score (flip x) = -score x) :
    (1 / 2 : ℝ) ≤ P.real {x | 0 ≤ score x} := by
  have hm : MeasurableSet {x | 0 ≤ score x} := measurableSet_le measurable_const hscore
  have hp : flip ⁻¹' {x | 0 ≤ score x} = {x | score x ≤ 0} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hneg]
    exact neg_nonneg
  have he := hflip.measureReal_preimage hm.nullMeasurableSet
  rw [hp] at he
  have hu : {x | 0 ≤ score x} ∪ {x | score x ≤ 0} = univ := by
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total 0 (score x)
  have hb := measureReal_union_le (μ := P) {x | 0 ≤ score x} {x | score x ≤ 0}
  rw [hu, he] at hb
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hb
  change (1 : ℝ) ≤ P.real {x | 0 ≤ score x} + P.real {x | 0 ≤ score x} at hb
  linarith

theorem seed_half (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (i h u v : Fin k) :
    (1 / 2 : ℝ) ≤ (isolationLaw k L).real {t | 0 ≤ seedContrast hk w i h u v t} :=
  nonnegative_half _ _ (measurable_of_countable _) _
    (relabel_preserves hk (Equiv.swap u v)) (seedContrast_swap hk w i h u v)

theorem seed_half_ennreal (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (i h u v : Fin k) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ (isolationLaw k L) {t | 0 ≤ seedContrast hk w i h u v t} := by
  have hb := ENNReal.ofReal_le_ofReal (seed_half hk w i h u v)
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hb

abbrev Selection (k : ℕ) := (Fin k × Fin k) × (Fin k × Fin k)

def selectedSeed {X : Type*} (hk : 2 ≤ k) (w : X → Job k → Fin L → Fin k → ℝ)
    (chosen : X → Selection k) (p : X × IsolationDraw k L) : ℝ :=
  seedContrast hk (w p.1) (chosen p.1).1.1 (chosen p.1).1.2 (chosen p.1).2.1 (chosen p.1).2.2 p.2

variable {X : Type*} [MeasurableSpace X]

theorem selectedSeed_measurable (hk : 2 ≤ k) (w : X → Job k → Fin L → Fin k → ℝ)
    (chosen : X → Selection k) (hw : ∀ j a i, Measurable (fun x => w x j a i))
    (hchosen : Measurable chosen) : Measurable (selectedSeed hk w chosen) := by
  have hV := coreMatrix_measurable hk (fun p : X × IsolationDraw k L => w p.1)
    (fun _ _ _ => 0) (fun p => p.2.1) (fun p => p.2.2)
    (fun j a i => (hw j a i).comp measurable_fst) (fun _ _ => measurable_const)
    (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  have hfixed (c : Selection k) : Measurable (fun p : X × IsolationDraw k L =>
      seedContrast hk (w p.1) c.1.1 c.1.2 c.2.1 c.2.2 p.2) :=
    (((hV c.1.1 c.2.1).sub (hV c.1.2 c.2.1)).sub (hV c.1.1 c.2.2)).add (hV c.1.2 c.2.2)
  have hall : Measurable (fun p : (X × IsolationDraw k L) × Selection k =>
      seedContrast hk (w p.1.1) p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 p.1.2) :=
    measurable_from_prod_countable_left hfixed
  have hmap : Measurable (fun p : X × IsolationDraw k L => (p, chosen p.1)) :=
    measurable_id.prodMk (hchosen.comp measurable_fst)
  convert hall.comp hmap using 1
  rfl

/-- The row and old-label choice may depend on the entire preparation
parameter. Every fiber is evaluated on the original fresh seed law. -/
theorem family_half (hk : 2 ≤ k) (P : Measure X) [IsProbabilityMeasure P]
    (w : X → Job k → Fin L → Fin k → ℝ) (chosen : X → Selection k)
    (hw : ∀ j a i, Measurable (fun x => w x j a i)) (hchosen : Measurable chosen) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ (P.prod (isolationLaw k L)) {p | 0 ≤ selectedSeed hk w chosen p} := by
  rw [Measure.prod_apply (measurableSet_le measurable_const (selectedSeed_measurable hk w chosen hw hchosen))]
  calc
    _ = ∫⁻ _x, ENNReal.ofReal (1 / 2 : ℝ) ∂P := by simp
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      exact seed_half_ennreal hk (w x) (chosen x).1.1 (chosen x).1.2 (chosen x).2.1 (chosen x).2.2

end EnvyFreeResearch.Full.UpperSnapshotContrast
