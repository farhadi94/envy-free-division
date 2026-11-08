import EnvyFreeResearch.Full.UpperSnapshotContrastSelection

/-! Deterministic finite-table choices for Snapshot. Disagreement here is
the sum of absolute cell differences, not the maximum-cell Repair gap. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
variable {Cell : Type*} [Fintype Cell]

def selectMax (fallback : Cell) (score : Cell → ℝ) : Cell :=
  (Finset.univ.toList.argmax score).getD fallback

theorem selectMax_spec (fallback : Cell) (score : Cell → ℝ) (c : Cell) :
    score c ≤ score (selectMax fallback score) := by
  have hmem : c ∈ (Finset.univ : Finset Cell).toList := by simp
  obtain ⟨a, ha⟩ := UpperRepresentatives.argmax_exists score Finset.univ.toList (List.ne_nil_of_mem hmem)
  have hm := List.le_of_mem_argmax hmem (by simp [ha] : a ∈ Finset.univ.toList.argmax score)
  simpa only [selectMax, ha, Option.getD_some] using hm

variable {X : Type*} [MeasurableSpace X]

theorem selectMax_measurable [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (fallback : Cell) (score : X → Cell → ℝ) (hscore : ∀ c, Measurable (fun x => score x c)) :
    Measurable (fun x => selectMax fallback (score x)) :=
  ProtocolMeasurable.measurable_option_cases (present := fun _ c => c) (absent := fun _ => fallback)
    (UpperRepresentatives.argmax_measurable Finset.univ.toList score hscore) measurable_snd measurable_const

/-- A zero-total signed row has a positive cell at least its absolute mass
sum divided by twice its number of cells. The selected cell is explicit. -/
theorem selectMax_signed (fallback : Cell) (score : Cell → ℝ) (hsum : ∑ c, score c = 0) :
    (∑ c, |score c|) / (2 * Fintype.card Cell) ≤ score (selectMax fallback score) := by
  let M := score (selectMax fallback score)
  have hcard : (0 : ℝ) < Fintype.card Cell := by
    have : Nonempty Cell := ⟨fallback⟩
    exact_mod_cast Fintype.card_pos
  have hmax (c : Cell) : score c ≤ M := selectMax_spec fallback score c
  have hm : 0 ≤ M := by
    have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset Cell)) => hmax c)
    simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    nlinarith
  have habs (c : Cell) : |score c| ≤ 2 * M - score c := by
    apply abs_le.mpr
    constructor <;> linarith [hmax c]
  have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset Cell)) => habs c)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum, sub_zero] at h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Fintype.card Cell)).mpr
  nlinarith

variable {Agent : Type*}

def rowDistance (values : Agent → Cell → ℝ) (cutter row : Agent) : ℝ :=
  ∑ c, |values row c - values cutter c|

def positiveCell (fallback : Cell) (values : Agent → Cell → ℝ) (cutter row : Agent) : Cell :=
  selectMax fallback (fun c => values row c - values cutter c)

def negativeCell (fallback : Cell) (values : Agent → Cell → ℝ) (cutter row : Agent) : Cell :=
  selectMax fallback (fun c => values cutter c - values row c)

theorem rowDistance_nonnegative (values : Agent → Cell → ℝ) (cutter row : Agent) :
    0 ≤ rowDistance values cutter row := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem rowDistance_self (values : Agent → Cell → ℝ) (cutter : Agent) :
    rowDistance values cutter cutter = 0 := by simp [rowDistance]

theorem rowDistance_measurable (values : X → Agent → Cell → ℝ)
    (hvalues : ∀ i c, Measurable (fun x => values x i c)) (cutter row : Agent) :
    Measurable (fun x => rowDistance (values x) cutter row) :=
  Finset.measurable_sum _ (fun c _ => ((hvalues row c).sub (hvalues cutter c)).abs)

/-- Actual positive and negative signed-extreme choices, including their
strict distinctness whenever the selected row has positive disagreement. -/
theorem signed_cells (fallback : Cell) (values : Agent → Cell → ℝ) (cutter row : Agent)
    (hrow : ∑ c, values row c = 1) (hcutter : ∑ c, values cutter c = 1)
    (hD : 0 < rowDistance values cutter row) :
    rowDistance values cutter row / (2 * Fintype.card Cell) ≤
        values row (positiveCell fallback values cutter row) - values cutter (positiveCell fallback values cutter row) ∧
      rowDistance values cutter row / (2 * Fintype.card Cell) ≤
        values cutter (negativeCell fallback values cutter row) - values row (negativeCell fallback values cutter row) ∧
      positiveCell fallback values cutter row ≠ negativeCell fallback values cutter row := by
  have hp := selectMax_signed fallback (fun c => values row c - values cutter c)
    (by rw [Finset.sum_sub_distrib, hrow, hcutter]; ring)
  have hn := selectMax_signed fallback (fun c => values cutter c - values row c)
    (by rw [Finset.sum_sub_distrib, hcutter, hrow]; ring)
  have hp' : rowDistance values cutter row / (2 * Fintype.card Cell) ≤
      values row (positiveCell fallback values cutter row) - values cutter (positiveCell fallback values cutter row) := hp
  have hn' : rowDistance values cutter row / (2 * Fintype.card Cell) ≤
      values cutter (negativeCell fallback values cutter row) - values row (negativeCell fallback values cutter row) := by
    simpa only [rowDistance, negativeCell, abs_sub_comm] using hn
  refine ⟨hp', hn', ?_⟩
  intro heq
  have hcard : (0 : ℝ) < Fintype.card Cell := by
    have : Nonempty Cell := ⟨fallback⟩
    exact_mod_cast Fintype.card_pos
  have hpos : 0 < rowDistance values cutter row / (2 * Fintype.card Cell) := div_pos hD (by positivity)
  rw [heq] at hp'
  linarith

end EnvyFreeResearch.Full.UpperSnapshotCandidates
