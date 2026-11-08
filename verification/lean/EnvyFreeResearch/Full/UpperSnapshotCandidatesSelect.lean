import EnvyFreeResearch.Full.UpperSnapshotCandidatesTable

/-! First-tie selected row and signed cells are Borel in the complete cached
table. The comparison family remains fixed before the later row choice. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
variable {k m : ℕ}

def selectedRow (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter : Fin k) : Fin k :=
  selectMax ⟨0, hk⟩ (rowDistance values cutter)

def selectedDistance (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter : Fin k) : ℝ :=
  rowDistance values cutter (selectedRow hk values cutter)

def selectedPositive (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter : Fin k) : Fin (m + 1) :=
  positiveCell 0 values cutter (selectedRow hk values cutter)

def selectedNegative (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter : Fin k) : Fin (m + 1) :=
  negativeCell 0 values cutter (selectedRow hk values cutter)

theorem selectedRow_spec (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter i : Fin k) :
    rowDistance values cutter i ≤ selectedDistance hk values cutter := selectMax_spec _ _ i

theorem selectedRow_ne (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hD : 0 < selectedDistance hk values cutter) : selectedRow hk values cutter ≠ cutter := by
  intro heq
  simp only [selectedDistance, heq, rowDistance_self, lt_self_iff_false] at hD

theorem selected_signed_cells (hk : 0 < k) (values : Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hnormal : ∀ i, ∑ e, values i e = 1) (hD : 0 < selectedDistance hk values cutter) :
    selectedDistance hk values cutter / (2 * (m + 1 : ℕ)) ≤
      values (selectedRow hk values cutter) (selectedPositive hk values cutter) - values cutter (selectedPositive hk values cutter) ∧
    selectedDistance hk values cutter / (2 * (m + 1 : ℕ)) ≤
      values cutter (selectedNegative hk values cutter) - values (selectedRow hk values cutter) (selectedNegative hk values cutter) ∧
    selectedPositive hk values cutter ≠ selectedNegative hk values cutter := by
  simpa only [Fintype.card_fin, selectedDistance, selectedPositive, selectedNegative] using signed_cells 0 values cutter (selectedRow hk values cutter)
    (hnormal _) (hnormal cutter) hD

variable {X : Type*} [MeasurableSpace X]

theorem selectedRow_measurable (hk : 0 < k) (values : X → Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hvalues : ∀ i e, Measurable (fun x => values x i e)) :
    Measurable (fun x => selectedRow hk (values x) cutter) :=
  selectMax_measurable _ _ (rowDistance_measurable values hvalues cutter)

theorem selected_value_measurable (hk : 0 < k) (values : X → Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hvalues : ∀ i e, Measurable (fun x => values x i e)) (e : Fin (m + 1)) :
    Measurable (fun x => values x (selectedRow hk (values x) cutter) e) :=
  (UpperRepresentatives.score_eval_measurable (fun x i => values x i e) (fun i => hvalues i e)).comp
    (measurable_id.prodMk (selectedRow_measurable hk values cutter hvalues))

theorem selectedDistance_measurable (hk : 0 < k) (values : X → Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hvalues : ∀ i e, Measurable (fun x => values x i e)) :
    Measurable (fun x => selectedDistance hk (values x) cutter) :=
  (UpperRepresentatives.score_eval_measurable (fun x i => rowDistance (values x) cutter i)
    (rowDistance_measurable values hvalues cutter)).comp
      (measurable_id.prodMk (selectedRow_measurable hk values cutter hvalues))

theorem selectedPositive_measurable (hk : 0 < k) (values : X → Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hvalues : ∀ i e, Measurable (fun x => values x i e)) :
    Measurable (fun x => selectedPositive hk (values x) cutter) :=
  selectMax_measurable _ _ (fun e => (selected_value_measurable hk values cutter hvalues e).sub (hvalues cutter e))

theorem selectedNegative_measurable (hk : 0 < k) (values : X → Fin k → Fin (m + 1) → ℝ) (cutter : Fin k)
    (hvalues : ∀ i e, Measurable (fun x => values x i e)) :
    Measurable (fun x => selectedNegative hk (values x) cutter) :=
  selectMax_measurable _ _ (fun e => (hvalues cutter e).sub (selected_value_measurable hk values cutter hvalues e))

end EnvyFreeResearch.Full.UpperSnapshotCandidates
