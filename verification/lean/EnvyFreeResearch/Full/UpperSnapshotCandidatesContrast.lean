import EnvyFreeResearch.Full.UpperSnapshotCandidatesSelect

/-! Reserve-normalized large-branch contrasts use the two-sided mass check.
The selected row/label orientation is an explicit Borel finite choice. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperSnapshotContrast
variable {k m : ℕ}

theorem scaled_difference (x y r s delta : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hy : 0 ≤ y) (hdelta : delta ≤ x - y) :
    delta / r ≤ x / r - y / s := by
  calc
    delta / r ≤ (x - y) / r := div_le_div_of_nonneg_right hdelta hr.le
    _ = x / r - y / r := sub_div x y r
    _ ≤ x / r - y / s := sub_le_sub_left (div_le_div_of_nonneg_left hy hr hrs) _

theorem scaled_large_threshold (D M theta r : ℝ) (hD : 0 ≤ D) (hM : 0 < M)
    (hr : 0 < r) (hupper : r ≤ 3 * theta / 2) :
    D / (3 * theta * M) ≤ (D / (2 * M)) / r := by
  have hden : (2 * M) * r ≤ 3 * theta * M := by
    have h := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 2 * M)
    nlinarith
  rw [div_div]
  exact div_le_div_of_nonneg_left hD (by positivity) hden

def largeSelection (hk : 3 ≤ k) (row cutter : Fin k) (reserve : Fin k → ℝ) : (Fin k × Fin k) × (Fin k × Fin k) :=
  if reserve row ≤ reserve cutter then ((row, cutter), (⟨0, by omega⟩, ⟨2, by omega⟩))
  else ((cutter, row), (⟨1, by omega⟩, ⟨2, by omega⟩))

/-- The actual finite choice compares the appropriate signed cell with the
empty third endowment. Both possible reserve-normalization orders are proved. -/
theorem largeSelection_contrast (hk : 3 ≤ k) (values : Fin k → Fin (m + 1) → ℝ)
    (row cutter : Fin k) (F G : Fin (m + 1)) (old : Fin k → Fin k → ℝ)
    (reserve : Fin k → ℝ) (hreserve : ∀ i, 0 < reserve i) (theta D : ℝ)
    (hD : 0 ≤ D) (hupper : ∀ i, reserve i ≤ 3 * theta / 2)
    (hnonnegative : ∀ i e, 0 ≤ values i e)
    (hpositive : D / (2 * (m + 1 : ℕ)) ≤ values row F - values cutter F)
    (hnegative : D / (2 * (m + 1 : ℕ)) ≤ values cutter G - values row G)
    (hfirst : ∀ i, old i ⟨0, by omega⟩ = values i F / reserve i)
    (hsecond : ∀ i, old i ⟨1, by omega⟩ = values i G / reserve i)
    (hempty : ∀ i, old i ⟨2, by omega⟩ = 0) :
    let c := largeSelection hk row cutter reserve
    D / (3 * theta * (m + 1 : ℕ)) ≤ contrast old c.1.1 c.1.2 c.2.1 c.2.2 := by
  unfold largeSelection
  split_ifs with horder
  · simp only [contrast, hfirst, hempty, sub_zero, add_zero]
    exact (scaled_large_threshold D (m + 1 : ℕ) theta (reserve row) hD (by positivity)
      (hreserve row) (hupper row)).trans
      (scaled_difference _ _ _ _ _ (hreserve row) horder (hnonnegative cutter F) hpositive)
  · simp only [contrast, hsecond, hempty, sub_zero, add_zero]
    exact (scaled_large_threshold D (m + 1 : ℕ) theta (reserve cutter) hD (by positivity)
      (hreserve cutter) (hupper cutter)).trans
      (scaled_difference _ _ _ _ _ (hreserve cutter) (le_of_not_ge horder)
        (hnonnegative row G) hnegative)

variable {X : Type*} [MeasurableSpace X]

theorem largeSelection_measurable (hk : 3 ≤ k) (row : X → Fin k) (cutter : Fin k)
    (reserve : X → Fin k → ℝ) (hrow : Measurable row) (hreserve : ∀ i, Measurable (fun x => reserve x i)) :
    Measurable (fun x => largeSelection hk (row x) cutter (reserve x)) := by
  have hr : Measurable (fun x => reserve x (row x)) :=
    (UpperRepresentatives.score_eval_measurable reserve hreserve).comp (measurable_id.prodMk hrow)
  exact ((hrow.prodMk measurable_const).prodMk measurable_const).ite
    (measurableSet_le hr (hreserve cutter)) ((measurable_const.prodMk hrow).prodMk measurable_const)

end EnvyFreeResearch.Full.UpperSnapshotCandidates
