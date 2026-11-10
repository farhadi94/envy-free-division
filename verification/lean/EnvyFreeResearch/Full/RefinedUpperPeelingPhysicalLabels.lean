import EnvyFreeResearch.Full.RefinedUpperPeelingTransport

/-! Exact physical interval labels for the recorded max-determinant run. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open MeasureTheory Set UpperGridParents UpperLogicalCells UpperRecordedDomain
  UpperCorrectionExecution UpperCircularStage UpperStageMeasurable UpperCommonGrid Chores
open scoped Classical BigOperators unitInterval

/-- The parent depends only on the two physical endpoints, including null
intervals. The special ownership of zero is redundant for the parent search. -/
def intervalFits {a : ℕ} (coarse : Fin (a+2) → ℝ) (interval : ℝ × ℝ) (j : Fin (a+1)) : Prop :=
  coarse j.castSucc ≤ interval.1 ∧ interval.2 ≤ coarse j.succ

def firstIntervalParent {a : ℕ} (coarse : Fin (a+2) → ℝ) (interval : ℝ × ℝ) :
    List (Fin (a+1)) → Fin (a+1)
  | [] => 0
  | j::js => if intervalFits coarse interval j then j else firstIntervalParent coarse interval js

def intervalParent {a : ℕ} (coarse : Fin (a+2) → ℝ) (interval : ℝ × ℝ) : Fin (a+1) :=
  firstIntervalParent coarse interval Finset.univ.toList

def intervalLabel {m : ℕ} (fine : Fin (m+2) → ℝ) (i : Fin (m+1)) : ℝ × ℝ :=
  (fine i.castSucc,fine i.succ)

lemma fits_iff_intervalFits {a b : ℕ} (coarse : Fin (a+2) → ℝ) (fine : Fin (b+2) → ℝ)
    (hc : Monotone coarse) (hc0 : coarse 0 = 0) (hf0 : fine 0 = 0)
    (hcz : ∀ j, coarse j = 0 → j = 0) (i : Fin (b+1)) (j : Fin (a+1)) :
    Fits coarse fine i j ↔ intervalFits coarse (intervalLabel fine i) j := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1⟩
  · intro h
    refine ⟨h.1,h.2,?_⟩
    intro hi
    have hl := h.1
    change coarse j.castSucc ≤ fine i.castSucc at hl
    rw [hi,Fin.castSucc_zero,hf0] at hl
    have hz : coarse j.castSucc = 0 := le_antisymm hl (by rw [← hc0]; exact hc (Fin.zero_le _))
    have hj := hcz j.castSucc hz
    apply Fin.ext
    exact congrArg (fun z : Fin (a+2) => z.val) hj

lemma firstParent_interval {a b : ℕ} (coarse : Fin (a+2) → ℝ) (fine : Fin (b+2) → ℝ)
    (hc : Monotone coarse) (hc0 : coarse 0 = 0) (hf0 : fine 0 = 0)
    (hcz : ∀ j, coarse j = 0 → j = 0) (i : Fin (b+1)) (js : List (Fin (a+1))) :
    firstParent coarse fine i js = firstIntervalParent coarse (intervalLabel fine i) js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [firstParent,firstIntervalParent,fits_iff_intervalFits coarse fine hc hc0 hf0 hcz,ih]

theorem parent_interval {a b : ℕ} (coarse : Fin (a+2) → ℝ) (fine : Fin (b+2) → ℝ)
    (hc : Monotone coarse) (hc0 : coarse 0 = 0) (hf0 : fine 0 = 0)
    (hcz : ∀ j, coarse j = 0 → j = 0) (i : Fin (b+1)) :
    UpperGridParents.parent coarse fine i = intervalParent coarse (intervalLabel fine i) :=
  firstParent_interval coarse fine hc hc0 hf0 hcz i _

variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

def intervalRows (μ : Fin n → Measure ℝ) (active : Agent → Fin n) (origin : State n)
    (a : Agent) (interval : ℝ × ℝ) : ℝ :=
  (μ (active a)).real (domain origin.cells ∩ Ioc interval.1 interval.2) /
    (μ (active a)).real (domain origin.cells)

lemma intervalRows_nonneg (μ : Fin n → Measure ℝ) (active : Agent → Fin n) (origin : State n)
    (a : Agent) (interval : ℝ × ℝ) : 0 ≤ intervalRows μ active origin a interval :=
  div_nonneg measureReal_nonneg measureReal_nonneg

/-- The cache is exactly the physical mass of the interval label. This also
holds for the first cell and repeated endpoints, by nonatomicity. -/
theorem recorded_table_interval (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent)
    (i : Fin (UpperRecordedQuantiles.count (Agent := Agent) q + m + 1)) :
    UpperGridCache.table policy active origin q m draw a i =
      intervalRows μ active origin a (intervalLabel (UpperGridMerge.cuts policy active origin q m draw) i) := by
  rw [UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive]
  unfold UpperGridMerge.logicalCells intervalRows intervalLabel
  rw [measureReal_congr (cell_ae_eq (μ (active a)) (domain origin.cells)
    (UpperGridMerge.cuts policy active origin q m draw) i)]

theorem recorded_parent_interval (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I)
    (i : Fin (UpperRecordedQuantiles.count (Agent := Agent) q + m + 1)) :
    UpperRecordedParents.parent policy active origin q m draw i =
      intervalParent (UpperRecordedQuantiles.cuts policy active origin q)
        (intervalLabel (UpperGridMerge.cuts policy active origin q m draw) i) := by
  apply parent_interval _ _ (grid_monotone _)
    (UpperRecordedQuantiles.cuts_endpoints μ policy hpolicy active origin hgood hpositive q).1
    (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
    (UpperGridInterior.coarse_zero_only μ policy hpolicy active origin hgood hpositive q)

/-- Exact transport of the actual cached run to the same physical interval
universe for every grid size. Neither injectivity nor positive cell length is
required, so repeated permanent endpoints cause no exceptional branch. -/
theorem recorded_run_physical (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent)) :
    let label := intervalLabel (UpperGridMerge.cuts policy active origin q m draw)
    run (intervalRows μ active origin)
      (intervalParent (UpperRecordedQuantiles.cuts policy active origin q))
      (List.ofFn label) jobs ∅ =
      (representativeRun policy active origin q m draw jobs).map
        (fun result => (result.1.map (fun p => (label p.1,label p.2)),result.2)) := by
  dsimp only
  have hv : (fun a => intervalRows μ active origin a ∘
      intervalLabel (UpperGridMerge.cuts policy active origin q m draw)) =
      UpperGridCache.table policy active origin q m draw := by
    funext a i
    exact (recorded_table_interval μ policy hpolicy active origin hgood hpositive q m draw a i).symm
  have hp : intervalParent (UpperRecordedQuantiles.cuts policy active origin q) ∘
      intervalLabel (UpperGridMerge.cuts policy active origin q m draw) =
      UpperRecordedParents.parent policy active origin q m draw := by
    funext i
    exact (recorded_parent_interval μ policy hpolicy active origin hgood hpositive q m draw i).symm
  have hm := run_map (intervalLabel (UpperGridMerge.cuts policy active origin q m draw))
    (intervalRows μ active origin) (intervalParent (UpperRecordedQuantiles.cuts policy active origin q))
    (List.ofFn (fun i : Fin (UpperRecordedQuantiles.count (Agent := Agent) q + m + 1) => i)) jobs ∅
  rw [hv,hp] at hm
  simpa only [List.map_ofFn,Function.comp_def,representativeRun] using hm

end EnvyFreeResearch.Full.RefinedUpperPeeling
