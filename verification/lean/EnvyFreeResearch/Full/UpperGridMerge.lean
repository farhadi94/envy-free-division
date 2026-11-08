import EnvyFreeResearch.Full.UpperRecordedQuantiles

/-!
# The actual common quantile-plus-sample grid

The deterministic recorded quantile stage runs first, then the recorded iid
sampler sees its entire history. The merged logical grid has `k*q+m+1` cell
indices regardless of old physical joins, and the returned physical state
has the correct cache for all original observers.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperGridMerge

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalCells UpperCommonGrid UpperRecordedQuantiles UpperQuantileBounds
  UpperMixtureSampling UpperAdaptiveProduct Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

def prepare (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) : (Fin (count (Agent := Agent) q) → ℝ) × (Fin m → ℝ) × State n :=
  let coarse := UpperRecordedQuantiles.run policy active origin q
  (coarse.1, UpperRecordedGrid.execute policy active coarse.2 m draw)

def cuts (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) : Fin (count (Agent := Agent) q + m + 2) → ℝ :=
  let result := prepare policy active origin q m draw
  grid (Fin.append result.1 result.2.1)

def logicalCells (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) : Fin (count (Agent := Agent) q + m + 1) → Set ℝ :=
  cell (domain origin.cells) (cuts policy active origin q m draw)

theorem prepare_domain (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) : domain (prepare policy active origin q m draw).2.2.cells = domain origin.cells := by
  rw [prepare, UpperRecordedGrid.execute_domain, UpperRecordedQuantiles.run_domain]

theorem query_bound (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) :
    (prepare policy active origin q m draw).2.2.history.length ≤
      origin.history.length + (Fintype.card Agent * q + m) * (n + 1) := by
  have hc := UpperRecordedQuantiles.query_bound policy active origin q
  have hs := UpperRecordedGrid.query_bound policy active (UpperRecordedQuantiles.run policy active origin q).2 m draw
  simp only [Nat.add_mul]
  simpa only [prepare, Nat.add_assoc] using hs.trans (Nat.add_le_add_right hc (m * (n + 1)))

theorem cut_bound (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) :
    ((prepare policy active origin q m draw).2.2.history.map Prod.fst).countP isCut ≤
      (origin.history.map Prod.fst).countP isCut + Fintype.card Agent * q + m := by
  exact (UpperRecordedGrid.cut_bound policy active (UpperRecordedQuantiles.run policy active origin q).2 m draw).trans
    (Nat.add_le_add_right (UpperRecordedQuantiles.cut_bound policy active origin q) _)

/-- Every old coarse endpoint remains a boundary of the merged logical grid. -/
theorem grid_append_contains {a b : ℕ} (left : Fin a → ℝ) (right : Fin b → ℝ)
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1) (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (i : Fin (a + 2)) : ∃ j, grid (Fin.append left right) j = grid left i := by
  have hbound : ∀ j, Fin.append left right j ∈ Icc (0 : ℝ) 1 := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro r
      simpa only [Fin.append_left] using hleft r
    · intro r
      simpa only [Fin.append_right] using hright r
  have hraw : ∀ r : Fin (a + 2), ∃ j, grid (Fin.append left right) j = raw left r := by
    intro r
    refine Fin.lastCases ?_ (fun s => ?_) r
    · exact ⟨Fin.last (a + b + 1), by rw [grid_last _ hbound]; simp [raw]⟩
    · refine Fin.cases ?_ (fun s => ?_) s
      · exact ⟨0, by rw [grid_first _ hbound]; simp [raw]⟩
      · obtain ⟨j, hj⟩ := grid_contains (Fin.append left right) (s.castAdd b)
        refine ⟨j, ?_⟩
        simpa only [Fin.append_left, raw_endpoint] using hj
  exact hraw (UpperSortedGrid.select (raw left) i)

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem coarse_good (q : ℕ) : WellFormed μ (UpperRecordedQuantiles.run policy active origin q).2 :=
  UpperRecordedQuantiles.run_wellFormed μ policy hpolicy active origin hgood hpositive q

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)] hpolicy hgood in
theorem coarse_positive (q : ℕ) (a : Agent) :
    0 < (μ (active a)).real (domain (UpperRecordedQuantiles.run policy active origin q).2.cells) := by
  rw [UpperRecordedQuantiles.run_domain]
  exact hpositive a

theorem prepare_wellFormed (q m : ℕ) (draw : Fin m → Agent × I) :
    WellFormed μ (prepare policy active origin q m draw).2.2 :=
  UpperRecordedGrid.execute_wellFormed μ policy hpolicy active _
    (coarse_good μ policy hpolicy active origin hgood hpositive q)
    (coarse_positive μ policy active origin hpositive q) m draw

theorem coarse_endpoints (q : ℕ) (i : Fin (count (Agent := Agent) q)) :
    (UpperRecordedQuantiles.run policy active origin q).1 i ∈ Icc (0 : ℝ) 1 :=
  UpperRecordedGrid.execute_endpoints μ policy hpolicy active origin hgood hpositive _ _ i

theorem sampled_endpoints (q m : ℕ) (draw : Fin m → Agent × I) (i : Fin m) :
    (prepare policy active origin q m draw).2.1 i ∈ Icc (0 : ℝ) 1 :=
  UpperRecordedGrid.execute_endpoints μ policy hpolicy active _
    (coarse_good μ policy hpolicy active origin hgood hpositive q)
    (coarse_positive μ policy active origin hpositive q) m draw i

theorem merged_endpoints (q m : ℕ) (draw : Fin m → Agent × I)
    (i : Fin (count (Agent := Agent) q + m)) :
    Fin.append (prepare policy active origin q m draw).1 (prepare policy active origin q m draw).2.1 i ∈ Icc (0 : ℝ) 1 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, prepare] using coarse_endpoints μ policy hpolicy active origin hgood hpositive q j
  · intro j
    simpa only [Fin.append_right] using sampled_endpoints μ policy hpolicy active origin hgood hpositive q m draw j

theorem cuts_endpoints (q m : ℕ) (draw : Fin m → Agent × I) :
    cuts policy active origin q m draw 0 = 0 ∧
      cuts policy active origin q m draw (Fin.last (count (Agent := Agent) q + m + 1)) = 1 :=
  ⟨grid_first _ (merged_endpoints μ policy hpolicy active origin hgood hpositive q m draw),
    grid_last _ (merged_endpoints μ policy hpolicy active origin hgood hpositive q m draw)⟩

theorem contains_coarse (q m : ℕ) (draw : Fin m → Agent × I) (i : Fin (count (Agent := Agent) q + 2)) :
    ∃ j, cuts policy active origin q m draw j = UpperRecordedQuantiles.cuts policy active origin q i :=
  grid_append_contains _ _ (coarse_endpoints μ policy hpolicy active origin hgood hpositive q)
    (sampled_endpoints μ policy hpolicy active origin hgood hpositive q m draw) i

theorem logical_cells_small (q m : ℕ) (draw : Fin m → Agent × I)
    (a : Agent) (i : Fin (count (Agent := Agent) q + m + 1)) :
    (μ (active a)).real (logicalCells policy active origin q m draw i) /
      (μ (active a)).real (domain origin.cells) ≤ 1 / (q + 1 : ℝ) := by
  have hquant : ∀ j : Fin (q + 2), 0 < j.val → j.val < q + 1 →
      ∃ c, cdf (cond (μ (active a)) (domain origin.cells)) (cuts policy active origin q m draw c) =
        (j.val : ℝ) / (q + 1) := by
    intro j hj0 hjq
    obtain ⟨c, hc⟩ := UpperCommonGrid.quantiles_present μ policy hpolicy active
      (fun a => values origin (active a)) origin.cells hgood.1 hgood.2.1
      (fun a => values_correct μ origin hgood (active a)) hpositive q origin.history a j hj0 hjq
    obtain ⟨d, hd⟩ := contains_coarse μ policy hpolicy active origin hgood hpositive q m draw c
    refine ⟨d, ?_⟩
    rw [hd, UpperRecordedQuantiles.cuts_eq_common μ policy active origin hgood]
    exact hc
  have h := normalized_cell_mass_le (Nat.succ_pos q) (μ (active a)) (domain origin.cells)
    (domain_measurable origin.cells) (hpositive a) (cuts policy active origin q m draw) (grid_monotone _)
    (fun j hj0 hjq => by simpa only [Nat.cast_succ] using hquant j hj0 hjq) i
  simpa only [logicalCells, Nat.cast_succ] using h

theorem logical_partition (q m : ℕ) (draw : Fin m → Agent × I) :
    Pairwise (fun i j => Disjoint (logicalCells policy active origin q m draw i)
      (logicalCells policy active origin q m draw j)) ∧
    (∀ i, MeasurableSet (logicalCells policy active origin q m draw i)) ∧
    (⋃ i, logicalCells policy active origin q m draw i) = domain origin.cells := by
  have he := cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  refine ⟨cells_disjoint _ _ (grid_monotone _), cell_measurable _ (domain_measurable origin.cells) _, ?_⟩
  apply cells_cover _ _ (grid_monotone _)
  change domain origin.cells ⊆ Icc (cuts policy active origin q m draw 0)
    (cuts policy active origin q m draw (Fin.last (count (Agent := Agent) q + m + 1)))
  rw [he.1, he.2]
  exact domain_subset_unit origin.cells

end Correctness

/-- The logical index bound used by Repair counts no old physical joins. -/
theorem logical_count_le (q m : ℕ) (h : Fintype.card Agent * q + 1 ≤ m) :
    Fintype.card (Fin (count (Agent := Agent) q + m + 1)) ≤ 2 * m := by
  simp only [Fintype.card_fin, count, Fintype.card_prod, Fintype.card_fin]
  omega

section Distribution

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [Nonempty Agent]

/-- The later samples are iid from the original buffer mixture, even though
their oracle replies see the full deterministic quantile-stage history. -/
theorem iid_sample_law (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Agent → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) :
    MeasurePreserving (fun draw => (prepare policy active origin q m draw).2.1)
      (tapeLaw (seedLaw Agent) m) (tapeLaw (mixture μ active origin.cells) m) := by
  have h := UpperRecordedGrid.iid_law μ policy hpolicy hmeas active
    (UpperRecordedQuantiles.run policy active origin q).2
    (coarse_good μ policy hpolicy active origin hgood hpositive q)
    (coarse_positive μ policy active origin hpositive q) m
  have hm : mixture μ active (UpperRecordedQuantiles.run policy active origin q).2.cells =
      mixture μ active origin.cells := by
    unfold mixture
    rw [UpperRecordedQuantiles.run_domain]
  simpa only [prepare, hm] using h

end Distribution

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem prepare_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q m : ℕ) :
    Measurable (fun p : State n × (Fin m → Agent × I) => prepare policy active p.1 q m p.2) := by
  have hcoarse : Measurable (fun p : State n × (Fin m → Agent × I) =>
      UpperRecordedQuantiles.run policy active p.1 q) :=
    (UpperRecordedQuantiles.run_measurable policy hpolicy active q).comp measurable_fst
  have hsample := (UpperRecordedGrid.execute_measurable policy hpolicy active m).comp
    ((measurable_snd.comp hcoarse).prodMk measurable_snd)
  exact (measurable_fst.comp hcoarse).prodMk hsample

theorem cuts_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q m : ℕ) :
    Measurable (fun p : State n × (Fin m → Agent × I) => cuts policy active p.1 q m p.2) := by
  have hr := prepare_measurable policy hpolicy active q m
  apply grid_measurable
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_fst.comp hr)
  · intro j
    simpa only [Fin.append_right, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp hr))

end Measurability

end EnvyFreeResearch.Full.UpperGridMerge
