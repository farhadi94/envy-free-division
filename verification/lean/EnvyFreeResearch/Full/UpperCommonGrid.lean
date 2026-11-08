import EnvyFreeResearch.Full.UpperSortedGrid

/-!
# The actual common quantile grid on a physical union

The grid sorts the endpoints returned by the ordinary-query quantile
executor, adjoining the physical resource bounds. Every logical cell has
every normalized row's value at most one quantile step. The literal partition
retains null endpoint material and its logical cell count ignores old joins.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperCommonGrid

open UpperCircularStage UpperRecordedDomain UpperQuantileExecution UpperQuantileBounds
  UpperLogicalCells UpperSortedGrid UpperStageMeasurable Chores

def raw {m : ℕ} (endpoints : Fin m → ℝ) : Fin (m + 2) → ℝ :=
  Fin.snoc (Fin.cons 0 endpoints) 1

def grid {m : ℕ} (endpoints : Fin m → ℝ) : Fin (m + 2) → ℝ := sorted (raw endpoints)

theorem raw_endpoint {m : ℕ} (endpoints : Fin m → ℝ) (i : Fin m) :
    raw endpoints i.succ.castSucc = endpoints i := by simp only [raw, Fin.snoc_castSucc, Fin.cons_succ]

theorem raw_bounds {m : ℕ} (endpoints : Fin m → ℝ)
    (h : ∀ i, endpoints i ∈ Icc (0 : ℝ) 1) (i : Fin (m + 2)) :
    0 ≤ raw endpoints i ∧ raw endpoints i ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [raw]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [raw]
    · simpa only [raw, Fin.snoc_castSucc, Fin.cons_succ, mem_Icc] using h j

theorem grid_monotone {m : ℕ} (endpoints : Fin m → ℝ) : Monotone (grid endpoints) :=
  sorted_monotone (raw endpoints)

theorem grid_contains {m : ℕ} (endpoints : Fin m → ℝ) (i : Fin m) :
    ∃ j, grid endpoints j = endpoints i := by
  obtain ⟨j, hj⟩ := sorted_contains (raw endpoints) i.succ.castSucc
  exact ⟨j, hj.trans (raw_endpoint endpoints i)⟩

theorem grid_first {m : ℕ} (endpoints : Fin m → ℝ)
    (h : ∀ i, endpoints i ∈ Icc (0 : ℝ) 1) : grid endpoints 0 = 0 := by
  apply first_eq_zero (raw endpoints) (fun i => (raw_bounds endpoints h i).1)
  exact ⟨0, by simp [raw]⟩

theorem grid_last {m : ℕ} (endpoints : Fin m → ℝ)
    (h : ∀ i, endpoints i ∈ Icc (0 : ℝ) 1) : grid endpoints (Fin.last (m + 1)) = 1 := by
  apply last_eq_one (raw endpoints) (fun i => (raw_bounds endpoints h i).2)
  exact ⟨Fin.last (m + 1), by simp [raw]⟩

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

def cuts (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ) (history : History n) :
    Fin (Fintype.card (Agent × Fin q) + 2) → ℝ :=
  grid (execution μ policy active cached cells q history).1

def logicalCells (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ) (history : History n) :
    Fin (Fintype.card (Agent × Fin q) + 1) → Set ℝ :=
  cell (domain cells) (cuts μ policy active cached cells q history)

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (cached : Agent → Component → ℝ) (cells : List Component)
  (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
  (hcache : ∀ a c, c ∈ cells → cached a c = mass (μ (active a)) c)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain cells)) (q : ℕ) (history : History n)

include hpolicy hordered hdisjoint hcache hpositive

theorem executed_endpoints_bounded (i : Fin (Fintype.card (Agent × Fin q))) :
    (execution μ policy active cached cells q history).1 i ∈ Icc (0 : ℝ) 1 := by
  let job := (Fintype.equivFin (Agent × Fin q)).symm i
  have h := (roots_spec μ policy hpolicy active cached cells hordered hdisjoint hcache hpositive
    q history job.1 job.2).1
  simpa only [root, jobIndex, Prod.mk.eta, job, Equiv.apply_symm_apply] using h

theorem cuts_endpoints : cuts μ policy active cached cells q history 0 = 0 ∧
    cuts μ policy active cached cells q history (Fin.last (Fintype.card (Agent × Fin q) + 1)) = 1 :=
  ⟨grid_first _ (executed_endpoints_bounded μ policy hpolicy active cached cells hordered hdisjoint
      hcache hpositive q history),
    grid_last _ (executed_endpoints_bounded μ policy hpolicy active cached cells hordered hdisjoint
      hcache hpositive q history)⟩

theorem quantiles_present (a : Agent) (j : Fin (q + 2)) (hjpos : 0 < j.val) (hjlt : j.val < q + 1) :
    ∃ c, cdf (cond (μ (active a)) (domain cells)) (cuts μ policy active cached cells q history c) =
      (j.val : ℝ) / (q + 1) := by
  let r : Fin q := ⟨j.val - 1, by omega⟩
  obtain ⟨c, hc⟩ := grid_contains (execution μ policy active cached cells q history).1 (jobIndex a r)
  refine ⟨c, ?_⟩
  change cuts μ policy active cached cells q history c = root μ policy active cached cells q history a r at hc
  rw [hc, (roots_spec μ policy hpolicy active cached cells hordered hdisjoint hcache hpositive q history a r).2]
  congr 1
  have hr : r.val + 1 = j.val := by dsimp [r]; omega
  exact_mod_cast hr

theorem logical_cells_small (a : Agent) (i : Fin (Fintype.card (Agent × Fin q) + 1)) :
    (μ (active a)).real (logicalCells μ policy active cached cells q history i) /
      (μ (active a)).real (domain cells) ≤ 1 / (q + 1 : ℝ) := by
  have h := normalized_cell_mass_le (Nat.succ_pos q) (μ (active a)) (domain cells) (domain_measurable cells)
    (hpositive a) (cuts μ policy active cached cells q history) (grid_monotone _)
    (fun j hjpos hjlt => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
        quantiles_present μ policy hpolicy active cached cells hordered hdisjoint hcache hpositive q history a j hjpos hjlt) i
  simpa only [logicalCells, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using h

/-- The common grid is a literal finite measurable partition of the
disconnected buffer, with exactly `k*q+1` logical cell indices. -/
theorem logical_partition :
    (Pairwise (fun i j => Disjoint (logicalCells μ policy active cached cells q history i)
      (logicalCells μ policy active cached cells q history j))) ∧
      (∀ i, MeasurableSet (logicalCells μ policy active cached cells q history i)) ∧
      (⋃ i, logicalCells μ policy active cached cells q history i) = domain cells := by
  have hends := cuts_endpoints μ policy hpolicy active cached cells hordered hdisjoint hcache hpositive q history
  refine ⟨cells_disjoint _ _ (grid_monotone _), cell_measurable _ (domain_measurable cells) _, ?_⟩
  apply cells_cover _ _ (grid_monotone _)
  change domain cells ⊆ Icc (cuts μ policy active cached cells q history 0)
    (cuts μ policy active cached cells q history (Fin.last (Fintype.card (Agent × Fin q) + 1)))
  rw [hends.1, hends.2]
  exact domain_subset_unit cells

end Correctness

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem raw_measurable {m : ℕ} (endpoints : X → Fin m → ℝ)
    (h : ∀ i, Measurable (fun x => endpoints x i)) : Measurable (fun x => raw (endpoints x)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [raw, Fin.snoc_last] using (measurable_const : Measurable (fun _ : X => (1 : ℝ)))
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [raw, Fin.snoc_castSucc, Fin.cons_zero] using
        (measurable_const : Measurable (fun _ : X => (0 : ℝ)))
    · simpa only [raw, Fin.snoc_castSucc, Fin.cons_succ] using h j

theorem grid_measurable {m : ℕ} (endpoints : X → Fin m → ℝ)
    (h : ∀ i, Measurable (fun x => endpoints x i)) : Measurable (fun x => grid (endpoints x)) :=
  sorted_measurable _ (fun i => (measurable_pi_apply i).comp (raw_measurable endpoints h))

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem cuts_measurable (μ : Fin n → Measure ℝ) (policy : Policy n)
    (hmeas : MeasurablePolicy policy) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ) :
    Measurable (cuts μ policy active cached cells q) :=
  grid_measurable _ (fun i => (measurable_pi_apply i).comp (measurable_fst.comp
    (execution_measurable μ policy hmeas active cached cells q)))

end Measurability

end EnvyFreeResearch.Full.UpperCommonGrid
