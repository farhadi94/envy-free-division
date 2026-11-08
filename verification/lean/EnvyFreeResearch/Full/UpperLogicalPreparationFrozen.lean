import EnvyFreeResearch.Full.UpperLogicalPreparationMass

/-!
# Fixed pre-sample reserve and the final recorded reserve are the same set

The frozen reserve has a concrete component representation using the coarse
quantile execution and the zero-length fine tape. It is independent of the
later fine samples. The final state has exactly this domain and retains all
later history, allowing the aggregate theorem to use distinct fixed error
and sampling domains without reconstructing histories from sample points.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperGridCells
  UpperLogicalCells UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperCommonGrid Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

def frozenReserveState (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ)
    (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) : State n :=
  reserveState policy active origin q 0 (fun i => Fin.elim0 i) theta labels

theorem frozenReserveState_history (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ)
    (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    (frozenReserveState policy active origin q theta labels).history =
      (UpperRecordedQuantiles.run policy active origin q).2.history := rfl

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem frozenReserveState_domain (q : ℕ) (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    domain (frozenReserveState policy active origin q theta labels).cells =
      labelledUnion (UpperRecordedQuantiles.logicalCells policy active origin q) theta labels :=
  reserveState_domain μ policy hpolicy active origin hgood hpositive q 0 _ theta labels

theorem final_reserve_eq_frozen (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) :
    domain (reserveState policy active origin q m draw theta labels).cells =
      domain (frozenReserveState policy active origin q theta labels).cells :=
  (reserveState_domain μ policy hpolicy active origin hgood hpositive q m draw theta labels).trans
    (frozenReserveState_domain μ policy hpolicy active origin hgood hpositive q theta labels).symm

theorem frozenReserveState_wellFormed (q : ℕ) (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    WellFormed μ (frozenReserveState policy active origin q theta labels) :=
  reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q 0 _ theta labels

theorem reserveState_subset (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) :
    domain (reserveState policy active origin q m draw theta labels).cells ⊆ domain origin.cells := by
  rw [reserveState_domain μ policy hpolicy active origin hgood hpositive q m draw theta labels]
  intro x hx
  obtain ⟨p, hp⟩ := mem_iUnion.mp hx
  by_cases hl : labels p ≤ theta
  · have hc : x ∈ UpperRecordedQuantiles.logicalCells policy active origin q p := by
      simpa only [hl, ite_true] using hp
    exact cell_subset _ _ p hc
  · simp only [hl, ite_false, mem_empty_iff_false] at hp

end Correctness

/-- If the permanent coarse-grid count fits inside the fine-sample budget,
the retained logical-cell count has the exact `2*theta*m/cap` tail bound. -/
theorem recorded_reserve_count_probability (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Agent × I) (theta : I) (cap : ℝ) (hcap : 0 < cap)
    (hgrid : count (Agent := Agent) q + 1 ≤ m) :
    UpperReserve.labelLaw {labels | cap <
      ((reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels).card : ℝ)} ≤
      ENNReal.ofReal (2 * (theta : ℝ) * m / cap) := by
  apply (reserveCells_count_probability _ theta cap hcap).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hcap.le
  have hcount : (Fintype.card (Fin (count (Agent := Agent) q + m + 1)) : ℝ) ≤ 2 * m := by
    simp only [Fintype.card_fin]
    exact_mod_cast (by omega : count (Agent := Agent) q + m + 1 ≤ 2 * m)
  nlinarith [mul_le_mul_of_nonneg_left hcount theta.property.1]

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem freeze_middle_measurable {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (f : (A × B) × C → D) (hf : Measurable f) (b : B) :
    Measurable (fun p : A × C => f ((p.1, b), p.2)) :=
  hf.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

theorem frozenReserveState_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q : ℕ) (theta : I) :
    Measurable (fun p : State n × (Fin (count (Agent := Agent) q + 1) → I) =>
      frozenReserveState policy active p.1 q theta p.2) := by
  have h := freeze_middle_measurable
    (fun p : (State n × (Fin 0 → Agent × I)) × (Fin (count (Agent := Agent) q + 1) → I) =>
      reserveState policy active p.1.1 q 0 p.1.2 theta p.2)
    (reserveState_measurable policy hpolicy active q 0 theta) (fun i : Fin 0 => Fin.elim0 i)
  exact h

end Measurability

end EnvyFreeResearch.Full.UpperLogicalPreparation
