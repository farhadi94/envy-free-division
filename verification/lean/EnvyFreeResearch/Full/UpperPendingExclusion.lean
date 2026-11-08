import EnvyFreeResearch.Full.UpperGridCells
import EnvyFreeResearch.Full.UpperRawPayments

/-!
# Literal cached state after all pending whole-cell payments

The implementation filters already recorded physical atoms by logical-cell
indices. It neither queries the measures nor adds physical joins to the
logical cell count. All null endpoint material retains its literal owner.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperPendingExclusion

open UpperRecordedDomain UpperDomainDifference UpperGridCells UpperLogicalCells
  UpperCorrectionExecution UpperEndpointCache UpperWholePaymentsPhysical

variable {n m : ℕ} {Agent : Type*} [Fintype Agent]

def atomIn (cuts : Fin (m + 2) → ℝ) (e : Fin (m + 1)) (c : Component) : Bool :=
  if e = 0 then decide (c.right ≤ cuts e.succ)
  else decide (cuts e.castSucc < c.right ∧ c.right ≤ cuts e.succ)

def selected (cuts : Fin (m + 2) → ℝ) (owned : Agent → Finset (Fin (m + 1))) (c : Component) : Bool :=
  decide (∃ j e, e ∈ owned j ∧ atomIn cuts e c = true)

def remove (state : State n) (cuts : Fin (m + 2) → ℝ) (owned : Agent → Finset (Fin (m + 1))) : State n :=
  ⟨state.cells.filter (fun c => !selected cuts owned c), state.history⟩

omit [Fintype Agent] in
theorem logicalAtoms_filter (cs : List Component) (cuts : Fin (m + 2) → ℝ) (e : Fin (m + 1)) :
    logicalAtoms cs cuts e = cs.filter (atomIn cuts e) := by
  unfold logicalAtoms prefixAtoms intervalAtoms atomIn
  split_ifs <;> rfl

theorem selected_domain (cs : List Component) (cuts : Fin (m + 2) → ℝ)
    (owned : Agent → Finset (Fin (m + 1))) :
    domain (cs.filter (selected cuts owned)) =
      ⋃ j, piece (fun e => domain (logicalAtoms cs cuts e)) owned j := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    obtain ⟨hmem, hselected⟩ := List.mem_filter.mp hc
    obtain ⟨j, e, he, hce⟩ := of_decide_eq_true hselected
    apply mem_iUnion.mpr
    refine ⟨j, (mem_piece _ _ _ _).mpr ⟨e, he, ?_⟩⟩
    apply mem_domain.mpr
    refine ⟨c, ?_, hxc⟩
    rw [logicalAtoms_filter]
    exact List.mem_filter.mpr ⟨hmem, hce⟩
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨e, he, hxe⟩ := (mem_piece _ _ _ _).mp hj
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hxe
    rw [logicalAtoms_filter] at hc
    obtain ⟨hmem, hce⟩ := List.mem_filter.mp hc
    apply mem_domain.mpr
    refine ⟨c, List.mem_filter.mpr ⟨hmem, ?_⟩, hxc⟩
    exact decide_eq_true ⟨j, e, he, hce⟩

/-- The finite filtering computation removes exactly the physical whole-cell
payments, not an almost-everywhere replacement of those payments. -/
theorem remove_domain (state : State n) (hdis : DisjointComponents state.cells)
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) state.cells) (owned : Agent → Finset (Fin (m + 1))) :
    domain (remove state cuts owned).cells = domain state.cells \
      ⋃ j, piece (cell (domain state.cells) cuts) owned j := by
  rw [remove, whole_filter_domain _ hdis, selected_domain]
  congr 1
  simp_rw [logicalAtoms_domain _ _ hzero hmono hsep]

theorem remove_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (state : State n) (hstate : WellFormed μ state) (cuts : Fin (m + 2) → ℝ)
    (owned : Agent → Finset (Fin (m + 1))) : WellFormed μ (remove state cuts owned) := by
  refine ⟨hstate.1.filter _, hstate.2.1.filter _, hstate.2.2.1, ?_⟩
  intro i p hp
  obtain ⟨c, hc, hpc⟩ := hp
  exact hstate.2.2.2 i p ⟨c, (List.mem_filter.mp hc).1, hpc⟩

theorem remove_history (state : State n) (cuts : Fin (m + 2) → ℝ)
    (owned : Agent → Finset (Fin (m + 1))) : (remove state cuts owned).history = state.history := rfl

section Measurability

variable {X : Type*} [MeasurableSpace X]

omit [Fintype Agent] in
theorem atomIn_measurable (cuts : X → Fin (m + 2) → ℝ)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (e : Fin (m + 1)) :
    Measurable (fun p : X × Component => atomIn (cuts p.1) e p.2) := by
  by_cases he : e = 0
  · simp only [atomIn, he, ite_true]
    exact decide_measurable _ (measurableSet_le (component_right_measurable.comp measurable_snd)
      ((hcuts _).comp measurable_fst))
  · simp only [atomIn, he, ite_false]
    exact decide_measurable _ ((measurableSet_lt ((hcuts _).comp measurable_fst)
      (component_right_measurable.comp measurable_snd)).inter
      (measurableSet_le (component_right_measurable.comp measurable_snd) ((hcuts _).comp measurable_fst)))

theorem selected_measurable (cuts : X → Fin (m + 2) → ℝ)
    (owned : X → Agent → Finset (Fin (m + 1)))
    (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (howned : ∀ j, Measurable (fun z => owned z j)) :
    Measurable (fun p : X × Component => selected (cuts p.1) (owned p.1) p.2) := by
  apply decide_measurable
  have heq : {p : X × Component | ∃ j e, e ∈ owned p.1 j ∧ atomIn (cuts p.1) e p.2 = true} =
      ⋃ j, ⋃ e, ({p : X × Component | e ∈ owned p.1 j} ∩
        {p : X × Component | atomIn (cuts p.1) e p.2 = true}) := by ext p; simp
  rw [heq]
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun e =>
    (((measurableSet_mem_finset e).preimage ((howned j).comp measurable_fst))).inter
      (measurableSet_eq_fun (atomIn_measurable cuts hcuts e) measurable_const)))

theorem remove_measurable (state : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (owned : X → Agent → Finset (Fin (m + 1))) (hstate : Measurable state)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (howned : ∀ j, Measurable (fun z => owned z j)) :
    Measurable (fun z => remove (state z) (cuts z) (owned z)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z => ((state z).cells.filter
    (fun c => !selected (cuts z) (owned z) c), (state z).history))
  exact (list_filter_measurable _ _
    ((measurable_of_countable (fun b : Bool => !b)).comp (selected_measurable cuts owned hcuts howned))
    (state_cells_measurable.comp hstate)).prodMk (state_history_measurable.comp hstate)

end Measurability

end EnvyFreeResearch.Full.UpperPendingExclusion
