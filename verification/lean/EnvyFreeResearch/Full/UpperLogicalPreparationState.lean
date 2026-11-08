import EnvyFreeResearch.Full.UpperRecordedParents
import EnvyFreeResearch.Full.UpperPendingExclusion
import EnvyFreeResearch.Full.UpperReserve

/-!
# A labelled logical reserve with the complete recorded sample history

The reserve is computed by filtering the final recorded atoms. Its literal
domain is the union of the coarse parents whose independent labels pass the
retention test, although its history retains every fine-grid sample query.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperGridCells
  UpperLogicalCells UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperCommonGrid Chores

variable {n m : ℕ}

def selectedUnion {Cell : Type*} (cells : Cell → Set ℝ) (selected : Finset Cell) : Set ℝ :=
  ⋃ e, if e ∈ selected then cells e else ∅

theorem mem_selectedUnion {Cell : Type*} (cells : Cell → Set ℝ) (selected : Finset Cell) (x : ℝ) :
    x ∈ selectedUnion cells selected ↔ ∃ e ∈ selected, x ∈ cells e := by
  simp only [selectedUnion, mem_iUnion]
  apply exists_congr
  intro e
  split_ifs <;> simp_all

/-- Retaining logical cells uses only the final recorded component list and
cached endpoint comparisons, and leaves the complete query history unchanged. -/
def retain (state : State n) (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) : State n :=
  ⟨state.cells.filter (UpperPendingExclusion.selected cuts (fun _ : Unit => selected)), state.history⟩

theorem retain_history (state : State n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) : (retain state cuts selected).history = state.history := rfl

theorem retain_domain (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (selected : Finset (Fin (m + 1))) :
    domain (retain state cuts selected).cells = selectedUnion (cell (domain state.cells) cuts) selected := by
  rw [retain, UpperPendingExclusion.selected_domain]
  simp_rw [logicalAtoms_domain _ _ hzero hmono hsep]
  simp only [UpperWholePaymentsPhysical.piece, iUnion_const, selectedUnion]
  apply iUnion_congr
  intro e
  split_ifs <;> rfl

theorem retain_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (state : State n) (hstate : WellFormed μ state) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) : WellFormed μ (retain state cuts selected) := by
  refine ⟨hstate.1.filter _, hstate.2.1.filter _, hstate.2.2.1, ?_⟩
  intro i p hp
  obtain ⟨c, hc, hpc⟩ := hp
  exact hstate.2.2.2 i p ⟨c, (List.mem_filter.mp hc).1, hpc⟩

theorem retain_separated (state : State n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (p : ℝ) (hsep : SeparatedAt p state.cells) :
    SeparatedAt p (retain state cuts selected).cells :=
  fun c hc => hsep c (List.mem_filter.mp hc).1

theorem retain_measurable {X : Type*} [MeasurableSpace X]
    (state : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (selected : X → Finset (Fin (m + 1))) (hstate : Measurable state)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (hselected : Measurable selected) :
    Measurable (fun z => retain (state z) (cuts z) (selected z)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z => ((state z).cells.filter
    (UpperPendingExclusion.selected (cuts z) (fun _ : Unit => selected z)), (state z).history))
  exact (list_filter_measurable _ _
    (UpperPendingExclusion.selected_measurable cuts (fun z (_ : Unit) => selected z) hcuts
      (fun _ => hselected)) (state_cells_measurable.comp hstate)).prodMk
    (state_history_measurable.comp hstate)

variable {Fine Parent : Type*} [Fintype Fine]

def reserveCells (parent : Fine → Parent) (theta : I) (labels : Parent → I) : Finset Fine :=
  Finset.univ.filter (fun e => labels (parent e) ≤ theta)

def labelledUnion (coarse : Parent → Set ℝ) (theta : I) (labels : Parent → I) : Set ℝ :=
  ⋃ p, if labels p ≤ theta then coarse p else ∅

/-- Grouping the selected fine cells by their actual coarse parent recovers
the reserve fixed before sampling, literally including all owned endpoints. -/
theorem selectedUnion_parent (fine : Fine → Set ℝ) (coarse : Parent → Set ℝ)
    (parent : Fine → Parent) (theta : I) (labels : Parent → I)
    (hfiber : ∀ p, (⋃ e, if parent e = p then fine e else ∅) = coarse p) :
    selectedUnion fine (reserveCells parent theta labels) = labelledUnion coarse theta labels := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ := (mem_selectedUnion _ _ x).mp hx
    have hlabel : labels (parent e) ≤ theta := (Finset.mem_filter.mp he).2
    refine mem_iUnion.mpr ⟨parent e, ?_⟩
    simp only [hlabel, ite_true]
    rw [← hfiber (parent e)]
    exact mem_iUnion.mpr ⟨e, by simpa using hxe⟩
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    by_cases hlabel : labels p ≤ theta
    · simp only [hlabel, ite_true, ← hfiber p] at hp
      obtain ⟨e, he⟩ := mem_iUnion.mp hp
      by_cases hparent : parent e = p
      · exact (mem_selectedUnion _ _ x).mpr ⟨e, by simp [reserveCells, hparent, hlabel],
          by simpa only [hparent, ite_true] using he⟩
      · simp only [hparent, ite_false, mem_empty_iff_false] at he
    · simp only [hlabel, ite_false, mem_empty_iff_false] at hp

theorem reserveCells_measurable [Fintype Parent] [MeasurableSpace Parent] [MeasurableSingletonClass Parent]
    {X : Type*} [MeasurableSpace X] (parent : X → Fine → Parent) (theta : I)
    (labels : X → Parent → I) (hparent : ∀ e, Measurable (fun z => parent z e))
    (hlabels : ∀ p, Measurable (fun z => labels z p)) :
    Measurable (fun z => reserveCells (parent z) theta (labels z)) := by
  apply measurable_finset_iff.mpr
  intro e
  apply measurableSet_setOfPred.mp
  have heq : {z | e ∈ reserveCells (parent z) theta (labels z)} =
      ⋃ p, ({z | parent z e = p} ∩ {z | labels z p ≤ theta}) := by
    ext z
    simp only [reserveCells, Finset.mem_filter, Finset.mem_univ, true_and, mem_iUnion,
      mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨parent z e, rfl, hz⟩
    · rintro ⟨p, hp, hz⟩
      simpa only [hp] using hz
  rw [heq]
  exact MeasurableSet.iUnion (fun p =>
    (measurableSet_eq_fun (hparent e) measurable_const).inter (measurableSet_le (hlabels p) measurable_const))

variable {Agent : Type*} [Fintype Agent]

/-- The actual reserve state, computed after all samples from the complete
recorded final atoms. Labels are attached to the original coarse parents. -/
def reserveState (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) : State n :=
  retain (UpperGridCache.aligned policy active origin q m draw)
    (UpperGridMerge.cuts policy active origin q m draw)
    (reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels)

theorem reserveState_history (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    (reserveState policy active origin q m draw theta labels).history =
      (UpperGridCache.aligned policy active origin q m draw).history := rfl

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem reserveState_domain (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) :
    domain (reserveState policy active origin q m draw theta labels).cells =
      labelledUnion (UpperRecordedQuantiles.logicalCells policy active origin q) theta labels := by
  rw [reserveState, retain_domain _ _
    (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
    (grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw),
    UpperGridCache.aligned_domain]
  apply selectedUnion_parent _ _ _ theta labels
  intro p
  rw [← UpperRecordedParents.parent_union μ policy hpolicy active origin hgood hpositive q m draw p]
  apply iUnion_congr
  intro e
  split_ifs <;> rfl

theorem reserveState_wellFormed (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) :
    WellFormed μ (reserveState policy active origin q m draw theta labels) :=
  retain_wellFormed μ _
    (UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw) _ _

end Correctness

theorem reserveState_separated (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (e : Fin (count (Agent := Agent) q + m + 2)) :
    SeparatedAt (UpperGridMerge.cuts policy active origin q m draw e)
      (reserveState policy active origin q m draw theta labels).cells :=
  retain_separated _ _ _ _ (UpperGridCache.aligned_separated policy active origin q m draw e)

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem reserveState_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q m : ℕ) (theta : I) :
    Measurable (fun p : (State n × (Fin m → Agent × I)) × (Fin (count (Agent := Agent) q + 1) → I) =>
      reserveState policy active p.1.1 q m p.1.2 theta p.2) := by
  apply retain_measurable
  · exact (UpperGridCache.aligned_measurable policy hpolicy active q m).comp measurable_fst
  · intro e
    exact (measurable_pi_apply e).comp ((UpperGridMerge.cuts_measurable policy hpolicy active q m).comp measurable_fst)
  · exact reserveCells_measurable _ theta _
      (fun e => (UpperRecordedParents.parent_measurable policy hpolicy active q m e).comp measurable_fst)
      (fun p => (measurable_pi_apply p).comp measurable_snd)

end Measurability

end EnvyFreeResearch.Full.UpperLogicalPreparation
