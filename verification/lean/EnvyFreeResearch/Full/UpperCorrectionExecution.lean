import EnvyFreeResearch.Full.UpperDynamicExecutor
import EnvyFreeResearch.Full.UpperEndpointCache
import EnvyFreeResearch.Full.UpperCorrectionStage

/-!
# A concrete correction transaction with its actual cache

The state consists of a literal recorded domain and the real oracle history.
The transaction reads its masses from the latest recorded Eval answers, calls
the actual two-endpoint executor, and refines/removes the returned physical
piece. Its invariant, measurability and query charges hold for this program.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperCorrectionExecution

open UpperRecordedDomain UpperDomainDifference UpperCircularStage UpperUnionCircular
  UpperStageMeasurable UpperDynamicExecutor UpperEndpointCache Chores ProtocolMeasurable

abbrev Circle := UpperCircular.Circle

structure State (n : ℕ) where
  cells : List Component
  history : History n

def stateCode {n : ℕ} (state : State n) : List Component × History n := (state.cells, state.history)

instance stateMeasurableSpace {n : ℕ} : MeasurableSpace (State n) :=
  MeasurableSpace.comap stateCode inferInstance

theorem stateCode_measurable {n : ℕ} : Measurable (stateCode (n := n)) := comap_measurable _

theorem state_cells_measurable {n : ℕ} : Measurable (State.cells (n := n)) :=
  measurable_fst.comp stateCode_measurable

theorem state_history_measurable {n : ℕ} : Measurable (State.history (n := n)) :=
  measurable_snd.comp stateCode_measurable

def values {n : ℕ} (state : State n) (cutter : Fin n) (cell : Component) : ℝ :=
  cached (historyPrefix state.history) cutter cell

def total {n : ℕ} (state : State n) (cutter : Fin n) : ℝ :=
  sumValues (values state cutter) state.cells

/-- Total finite-arithmetic implementation of deficit normalization. On every
well-formed reached correction, the clipping is proved inactive. -/
def amount (eps total : ℝ) : I :=
  ⟨max 0 (min 1 (eps / total)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem amount_eq_fraction (eps total : ℝ) (heps : 0 ≤ eps) (hfit : eps ≤ total) (hpos : 0 < total) :
    amount eps total = UpperCorrectionStage.fraction eps total heps hfit hpos := by
  apply Subtype.ext
  change max 0 (min 1 (eps / total)) = eps / total
  rw [min_eq_right ((div_le_one hpos).mpr hfit), max_eq_right (div_nonneg heps hpos.le)]

def descriptor {n : ℕ} (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) : Correction :=
  recordedCorrection policy state.history cutter (values state cutter) (total state cutter)
    state.cells (amount eps (total state cutter)) start

def execute {n : ℕ} (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) : Correction × State n :=
  let record := descriptor policy state cutter eps start
  (record, ⟨applyCorrection state.cells record,
    (secondRun policy state.history cutter (values state cutter) (total state cutter)
      state.cells (amount eps (total state cutter)) start).2⟩)

def payment {n : ℕ} (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) : Set ℝ :=
  correctionPiece state.cells (descriptor policy state cutter eps start)

def observedPayment {n : ℕ} (before after : State n) (observer : Fin n) : ℝ :=
  total before observer - total after observer

def WellFormed {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (state : State n) : Prop :=
  Ordered state.cells ∧ DisjointComponents state.cells ∧ Truthful μ state.history ∧
    RecordedHistory state.cells state.history

variable {n : ℕ}

theorem execute_domain (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) :
    domain (execute policy state cutter eps start).2.cells = domain state.cells \ payment policy state cutter eps start :=
  removeCorrection_domain state.cells _ _ _ _

theorem payment_subset (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) : payment policy state cutter eps start ⊆ domain state.cells :=
  UpperPhysical.physicalPiece_subset _ _ _ _ _

theorem payment_measurableSet (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) : MeasurableSet (payment policy state cutter eps start) := by
  unfold payment correctionPiece UpperPhysical.physicalPiece
  split_ifs
  · exact MeasurableSet.empty
  · exact domain_measurable _
  · exact (domain_measurable _).inter measurableSet_Ioc
  · exact (domain_measurable _).diff measurableSet_Ioc

theorem query_bound (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) :
    (execute policy state cutter eps start).2.history.length ≤ state.history.length + 2 * (n + 1) :=
  stage_query_bound policy state.history cutter (values state cutter) (total state cutter)
    state.cells (amount eps (total state cutter)) start

theorem cut_bound (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) :
    ((execute policy state cutter eps start).2.history.map Prod.fst).countP isCut ≤
      (state.history.map Prod.fst).countP isCut + 2 :=
  stage_cut_bound policy state.history cutter (values state cutter) (total state cutter)
    state.cells (amount eps (total state cutter)) start

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem values_correct (state : State n) (hstate : WellFormed μ state) (i : Fin n)
    (c : Component) (hc : c ∈ state.cells) : values state i c = mass (μ i) c :=
  cached_exact _ state.cells
    (historyPrefix_prefixCorrect μ state.history state.cells hstate.2.2.1 hstate.2.2.2) i c hc

theorem total_correct (state : State n) (hstate : WellFormed μ state) (i : Fin n) :
    total state i = (μ i).real (domain state.cells) := by
  unfold total
  rw [cached_sum_eq (μ i) state.cells (values state i) (values_correct μ state hstate i)]
  exact (domain_mass_sum (μ i) state.cells hstate.2.1).symm

theorem execute_wellFormed (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain state.cells)) (eps : ℝ) (start : Circle) :
    WellFormed μ (execute policy state cutter eps start).2 := by
  have hcache := values_correct μ state hstate cutter
  have h := removed_cache_correct μ policy hpolicy state.history cutter (values state cutter)
    state.cells hstate.2.1 hstate.2.2.1 hstate.2.2.2 hcache hpositive
    (amount eps (total state cutter)) start
  unfold WellFormed execute descriptor
  rw [total_correct μ state hstate cutter]
  rw [total_correct μ state hstate cutter] at h
  exact ⟨removeCorrection_ordered state.cells hstate.1 _ _ _ _,
    removeCorrection_disjoint state.cells hstate.2.1 _ _ _ _, h.1, h.2.1⟩

theorem execute_history (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain state.cells)) (eps : ℝ) (start : Circle) :
    Truthful μ (execute policy state cutter eps start).2.history ∧
      state.history ⊆ (execute policy state cutter eps start).2.history := by
  have h := circular_history μ policy hpolicy state.history cutter (values state cutter)
    state.cells hstate.2.1 hstate.2.2.1 hstate.2.2.2
    (values_correct μ state hstate cutter) hpositive (amount eps (total state cutter)) start
  rw [total_correct μ state hstate cutter] at h
  simpa only [execute, total_correct μ state hstate cutter] using And.intro h.1 h.2.1

/-- A rejected proposal keeps its newly learned truthful answers while
restoring the old physical domain, which remains correctly recorded. -/
theorem rejected_wellFormed (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain state.cells)) (eps : ℝ) (start : Circle) :
    WellFormed μ (⟨state.cells, (execute policy state cutter eps start).2.history⟩ : State n) := by
  have h := execute_history μ policy hpolicy state hstate cutter hpositive eps start
  exact ⟨hstate.1, hstate.2.1, h.1, recordedHistory_mono _ hstate.2.2.2 h.2⟩

theorem observedPayment_correct (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain state.cells)) (eps : ℝ) (start : Circle)
    (observer : Fin n) :
    observedPayment state (execute policy state cutter eps start).2 observer =
      (μ observer).real (payment policy state cutter eps start) := by
  have hnext := execute_wellFormed μ policy hpolicy state hstate cutter hpositive eps start
  unfold observedPayment
  rw [total_correct μ state hstate observer, total_correct μ _ hnext observer, execute_domain]
  have h := measureReal_inter_add_sdiff (μ := μ observer) (s := domain state.cells)
    (payment_measurableSet policy state cutter eps start)
  rw [inter_eq_right.mpr (payment_subset policy state cutter eps start)] at h
  linarith

/-- The executed transaction pays exactly the requested deficit. The caller
supplies the proved remaining-supply inequality, not a successful Cut or cache
update assumption. -/
theorem payment_exact (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain state.cells)) (eps : ℝ)
    (heps : 0 ≤ eps) (hfit : eps ≤ (μ cutter).real (domain state.cells)) (start : Circle) :
    (μ cutter).real (payment policy state cutter eps start) = eps := by
  change (μ cutter).real (piece policy state.history cutter (values state cutter) (total state cutter)
    state.cells (amount eps (total state cutter)) start) = eps
  rw [total_correct μ state hstate cutter, amount_eq_fraction eps _ heps hfit hpositive]
  exact UpperCorrectionStage.exact_deficit μ policy hpolicy state.history cutter (values state cutter)
    state.cells hstate.1 hstate.2.1 (values_correct μ state hstate cutter) hpositive eps heps hfit start

end Correctness

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem values_measurable (state : X → State n) (cutter : X → Fin n)
    (hstate : Measurable state) (hcutter : Measurable cutter) :
    Measurable (fun p : X × Component => values (state p.1) (cutter p.1) p.2) :=
  history_cache_joint_measurable (fun z => (state z).history) cutter
    (state_history_measurable.comp hstate) hcutter

theorem total_measurable (state : X → State n) (cutter : X → Fin n)
    (hstate : Measurable state) (hcutter : Measurable cutter) :
    Measurable (fun z => total (state z) (cutter z)) :=
  UpperDynamicRouting.sumValues_measurable _ (values_measurable state cutter hstate hcutter)
    _ (state_cells_measurable.comp hstate)

theorem observedPayment_measurable (before after : X → State n) (observer : X → Fin n)
    (hbefore : Measurable before) (hafter : Measurable after) (hobserver : Measurable observer) :
    Measurable (fun z => observedPayment (before z) (after z) (observer z)) :=
  (total_measurable before observer hbefore hobserver).sub
    (total_measurable after observer hafter hobserver)

theorem amount_measurable (eps total : X → ℝ) (heps : Measurable eps) (htotal : Measurable total) :
    Measurable (fun z => amount (eps z) (total z)) :=
  (measurable_const.max (measurable_const.min (heps.div htotal))).subtype_mk

theorem descriptor_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (state : X → State n) (cutter : X → Fin n) (eps : X → ℝ) (start : X → Circle)
    (hstate : Measurable state) (hcutter : Measurable cutter)
    (heps : Measurable eps) (hstart : Measurable start) :
    Measurable (fun z => descriptor policy (state z) (cutter z) (eps z) (start z)) :=
  recordedCorrection_joint_measurable policy hpolicy _ cutter _ _ _ _ start
    (state_history_measurable.comp hstate) hcutter (values_measurable state cutter hstate hcutter)
    (total_measurable state cutter hstate hcutter) (state_cells_measurable.comp hstate)
    (amount_measurable eps _ heps (total_measurable state cutter hstate hcutter)) hstart

/-- Joint Borel measurability of the concrete transaction and returned state,
including the actual latest-answer cache and physical domain update. -/
theorem execute_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (state : X → State n) (cutter : X → Fin n) (eps : X → ℝ) (start : X → Circle)
    (hstate : Measurable state) (hcutter : Measurable cutter)
    (heps : Measurable eps) (hstart : Measurable start) :
    Measurable (fun z => execute policy (state z) (cutter z) (eps z) (start z)) := by
  have hr := descriptor_measurable policy hpolicy state cutter eps start hstate hcutter heps hstart
  apply hr.prodMk
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · exact applyCorrection_measurable _ _ (state_cells_measurable.comp hstate) hr
  · exact measurable_snd.comp (secondRun_joint_measurable policy hpolicy _ cutter _ _ _ _ start
      (state_history_measurable.comp hstate) hcutter (values_measurable state cutter hstate hcutter)
      (total_measurable state cutter hstate hcutter) (state_cells_measurable.comp hstate)
      (amount_measurable eps _ heps (total_measurable state cutter hstate hcutter)) hstart)

end Measurability

end EnvyFreeResearch.Full.UpperCorrectionExecution
