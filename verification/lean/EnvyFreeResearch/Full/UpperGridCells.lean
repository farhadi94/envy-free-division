import EnvyFreeResearch.Full.UpperGridRecords
import EnvyFreeResearch.Full.UpperLogicalCells

/-!
# Exact cached logical cells inside a recorded physical grid

Logical cells may contain many physical interval components. Their values are
computed by filtering and summing the existing all-observer cache. Refinement
at the resource bounds is free: every boundary actually created there was
already an endpoint of an old component.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperGridCells

open UpperRecordedDomain UpperDomainDifference UpperEndpointCache UpperCorrectionExecution
  UpperGridRecords UpperLogicalCells ProtocolMeasurable

variable {n : ℕ}

theorem refineAt_recorded_zero (p : ℝ) (cells : List Component)
    (h : Recorded (refineAt p cells) 0) : Recorded cells 0 := by
  obtain ⟨d, hd, hz⟩ := h
  obtain ⟨c, hc, hd⟩ := mem_refineAt.mp hd
  have hb := splitAt_subpart p c d hd
  have hz' : c.left = 0 := by
    rcases hz with hz | hz
    · linarith [c.left_nonneg, hb.2.1]
    · linarith [c.left_nonneg, hb.2.1, d.left_le_right]
  exact ⟨c, hc, Or.inl hz'.symm⟩

theorem refineAt_recorded_one (p : ℝ) (cells : List Component)
    (h : Recorded (refineAt p cells) 1) : Recorded cells 1 := by
  obtain ⟨d, hd, ho⟩ := h
  obtain ⟨c, hc, hd⟩ := mem_refineAt.mp hd
  have hb := splitAt_subpart p c d hd
  have ho' : c.right = 1 := by
    rcases ho with ho | ho
    · linarith [c.right_le_one, hb.2.2, d.left_le_right]
    · linarith [c.right_le_one, hb.2.2]
  exact ⟨c, hc, Or.inr ho'.symm⟩

theorem refineBoundary_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (state : State n) (hstate : WellFormed μ state) (p : ℝ) (hp : p = 0 ∨ p = 1) :
    WellFormed μ (⟨refineAt p state.cells, state.history⟩ : State n) := by
  refine ⟨refineAt_ordered p _ hstate.1, refineAt_disjoint p _ hstate.2.1, hstate.2.2.1, ?_⟩
  intro i q hq
  have horig := hq
  rcases refineAt_recorded p state.cells hq with rfl | hq
  · rcases hp with rfl | rfl
    · exact hstate.2.2.2 i 0 (refineAt_recorded_zero 0 state.cells horig)
    · exact hstate.2.2.2 i 1 (refineAt_recorded_one 1 state.cells horig)
  · exact hstate.2.2.2 i q hq

def align (state : State n) : State n := ⟨refineAt 1 (refineAt 0 state.cells), state.history⟩

theorem align_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (state : State n) (hstate : WellFormed μ state) : WellFormed μ (align state) :=
  refineBoundary_wellFormed μ _ (refineBoundary_wellFormed μ state hstate 0 (Or.inl rfl)) 1 (Or.inr rfl)

theorem align_domain (state : State n) : domain (align state).cells = domain state.cells := by
  simp only [align, refineAt_domain]

theorem align_separated_zero (state : State n) : SeparatedAt 0 (align state).cells :=
  refineAt_preserves_separated 1 0 _ (refineAt_separated 0 state.cells)

theorem align_separated_one (state : State n) : SeparatedAt 1 (align state).cells :=
  refineAt_separated 1 _

theorem refineEndpoints_preserves_separated (cells : List Component) (points : List ℝ)
    (p : ℝ) (h : SeparatedAt p cells) : SeparatedAt p (refineEndpoints cells points) := by
  induction points generalizing cells with
  | nil => exact h
  | cons q points ih => exact ih _ (refineAt_preserves_separated q p cells h)

theorem refineEndpoints_separated (cells : List Component) (points : List ℝ)
    {p : ℝ} (hp : p ∈ points) : SeparatedAt p (refineEndpoints cells points) := by
  induction points generalizing cells with
  | nil => simp at hp
  | cons q points ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact refineEndpoints_preserves_separated _ points p (refineAt_separated p cells)
    · exact ih _ hp

def prefixAtoms (p : ℝ) (cells : List Component) : List Component :=
  cells.filter (fun c => decide (c.right ≤ p))

theorem prefixAtoms_domain (cells : List Component) (p : ℝ) (hsep : SeparatedAt p cells) :
    domain (prefixAtoms p cells) = domain cells ∩ Iic p := by
  apply domain_filter_carrier
  intro c hc x hx
  simp only [decide_eq_true_eq, mem_Iic]
  constructor
  · exact fun h => (c.subset_closed hx).2.trans h
  · intro h
    by_contra hn
    exact (not_lt_of_ge h) (hsep c hc (lt_of_not_ge hn) hx)

theorem cell_first_eq {m : ℕ} (buffer : Set ℝ) (cuts : Fin (m + 2) → ℝ)
    (hbuffer : buffer ⊆ Icc (0 : ℝ) 1) (hzero : cuts 0 = 0) (hmono : Monotone cuts) :
    cell buffer cuts 0 = buffer ∩ Iic (cuts (0 : Fin (m + 1)).succ) := by
  have hright : 0 ≤ cuts (0 : Fin (m + 1)).succ := by
    rw [← hzero]
    exact hmono (Fin.zero_le _)
  ext x
  simp only [cell, ite_true, Fin.castSucc_zero, hzero, mem_union, mem_inter_iff,
    mem_Ioc, mem_singleton_iff, mem_Iic]
  constructor
  · rintro (⟨hb, _, hr⟩ | ⟨hb, rfl⟩)
    · exact ⟨hb, hr⟩
    · exact ⟨hb, hright⟩
  · rintro ⟨hb, hr⟩
    by_cases hx : x = 0
    · exact Or.inr ⟨hb, hx⟩
    · exact Or.inl ⟨hb, lt_of_le_of_ne (hbuffer hb).1 (Ne.symm hx), hr⟩

def logicalAtoms {m : ℕ} (cells : List Component) (cuts : Fin (m + 2) → ℝ) (i : Fin (m + 1)) : List Component :=
  if i = 0 then prefixAtoms (cuts i.succ) cells else intervalAtoms (cuts i.castSucc) (cuts i.succ) cells

theorem logicalAtoms_subset {m : ℕ} (cells : List Component) (cuts : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) : logicalAtoms cells cuts i ⊆ cells := by
  unfold logicalAtoms prefixAtoms intervalAtoms
  split_ifs <;> intro c hc <;> exact (List.mem_filter.mp hc).1

/-- Literal equality, including the resource's left endpoint; this is not an
almost-everywhere substitute for the physical allocation domain. -/
theorem logicalAtoms_domain {m : ℕ} (cells : List Component) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ c, SeparatedAt (cuts c) cells)
    (i : Fin (m + 1)) : domain (logicalAtoms cells cuts i) = cell (domain cells) cuts i := by
  by_cases hi : i = 0
  · subst i
    rw [logicalAtoms, ite_eq_left rfl, prefixAtoms_domain _ _ (hsep _),
      cell_first_eq _ _ (domain_subset_unit cells) hzero hmono]
  · rw [logicalAtoms, ite_eq_right hi, intervalAtoms_domain _ _ _ (hsep _) (hsep _)]
    simp only [cell, hi, ite_false, union_empty]

def cachedMass {m : ℕ} (state : State n) (cuts : Fin (m + 2) → ℝ) (observer : Fin n)
    (i : Fin (m + 1)) : ℝ := sumValues (values state observer) (logicalAtoms state.cells cuts i)

theorem cachedMass_correct {m : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (state : State n) (hstate : WellFormed μ state) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ c, SeparatedAt (cuts c) state.cells)
    (observer : Fin n) (i : Fin (m + 1)) :
    cachedMass state cuts observer i = (μ observer).real (cell (domain state.cells) cuts i) := by
  have hd : DisjointComponents (logicalAtoms state.cells cuts i) := by
    unfold logicalAtoms prefixAtoms intervalAtoms
    split_ifs <;> exact List.Pairwise.filter _ hstate.2.1
  rw [cachedMass, cached_sum_eq (μ observer) _ _
    (fun c hc => values_correct μ state hstate observer c (logicalAtoms_subset _ _ _ hc)),
    ← domain_mass_sum (μ observer) _ hd, logicalAtoms_domain _ _ hzero hmono hsep]

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem align_measurable : Measurable (align (n := n)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun state : State n => (refineAt 1 (refineAt 0 state.cells), state.history))
  exact (refineAt_measurable _ _
    (refineAt_measurable _ _ state_cells_measurable measurable_const) measurable_const).prodMk
    state_history_measurable

theorem prefixAtoms_measurable (cells : X → List Component) (p : X → ℝ)
    (hcells : Measurable cells) (hp : Measurable p) :
    Measurable (fun z => prefixAtoms (p z) (cells z)) := by
  apply list_filter_measurable
  · apply decide_measurable
    exact measurableSet_le (component_right_measurable.comp measurable_snd) (hp.comp measurable_fst)
  · exact hcells

theorem logicalAtoms_measurable {m : ℕ} (cells : X → List Component) (cuts : X → Fin (m + 2) → ℝ)
    (hcells : Measurable cells) (hcuts : ∀ c, Measurable (fun z => cuts z c)) (i : Fin (m + 1)) :
    Measurable (fun z => logicalAtoms (cells z) (cuts z) i) := by
  by_cases hi : i = 0
  · simpa only [logicalAtoms, hi, ite_true] using prefixAtoms_measurable cells (fun z => cuts z i.succ) hcells (hcuts _)
  · simpa only [logicalAtoms, hi, ite_false] using
      intervalAtoms_measurable cells (fun z => cuts z i.castSucc) (fun z => cuts z i.succ) hcells (hcuts _) (hcuts _)

theorem cachedMass_measurable {m : ℕ} (state : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (hstate : Measurable state) (hcuts : ∀ c, Measurable (fun z => cuts z c))
    (observer : Fin n) (i : Fin (m + 1)) :
    Measurable (fun z => cachedMass (state z) (cuts z) observer i) :=
  UpperDynamicRouting.sumValues_measurable _ (values_measurable state (fun _ => observer) hstate measurable_const)
    _ (logicalAtoms_measurable _ cuts (state_cells_measurable.comp hstate) hcuts i)

end Measurability

end EnvyFreeResearch.Full.UpperGridCells
