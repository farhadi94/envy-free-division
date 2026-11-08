import EnvyFreeResearch.Full.UpperSnapshotSmallFirstSupply

/-! Literal geometry of the actual first candidate, including the case that
keeps all positive cells and fills from their complement. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m : ℕ}

theorem filter_flag_iff (cs : List Component) (hdis : DisjointComponents cs) (keep : Component → Bool)
    (c : Component) (hc : c ∈ cs) (x : ℝ) (hx : x ∈ c.carrier) :
    keep c = true ↔ x ∈ domain (cs.filter keep) := by
  constructor
  · intro h
    exact mem_domain.mpr ⟨c, List.mem_filter.mpr ⟨hc, h⟩, hx⟩
  · intro h
    obtain ⟨d, hd, hxd⟩ := mem_domain.mp h
    obtain ⟨hd, hk⟩ := List.mem_filter.mp hd
    by_cases he : c = d
    · simpa only [he] using hk
    · let : Std.Symm (fun c d : Component => Disjoint c.carrier d.carrier) := ⟨fun _ _ h => h.symm⟩
      exact False.elim (Set.disjoint_left.mp (hdis.forall hc hd he) hx hxd)

theorem physicalPiece_restrict (U S : Set ℝ) (hSU : S ⊆ U) (a : I) (start : Circle) (first last : ℝ) :
    physicalPiece S a start first last = S ∩ physicalPiece U a start first last := by
  unfold physicalPiece
  split_ifs
  · simp
  · exact (inter_eq_left.mpr hSU).symm
  · ext x; simp only [mem_inter_iff]; exact ⟨fun h => ⟨h.1, hSU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · ext x; simp only [mem_inter_iff, mem_sdiff]; exact ⟨fun h => ⟨h.1, hSU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

theorem firstSource_domain (origin : State n) (hdis : DisjointComponents origin.cells) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) :
    domain (firstSource origin cutter cuts selected t).cells =
      if firstFill origin cutter cuts selected t then domain origin.cells \ domain (retain origin cuts selected).cells
      else domain (retain origin cuts selected).cells := by
  unfold firstSource
  split_ifs
  · exact whole_filter_domain _ hdis _
  · rfl

theorem firstRestored_positive_domain (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    domain (retain (firstRestored policy origin cutter cuts selected t start) cuts selected).cells =
      domain (retain origin cuts selected).cells := by
  rw [retain_domain _ cuts hzero hmono (fun e => UpperGridCells.refineEndpoints_preserves_separated
    origin.cells _ (cuts e) (hsep e)), retain_domain origin cuts hzero hmono hsep, firstRestored_domain]

def firstArc (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) : Set ℝ :=
  physicalPiece (domain origin.cells) (firstAmount origin cutter cuts selected t) start
    ((firstRun policy origin cutter cuts selected t start).1 0)
    ((firstRun policy origin cutter cuts selected t start).1 1)

theorem firstCircular_restrict (policy : Policy n) (origin : State n) (hdis : DisjointComponents origin.cells)
    (cutter : Fin n) (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    firstCircular policy origin cutter cuts selected t start =
      (if firstFill origin cutter cuts selected t then domain origin.cells \ domain (retain origin cuts selected).cells
      else domain (retain origin cuts selected).cells) ∩ firstArc policy origin cutter cuts selected t start := by
  have hsource : domain (firstSource origin cutter cuts selected t).cells ⊆ domain origin.cells := by
    rw [firstSource_domain origin hdis]
    split_ifs
    · exact sdiff_subset
    · exact retain_subset origin cuts selected
  change physicalPiece (domain (firstSource origin cutter cuts selected t).cells) _ start
    ((firstRun policy origin cutter cuts selected t start).1 0)
    ((firstRun policy origin cutter cuts selected t start).1 1) = _
  rw [physicalPiece_restrict _ _ hsource, firstSource_domain origin hdis]
  rfl

theorem firstEndowment_arc_domain (policy : Policy n) (origin : State n) (hdis : DisjointComponents origin.cells)
    (cutter : Fin n) (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    domain (firstEndowment policy origin cutter cuts selected t start).cells =
      if firstFill origin cutter cuts selected t then
        domain (retain origin cuts selected).cells ∪ firstArc policy origin cutter cuts selected t start
      else domain (retain origin cuts selected).cells ∩ firstArc policy origin cutter cuts selected t start := by
  let full := firstRestored policy origin cutter cuts selected t start
  have hd : DisjointComponents full.cells := refineEndpoints_disjoint _ _ hdis
  have hdom : domain full.cells = domain origin.cells := firstRestored_domain _ _ _ _ _ _ _
  have hsepnew (j : Fin 2) : SeparatedAt ((firstRun policy origin cutter cuts selected t start).1 j) full.cells :=
    UpperGridCells.refineEndpoints_separated _ _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hpos : domain (retain full cuts selected).cells = domain (retain origin cuts selected).cells :=
    firstRestored_positive_domain policy origin cutter cuts hzero hmono hsep selected t start
  have hS : domain (retain origin cuts selected).cells ⊆ domain origin.cells := retain_subset _ _ _
  have hA : firstArc policy origin cutter cuts selected t start ⊆ domain origin.cells := physicalPiece_subset _ _ _ _ _
  let target := if firstFill origin cutter cuts selected t then
    domain (retain origin cuts selected).cells ∪ firstArc policy origin cutter cuts selected t start
    else domain (retain origin cuts selected).cells ∩ firstArc policy origin cutter cuts selected t start
  have htarg : target ⊆ domain full.cells := by
    rw [hdom]
    dsimp only [target]
    split_ifs
    · exact union_subset hS hA
    · exact inter_subset_left.trans hS
  change domain (full.cells.filter _) = target
  rw [domain_filter_carrier full.cells _ target]
  · exact inter_eq_right.mpr htarg
  · intro c hc x hx
    have hp : positiveFlag cuts selected c = true ↔ x ∈ domain (retain origin cuts selected).cells := by
      have hh := filter_flag_iff full.cells hd (positiveFlag cuts selected) c hc x hx
      change _ ↔ x ∈ domain (retain full cuts selected).cells at hh
      rwa [hpos] at hh
    have ha := prefixAtom_iff full.cells (firstAmount origin cutter cuts selected t) start
      ((firstRun policy origin cutter cuts selected t start).1 0)
      ((firstRun policy origin cutter cuts selected t start).1 1) (hsepnew 0) (hsepnew 1) c hc x hx
    rw [hdom] at ha
    change _ ↔ x ∈ firstArc policy origin cutter cuts selected t start at ha
    dsimp only [firstFlag, target]
    split_ifs
    · rw [Bool.or_eq_true]
      exact or_congr hp ha
    · rw [Bool.and_eq_true]
      exact and_congr hp ha

/-- The actual kept first piece is exactly the sampled positive-domain cut,
or all positive cells plus the sampled complementary-domain cut. -/
theorem firstEndowment_domain (policy : Policy n) (origin : State n) (hdis : DisjointComponents origin.cells)
    (cutter : Fin n) (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    domain (firstEndowment policy origin cutter cuts selected t start).cells =
      if firstFill origin cutter cuts selected t then
        domain (retain origin cuts selected).cells ∪ firstCircular policy origin cutter cuts selected t start
      else firstCircular policy origin cutter cuts selected t start := by
  rw [firstEndowment_arc_domain policy origin hdis cutter cuts hzero hmono hsep,
    firstCircular_restrict policy origin hdis]
  have hA : firstArc policy origin cutter cuts selected t start ⊆ domain origin.cells := physicalPiece_subset _ _ _ _ _
  split_ifs
  · ext x
    constructor
    · rintro (hp | ha)
      · exact Or.inl hp
      · by_cases hp : x ∈ domain (retain origin cuts selected).cells
        · exact Or.inl hp
        · exact Or.inr ⟨⟨hA ha, hp⟩, ha⟩
    · rintro (hp | ha)
      · exact Or.inl hp
      · exact Or.inr ha.2
  · rfl

end EnvyFreeResearch.Full.UpperSnapshotSmall
