import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationSupportedFirst

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperCorrectionPieces
variable {n m : ℕ} {Generated : Type*}

theorem recordedEndpoints_of_recorded (cuts : Fin (m+2) → ℝ) (points : Generated → ℝ)
    (cs : List Component)
    (h : ∀ p, Recorded cs p → (∃ e, cuts e=p) ∨ ∃ j, points j=p) :
    RecordedEndpoints cuts points cs := by
  intro c hc
  exact ⟨h c.left ⟨c,hc,Or.inl rfl⟩,h c.right ⟨c,hc,Or.inr rfl⟩⟩

theorem recordedEndpoints_append (cuts : Fin (m+2) → ℝ) (points : Generated → ℝ)
    (cs ds : List Component) (hc : RecordedEndpoints cuts points cs)
    (hd : RecordedEndpoints cuts points ds) : RecordedEndpoints cuts points (cs++ds) := by
  intro c h
  rcases List.mem_append.mp h with h | h
  · exact hc c h
  · exact hd c h

theorem recordedEndpoints_take (cuts : Fin (m+2) → ℝ) (points : Generated → ℝ)
    (cs : List Component) (hc : RecordedEndpoints cuts points cs) (r : Correction)
    (hf : ∃ j, points j=r.first) (hl : ∃ j, points j=r.last) :
    RecordedEndpoints cuts points (take cs r) := by
  apply recordedEndpoints_of_recorded
  intro p hp
  rcases take_recorded cs r hp with hp | hp | hp
  · exact Or.inr (hp ▸ hf)
  · exact Or.inr (hp ▸ hl)
  · obtain ⟨c,hc',he⟩ := hp
    rcases he with he | he
    · simpa only [he] using (hc c hc').1
    · simpa only [he] using (hc c hc').2

theorem recordedEndpoints_remove (cuts : Fin (m+2) → ℝ) (points : Generated → ℝ)
    (cs : List Component) (hc : RecordedEndpoints cuts points cs) (r : Correction)
    (hf : ∃ j, points j=r.first) (hl : ∃ j, points j=r.last) :
    RecordedEndpoints cuts points (applyCorrection cs r) := by
  apply recordedEndpoints_of_recorded
  intro p hp
  rcases removeCorrection_recorded cs r.amount r.start r.first r.last hp with hp | hp | hp
  · exact Or.inr (hp ▸ hf)
  · exact Or.inr (hp ▸ hl)
  · obtain ⟨c,hc',he⟩ := hp
    rcases he with he | he
    · simpa only [he] using (hc c hc').1
    · simpa only [he] using (hc c hc').2

theorem firstVirtual_recorded (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hone : cuts (Fin.last (m+1))=1)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) (points : Generated → ℝ)
    (hpoints : ∀ j, ∃ e, points e=(firstRun policy origin cutter cuts selected t first).1 j) :
    RecordedEndpoints cuts points (firstVirtual policy origin cutter cuts selected t first) ∧
    RecordedEndpoints cuts points (remainderVirtual policy origin cutter cuts selected t first) := by
  have ha : RecordedEndpoints cuts points (UpperVirtualGrid.atoms cuts) :=
    recordedEndpoints_of_recorded cuts points _ (fun _ hp => Or.inl (UpperVirtualGrid.atoms_recorded cuts hzero hone hp))
  have hp : RecordedEndpoints cuts points (positiveVirtual cuts selected) := by
    intro c hc
    exact ha c (List.mem_filter.mp hc).1
  have hn : RecordedEndpoints cuts points (negativeVirtual cuts selected) := by
    intro c hc
    exact ha c (List.mem_filter.mp hc).1
  have hf : ∃ e, points e=(firstRecord policy origin cutter cuts selected t first).first := hpoints 0
  have hl : ∃ e, points e=(firstRecord policy origin cutter cuts selected t first).last := hpoints 1
  constructor
  · unfold firstVirtual
    split_ifs
    · exact recordedEndpoints_append cuts points _ _ hp (recordedEndpoints_take cuts points _ ha _ hf hl)
    · exact recordedEndpoints_take cuts points _ hp _ hf hl
  · unfold remainderVirtual
    split_ifs
    · exact recordedEndpoints_remove cuts points _ hn _ hf hl
    · exact recordedEndpoints_append cuts points _ _ hn (recordedEndpoints_remove cuts points _ hp _ hf hl)

end EnvyFreeResearch.Full.UpperSnapshotSmall
