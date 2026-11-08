import EnvyFreeResearch.Full.UpperGlobalProtocolSnapshotPhysical

/-! The actual cached maximizing pair carries the positive Snapshot margin.
This converts the existential local success witness into the pair used by the
concrete global handler, without selecting a hidden physical witness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows
  UpperSnapshotProtocol UpperRepairProgram GlobalCompletion UpperSnapshotContrast
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (a : Anchor n) [Nonempty (Fin a.active.card)]
  (hk : 0 < a.active.card) (chores : Bool) (result : PhysicalResult n a.active.card)
  (facts : SnapshotSuccessFacts μ chores (enumerate a.active) a.residue result)

include facts in
theorem snapshotPending_localGap (i j : Fin a.active.card) :
    (a.snapshotPending hk chores result).localGap (if chores then .chore else .cake) i j =
      physicalGap chores (fun i => μ (enumerate a.active i)) (fun j => domain (result.1 j).cells) i j := by
  change margin (if chores then .chore else .cake)
    (fun r s => total (extendPieces a.active result.1 result.2.1.history s) r)
    (enumerate a.active i) (enumerate a.active j) = _
  cases chores <;> simp only [Bool.false_eq_true,↓reduceIte,GlobalCompletion.margin,
    physicalGap,signedGap,extendPieces_apply] <;>
    rw [total_correct μ _ (facts.allocation_wellFormed i),total_correct μ _ (facts.allocation_wellFormed j)]

include facts in
theorem snapshotPending_localBuffer (i : Fin a.active.card) :
    (a.snapshotPending hk chores result).localBuffer i =
      (μ (enumerate a.active i)).real (domain result.2.1.cells) :=
  total_correct μ _ facts.residue_wellFormed _

include facts in
theorem snapshotPending_positive (hnonterminal : result.2.1.cells ≠ []) :
    ∀ i, 0 < (μ (enumerate a.active i)).real (domain (a.snapshotPending hk chores result).buffer.cells) :=
  (facts.terminal_or_margin.resolve_left hnonterminal).1

include facts in
theorem snapshotPending_positive_active (hnonterminal : result.2.1.cells ≠ [])
    (i : Fin n) (hi : i ∈ a.active) :
    0 < (μ i).real (domain (a.snapshotPending hk chores result).buffer.cells) := by
  obtain ⟨j,rfl⟩ := enumerate_preimage _ i hi
  exact snapshotPending_positive μ a hk chores result facts hnonterminal j

include facts in
theorem snapshotPending_selected (haccept : result.2.2=false) (hnonterminal : result.2.1.cells ≠ []) :
    (a.snapshotPending hk chores result).witness ∈ a.active ∧
    (a.snapshotPending hk chores result).target ∈ a.active ∧
    (a.snapshotPending hk chores result).witness ≠ (a.snapshotPending hk chores result).target ∧
    0 < (a.snapshotPending hk chores result).snapshotGap (if chores then .chore else .cake)
      (a.snapshotPending hk chores result).witness (a.snapshotPending hk chores result).target ∧
    UpperShrinkPrecision.theta n * total (a.snapshotPending hk chores result).buffer
      (a.snapshotPending hk chores result).witness ≤
      (a.snapshotPending hk chores result).snapshotGap (if chores then .chore else .cake)
        (a.snapshotPending hk chores result).witness (a.snapshotPending hk chores result).target := by
  have hpos := (facts.terminal_or_margin.resolve_left hnonterminal).1
  obtain ⟨b,h,_,_,hmargin⟩ := (facts.terminal_or_margin.resolve_left hnonterminal).2
  have hgamma : 0 < UpperSnapshotProtocol.margin n := UpperShrinkPrecision.theta_positive n
  have hpass := UpperSnapshotRepair.passes_of_witness μ hk chores (enumerate a.active) result
    facts.allocation_wellFormed facts.residue_wellFormed hpos (UpperSnapshotProtocol.margin n)
    hgamma haccept b h hmargin
  have hselected := UpperSnapshotRepair.checked_physical μ hk chores (enumerate a.active) result
    facts.allocation_wellFormed facts.residue_wellFormed hpos (UpperSnapshotProtocol.margin n) hpass
  let chosen := UpperSnapshotRepair.pair hk chores (enumerate a.active) result
  refine ⟨enumerate_mem _ chosen.1,enumerate_mem _ chosen.2,?_,?_,?_⟩
  · exact fun he => hselected.1 ((enumerate_injective a.active) he)
  · change 0 < (a.snapshotPending hk chores result).localGap (if chores then .chore else .cake) chosen.1 chosen.2
    rw [snapshotPending_localGap μ a hk chores result facts]
    exact hselected.2.1
  · change UpperShrinkPrecision.theta n * (a.snapshotPending hk chores result).localBuffer chosen.1 ≤
      (a.snapshotPending hk chores result).localGap (if chores then .chore else .cake) chosen.1 chosen.2
    rw [snapshotPending_localBuffer μ a hk chores result facts,snapshotPending_localGap μ a hk chores result facts]
    exact hselected.2.2

end EnvyFreeResearch.Full.UpperGlobalPhysical
