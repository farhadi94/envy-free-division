import EnvyFreeResearch.Full.UpperGlobalPhysicalPending

/-! Entering the pending phase from a literal Snapshot partition. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

theorem pending_start_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n)
    (ha : a.Physical μ whole) (pieces : Fin n → State n) (residue : State n) (b h : Fin n)
    (hw : ∀j, WellFormed μ (pieces j)) (hr : WellFormed μ residue)
    (hpair : Pairwise (fun i j => Disjoint (domain (pieces i).cells) (domain (pieces j).cells)))
    (hsep : ∀j, Disjoint (domain (pieces j).cells) (domain residue.cells))
    (hcover : (⋃j, domain (pieces j).cells) ∪ domain residue.cells = domain a.residue.cells)
    (hwh : ∀j, (a.bundles j).history ⊆ residue.history)
    (hph : ∀j, (pieces j).history ⊆ residue.history)
    (hfrozen : ∀j ∉ a.active, domain (pieces j).cells = ∅) :
    (Pending.start a pieces residue b h).Physical μ whole := by
  refine ⟨ha,hw,?_,hr,hpair,?_,?_,hsep,?_,?_,hwh,hph,?_,hfrozen,?_,?_⟩
  · intro j
    exact empty_wellFormed μ residue.history hr.2.2.1
  · intro i j hij
    simp [Pending.start,empty,domain]
  · intro i j
    simp [Pending.start,empty,domain]
  · intro j
    simp [Pending.start,empty,domain]
  · simpa only [Pending.start,empty,domain,iUnion_empty,empty_union] using hcover
  · intro j x hx
    exact hx
  · intro j hj
    rfl
  · intro j hj
    rfl

theorem pending_refresh_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    (hp : p.Physical μ whole) (history : UpperCircularStage.History n)
    (htruth : UpperEndpointCache.Truthful μ history) (hext : p.buffer.history ⊆ history) :
    (p.refresh history).Physical μ whole := by
  refine ⟨hp.anchor,hp.snapshot_wf,hp.shrunk_wf,?_,hp.snapshot_pair,hp.shrunk_pair,
    hp.cross,hp.snapshot_sep,hp.shrunk_sep,hp.cover,?_,?_,?_,hp.snapshot_frozen,
    hp.shrunk_frozen,hp.permutation_frozen⟩
  · exact ⟨hp.buffer_wf.1,hp.buffer_wf.2.1,htruth,
      UpperEndpointCache.recordedHistory_mono _ hp.buffer_wf.2.2.2 hext⟩
  · exact fun j x hx => hext (hp.old_history j hx)
  · exact fun j x hx => hext (hp.snapshot_history j hx)
  · exact fun j x hx => hext (hp.shrunk_history j hx)

end EnvyFreeResearch.Full.UpperGlobalPhysical
