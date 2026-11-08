import EnvyFreeResearch.Full.UpperGlobalPhysicalPendingStart

/-! Accumulating an accepted Shrink allocation under the original owners. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

theorem pending_addShrink_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    (hp : p.Physical μ whole) (pieces : Fin n → State n) (residue : State n)
    (hw : ∀j, WellFormed μ (pieces j)) (hr : WellFormed μ residue)
    (hpair : Pairwise (fun i j => Disjoint (domain (pieces i).cells) (domain (pieces j).cells)))
    (hsep : ∀j, Disjoint (domain (pieces j).cells) (domain residue.cells))
    (hcover : (⋃j, domain (pieces j).cells) ∪ domain residue.cells = domain p.buffer.cells)
    (hext : p.buffer.history ⊆ residue.history)
    (hph : ∀j, (pieces j).history ⊆ residue.history)
    (hfrozen : ∀j ∉ p.anchor.active, domain (pieces j).cells = ∅) :
    (p.addShrink pieces residue).Physical μ whole := by
  have hs j : domain (pieces j).cells ⊆ domain p.buffer.cells := by
    rw [←hcover]
    exact (subset_iUnion (fun j => domain (pieces j).cells) j).trans subset_union_left
  have hrs : domain residue.cells ⊆ domain p.buffer.cells := by
    rw [←hcover]
    exact subset_union_right
  refine ⟨hp.anchor,hp.snapshot_wf,?_,hr,hp.snapshot_pair,?_,?_,?_,?_,?_,?_,?_,?_,
    hp.snapshot_frozen,?_,hp.permutation_frozen⟩
  · intro j
    exact join_wellFormed μ _ _ _ (hp.shrunk_wf j) (hw j)
      ((hp.shrunk_sep j).mono_right (hs j)) hr.2.2.1
      (fun _ hx => hext (hp.shrunk_history j hx)) (hph j)
  · intro i j hij
    simp only [Pending.addShrink,join_domain,disjoint_union_left,disjoint_union_right]
    exact ⟨⟨hp.shrunk_pair hij,((hp.shrunk_sep j).mono_right (hs i)).symm⟩,
      ⟨(hp.shrunk_sep i).mono_right (hs j),hpair hij⟩⟩
  · intro i j
    simp only [Pending.addShrink,join_domain,disjoint_union_left]
    exact ⟨hp.cross i j,((hp.snapshot_sep j).mono_right (hs i)).symm⟩
  · intro j
    exact (hp.snapshot_sep j).mono_right hrs
  · intro j
    simp only [Pending.addShrink,join_domain,disjoint_union_left]
    exact ⟨(hp.shrunk_sep j).mono_right hrs,hsep j⟩
  · simp only [Pending.addShrink,join_domain,iUnion_union_distrib]
    calc
      ((⋃j, domain (p.shrunk j).cells) ∪ (⋃j, domain (pieces j).cells)) ∪
          (⋃j, domain (p.snapshot j).cells) ∪ domain residue.cells =
        (⋃j, domain (p.shrunk j).cells) ∪ (⋃j, domain (p.snapshot j).cells) ∪
          ((⋃j, domain (pieces j).cells) ∪ domain residue.cells) := by
            ext x; simp only [mem_union]; tauto
      _ = domain p.anchor.residue.cells := by rw [hcover]; exact hp.cover
  · exact fun j x hx => hext (hp.old_history j hx)
  · exact fun j x hx => hext (hp.snapshot_history j hx)
  · exact fun _ _ hx => hx
  · intro j hj
    simp only [Pending.addShrink,join_domain,hp.shrunk_frozen j hj,hfrozen j hj,union_empty]

theorem pending_transfer_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    (hp : p.Physical μ whole) (alpha : Equiv.Perm (Fin n)) (b h : Fin n)
    (hfix : ∀ j ∉ p.anchor.active, alpha j=j) : (p.transfer alpha b h).Physical μ whole :=
  ⟨hp.anchor,hp.snapshot_wf,hp.shrunk_wf,hp.buffer_wf,hp.snapshot_pair,hp.shrunk_pair,
    hp.cross,hp.snapshot_sep,hp.shrunk_sep,hp.cover,hp.old_history,hp.snapshot_history,
    hp.shrunk_history,hp.snapshot_frozen,hp.shrunk_frozen,hfix⟩

end EnvyFreeResearch.Full.UpperGlobalPhysical
