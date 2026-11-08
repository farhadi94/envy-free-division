import EnvyFreeResearch.Full.UpperGlobalPhysical

/-! Global physical joins preserve the partition, with no new query and
with every old frozen label included in the original observer space. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

theorem transport_pairwise (old addition : Fin n → State n) (f : Equiv.Perm (Fin n))
    (history : UpperCircularStage.History n)
    (hold : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (hadd : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
    (hcross : ∀ i j, Disjoint (domain (old i).cells) (domain (addition j).cells)) :
    Pairwise (fun i j => Disjoint (domain (transport old addition f history i).cells)
      (domain (transport old addition f history j).cells)) := by
  intro i j hij
  have hne := fun h => hij (f.symm.injective h)
  simp only [transport, join_domain]
  exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hold hne, hcross _ _⟩,
    disjoint_union_right.mpr ⟨(hcross _ _).symm, hadd hne⟩⟩

theorem transport_union (old addition : Fin n → State n) (f : Equiv.Perm (Fin n))
    (history : UpperCircularStage.History n) :
    (⋃ j, domain (transport old addition f history j).cells) =
      (⋃ j, domain (old j).cells) ∪ (⋃ j, domain (addition j).cells) := by
  simp only [transport, join_domain]
  rw [iUnion_union_distrib]
  exact congrArg₂ (fun s t : Set ℝ => s ∪ t)
    (f.symm.surjective.iUnion_comp (fun j => domain (old j).cells))
    (f.symm.surjective.iUnion_comp (fun j => domain (addition j).cells))

def commit (a : Anchor n) (addition : Fin n → State n) (remaining : State n)
    (f : Equiv.Perm (Fin n)) : Anchor n where
  bundles := transport a.bundles addition f remaining.history
  residue := remaining
  active := a.active

theorem commit_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n)
    (ha : a.Physical μ whole) (addition : Fin n → State n) (remaining : State n)
    (f : Equiv.Perm (Fin n))
    (hadd : ∀ j, WellFormed μ (addition j)) (hr : WellFormed μ remaining)
    (hpair : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
    (hsep : ∀ j, Disjoint (domain (addition j).cells) (domain remaining.cells))
    (hcover : (⋃ j, domain (addition j).cells) ∪ domain remaining.cells = domain a.residue.cells)
    (holdhist : ∀ j, (a.bundles j).history ⊆ remaining.history)
    (haddhist : ∀ j, (addition j).history ⊆ remaining.history) :
    (commit a addition remaining f).Physical μ whole := by
  have hsub (j : Fin n) : domain (addition j).cells ⊆ domain a.residue.cells := by
    rw [← hcover]
    exact (subset_iUnion (fun j => domain (addition j).cells) j).trans subset_union_left
  have hrs : domain remaining.cells ⊆ domain a.residue.cells := by
    rw [← hcover]
    exact subset_union_right
  have hcross (i j : Fin n) := (ha.separate i).mono_right (hsub j)
  refine ⟨?_,hr,transport_pairwise a.bundles addition f remaining.history ha.pairwise hpair hcross,?_,?_⟩
  · intro j
    exact join_wellFormed μ _ _ _ (ha.bundles_wellFormed _) (hadd _) (hcross _ _)
      hr.2.2.1 (holdhist _) (haddhist _)
  · intro j
    change Disjoint (domain (transport a.bundles addition f remaining.history j).cells) _
    simp only [transport,join_domain]
    exact disjoint_union_left.mpr ⟨(ha.separate _).mono_right hrs,hsep _⟩
  · change (⋃ j, domain (transport a.bundles addition f remaining.history j).cells) ∪ domain remaining.cells = whole
    rw [transport_union, union_assoc, hcover, ha.cover]

end EnvyFreeResearch.Full.UpperGlobalPhysical
