import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair

/-! Cancellation of old whole bundles from actual Repair conservation.
These set identities retain zero-valued fragments literally. -/
noncomputable section
open Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
variable {k : ℕ}

theorem additions_partition (old addition output : Fin k → Set ℝ)
    (f : Equiv.Perm (Fin k)) (origin remaining : Set ℝ)
    (hlabel : ∀ j, output (f j) = old j ∪ addition j)
    (hcover : (⋃ j, output j) ∪ remaining = (⋃ j, old j) ∪ origin)
    (hdis : ∀ j, Disjoint (old j) origin)
    (hadd : ∀ j, addition j ⊆ origin) (hrem : remaining ⊆ origin) :
    (⋃ j, addition j) ∪ remaining = origin := by
  apply Subset.antisymm
  · exact union_subset (iUnion_subset hadd) hrem
  · intro x hx
    have hfull : x ∈ (⋃ j, output j) ∪ remaining := by
      rw [hcover]
      exact Or.inr hx
    rcases hfull with ho | hr
    · obtain ⟨recipient,ho⟩ := mem_iUnion.mp ho
      obtain ⟨j,rfl⟩ := f.surjective recipient
      rw [hlabel] at ho
      rcases ho with hold | hnew
      · exact False.elim (disjoint_left.mp (hdis j) hold hx)
      · exact Or.inl (mem_iUnion.mpr ⟨j,hnew⟩)
    · exact Or.inr hr

theorem additions_pairwise (old addition output : Fin k → Set ℝ)
    (f : Equiv.Perm (Fin k)) (hlabel : ∀ j, output (f j) = old j ∪ addition j)
    (hpair : Pairwise (fun i j => Disjoint (output i) (output j))) :
    Pairwise (fun i j => Disjoint (addition i) (addition j)) := by
  intro i j hij
  apply (hpair (fun h => hij (f.injective h))).mono
  · rw [hlabel]
    exact subset_union_right
  · rw [hlabel]
    exact subset_union_right

theorem additions_separate (old addition output : Fin k → Set ℝ)
    (f : Equiv.Perm (Fin k)) (remaining : Set ℝ)
    (hlabel : ∀ j, output (f j) = old j ∪ addition j)
    (hsep : ∀ j, Disjoint (output j) remaining) :
    ∀ j, Disjoint (addition j) remaining := by
  intro j
  apply (hsep (f j)).mono_left
  rw [hlabel]
  exact subset_union_right

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
