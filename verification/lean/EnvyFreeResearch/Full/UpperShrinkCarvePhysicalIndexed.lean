import EnvyFreeResearch.Full.UpperShrinkCarvePhysical
import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyMesh

noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution
variable {n k : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem Mesh.Physical.indexed_wellFormed {mesh : Mesh n k} {U : Set ℝ}
    (h : mesh.Physical μ U) (e : Fin mesh.pieces.length) : WellFormed μ (meshStates mesh e) :=
  h.pieces _ (List.get_mem _ e)

theorem Mesh.Physical.indexed_disjoint {mesh : Mesh n k} {U : Set ℝ}
    (h : mesh.Physical μ U) : Pairwise (fun e f =>
      Disjoint (domain (meshStates mesh e).cells) (domain (meshStates mesh f).cells)) := by
  intro e f hef
  have hne : e.val ≠ f.val := fun he => hef (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h.disjoint.rel_getElem_of_lt e.isLt f.isLt hlt
  · exact (h.disjoint.rel_getElem_of_lt f.isLt e.isLt hgt).symm

theorem Mesh.Physical.indexed_cover {mesh : Mesh n k} {U : Set ℝ}
    (h : mesh.Physical μ U) : (⋃ e, domain (meshStates mesh e).cells) = U := by
  rw [← h.cover]
  ext x
  simp only [Set.mem_iUnion,mem_pieceDomain]
  constructor
  · rintro ⟨e,he⟩
    exact ⟨mesh.pieces.get e,List.get_mem _ e,he⟩
  · rintro ⟨p,hp,hx⟩
    obtain ⟨e,he⟩ := List.mem_iff_get.mp hp
    exact ⟨e,by simpa only [meshStates,he] using hx⟩

end EnvyFreeResearch.Full.UpperShrinkCarve
