import EnvyFreeResearch.Full.UpperShrinkCarveRounds
import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyMesh

noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve

theorem mesh_split_count (mesh : Mesh n k) :
    (UpperWholePayments.splitCells (meshFractions mesh)).card = splitCount mesh.pieces := by
  have h := splitCount_ofFn (fun e : Fin mesh.pieces.length => mesh.pieces.get e)
  simp only [List.ofFn_get] at h
  have hs : UpperWholePayments.splitCells (meshFractions mesh) =
      Finset.univ.filter (fun e : Fin mesh.pieces.length => split (mesh.pieces.get e)) := by
    ext e
    constructor
    · intro he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩
    · intro he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩
  rw [hs,Finset.card_eq_sum_ones,Finset.sum_filter,h]

theorem rounds_sparse (policy : UpperCircularStage.Policy n) (active : Fin k → Fin n)
    (normal : Fin k → ℝ) (J : ℕ) (mesh : Mesh n k) (hv : mesh.FractionsValid) :
    splitCount (roundsExecute policy active normal J mesh).pieces ≤ k^2 := by
  induction J generalizing mesh with
  | zero => exact (floated_valid_count active normal mesh hv).2
  | succ J ih =>
    exact ih _ (refinement_valid policy active _ _ (floated_valid_count active normal mesh hv).1)

end EnvyFreeResearch.Full.UpperShrinkCarve
