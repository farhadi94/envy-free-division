import EnvyFreeResearch.Full.UpperShrinkCarvePhysical

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

variable {n k : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem physical_of_same_cells {a b : Mesh n k} {U : Set ℝ}
    (h : a.Physical μ U) (hc : b.pieces.map Piece.cells = a.pieces.map Piece.cells)
    (hh : b.history = a.history) : b.Physical μ U := by
  refine ⟨hh ▸ h.truthful,?_,?_,?_⟩
  · intro p hp
    have hm : p.cells ∈ a.pieces.map Piece.cells := hc ▸ List.mem_map.mpr ⟨p,hp,rfl⟩
    obtain ⟨q,hq,hcells⟩ := List.mem_map.mp hm
    rw [hh,← hcells]
    exact h.pieces q hq
  · have hd : (a.pieces.map Piece.cells).Pairwise (fun c d => Disjoint (domain c) (domain d)) :=
      List.pairwise_map.mpr h.disjoint
    rw [← hc] at hd
    exact (List.pairwise_map (f := Piece.cells)).mp hd
  · have he := congrArg List.flatten hc
    change domain (b.pieces.flatMap Piece.cells) = U
    rw [List.flatMap_def,he]
    exact h.cover

theorem floated_physical (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (mesh : Mesh n k) (U : Set ℝ) (h : mesh.Physical μ U) :
    (floated active normal mesh).Physical μ U := by
  apply physical_of_same_cells μ (b := floated active normal mesh) h _ rfl
  simp only [floated,List.map_ofFn]
  change List.ofFn (fun e : Fin mesh.pieces.length => (mesh.pieces.get e).cells) = _
  exact List.ofFn_getElem_eq_map mesh.pieces Piece.cells

theorem initial_physical (origin : State n) (ho : WellFormed μ origin) (f : ℝ) :
    (initial (k := k) origin f).Physical μ (domain origin.cells) := by
  let p : Piece k := ⟨origin.cells,fun j => match j with
    | none => 1-(k:ℝ)*f
    | some _ => f⟩
  have he : (initial (k := k) origin f).pieces = children p origin := rfl
  refine ⟨ho.2.2.1,?_,?_,?_⟩
  · exact children_wellFormed μ p origin ho origin.history ho.2.2.1 Subset.rfl
  · exact children_disjoint p origin ho.2.1
  · exact children_domain p origin

end EnvyFreeResearch.Full.UpperShrinkCarve
