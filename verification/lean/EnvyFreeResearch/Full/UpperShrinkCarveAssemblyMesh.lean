import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyBounds
import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyMeasurable

/-! The list-based final operation on the actual variable-length carve mesh. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperComponentAssembly
  UpperEndpointCache ProtocolMeasurable
variable {n k : ℕ}

def meshStates (mesh : Mesh n k) (e : Fin mesh.pieces.length) : State n :=
  ⟨(mesh.pieces.get e).cells,mesh.history⟩
def meshFractions (mesh : Mesh n k) (e : Fin mesh.pieces.length) := (mesh.pieces.get e).fraction

def meshCarve (mesh : Mesh n k) : UpperShrink.Carved n k where
  old j := state ((mesh.pieces.filter (fun p => p.fraction (some j)=1)).flatMap Piece.cells) mesh.history
  buffer := state ((mesh.pieces.filter (fun p => ∀ j, p.fraction (some j)≠1)).flatMap Piece.cells) mesh.history

theorem selected_list (pieces : List (Piece k)) (history : History n) (test : Piece k → Prop)
    [DecidablePred test] :
    selectedState (fun e : Fin pieces.length => (⟨(pieces.get e).cells,history⟩ : State n)) history
      (Finset.univ.filter (fun e => test (pieces.get e))) =
      state ((pieces.filter test).flatMap Piece.cells) history := by
  unfold selectedState family familyComponents
  congr 1
  have hm : (List.ofFn (fun e : Fin pieces.length =>
      (if e ∈ Finset.univ.filter (fun e => test (pieces.get e)) then
        (⟨(pieces.get e).cells,history⟩ : State n) else empty history).cells)) =
      pieces.map (fun p => if test p then p.cells else []) := by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,apply_ite,empty,List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map pieces (fun p => if test p then p.cells else []))
  rw [hm]
  clear hm
  change pieces.flatMap (fun p => if test p then p.cells else []) = _
  induction pieces with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : test p <;> simp [hp,ih]

theorem meshCarve_eq (mesh : Mesh n k) :
    meshCarve mesh = assembledCarve (meshStates mesh) mesh.history (meshFractions mesh) := by
  have ho : (meshCarve mesh).old = (assembledCarve (meshStates mesh) mesh.history (meshFractions mesh)).old := by
    funext j
    exact (selected_list mesh.pieces mesh.history (fun p => p.fraction (some j)=1)).symm
  have hb : (meshCarve mesh).buffer = (assembledCarve (meshStates mesh) mesh.history (meshFractions mesh)).buffer := by
    change state ((mesh.pieces.filter (fun p => ∀ j, p.fraction (some j)≠1)).flatMap Piece.cells) mesh.history =
      selectedState (meshStates mesh) mesh.history (dummyCells (meshFractions mesh))
    rw [← selected_list mesh.pieces mesh.history (fun p => ∀ j, p.fraction (some j)≠1)]
    congr 1
  cases h₁ : meshCarve mesh
  cases h₂ : assembledCarve (meshStates mesh) mesh.history (meshFractions mesh)
  simp only [h₁,h₂] at ho hb
  cases ho
  cases hb
  rfl

end EnvyFreeResearch.Full.UpperShrinkCarve
