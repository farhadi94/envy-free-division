import EnvyFreeResearch.Full.UpperShrinkCarveFractions
import EnvyFreeResearch.Full.UpperShrinkCarveCosts

/-! The actual finite recursive carving program and all-round query ledger.
The number of calls is derived from the selector's sparse fractional support,
not assumed as a successful carving specification. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperCircularStage UpperQueryPrograms Chores.QueryProgram

def roundsExecute (policy : Policy n) (active : Fin k → Fin n) (normal : Fin k → ℝ) :
    ℕ → Mesh n k → Mesh n k
  | 0, mesh => floated active normal mesh
  | J+1, mesh =>
    let ready := floated active normal mesh
    let next := refinePiecesExecute policy active ready.pieces ready.history
    roundsExecute policy active normal J next

theorem rounds_executes (policy : Policy n) (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (J : ℕ) (mesh : Mesh n k) :
    ∃ trace, Executes (totalPolicy policy) (rounds active normal J mesh) mesh.history
      (roundsExecute policy active normal J mesh) trace ∧
      (roundsExecute policy active normal J mesh).history = mesh.history ++ trace := by
  induction J generalizing mesh with
  | zero => exact ⟨[],Executes.returned _ _,by simp [roundsExecute,floated]⟩
  | succ J ih =>
    let ready := floated active normal mesh
    let next := refinePiecesExecute policy active ready.pieces ready.history
    obtain ⟨first,hfirst,hh⟩ := refinePieces_executes policy active ready.pieces ready.history
    obtain ⟨tail,htail,ht⟩ := ih next
    refine ⟨first++tail,?_,?_⟩
    · exact hfirst.bind (fun next => rounds active normal J next) (by rw [←hh]; exact htail)
    · change (roundsExecute policy active normal J next).history = _
      rw [ht,hh,List.append_assoc]
      rfl

theorem rounds_fractions_valid (policy : Policy n) (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (J : ℕ) (mesh : Mesh n k) (hvalid : mesh.FractionsValid) :
    (roundsExecute policy active normal J mesh).FractionsValid := by
  induction J generalizing mesh with
  | zero => exact (floated_valid_count active normal mesh hvalid).1
  | succ J ih =>
    exact ih _ (refinement_valid policy active _ _ (floated_valid_count active normal mesh hvalid).1)

theorem rounds_query_bound (policy : Policy n) (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (J : ℕ) (mesh : Mesh n k) (hvalid : mesh.FractionsValid) :
    (roundsExecute policy active normal J mesh).history.length ≤ mesh.history.length+J*k^3*(n+1) := by
  induction J generalizing mesh with
  | zero => simp [roundsExecute,floated]
  | succ J ih =>
    let ready := floated active normal mesh
    let next := refinePiecesExecute policy active ready.pieces ready.history
    have hv := floated_valid_count active normal mesh hvalid
    have hn := refinement_valid policy active ready.pieces ready.history hv.1
    have ht := ih next hn
    have hf := refinePieces_query_bound policy active ready.pieces ready.history
    have hb : splitCount ready.pieces*k*(n+1) ≤ k^3*(n+1) := by
      calc
        _ ≤ k^2*k*(n+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hv.2)
        _ = _ := by ring
    change (roundsExecute policy active normal J next).history.length ≤ _
    change next.history.length ≤ mesh.history.length+splitCount ready.pieces*k*(n+1) at hf
    calc
      _ ≤ next.history.length+J*k^3*(n+1) := ht
      _ ≤ mesh.history.length+k^3*(n+1)+J*k^3*(n+1) := by omega
      _ = mesh.history.length+(J+1)*k^3*(n+1) := by ring

theorem rounds_cut_bound (policy : Policy n) (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (J : ℕ) (mesh : Mesh n k) (hvalid : mesh.FractionsValid) :
    cuts (roundsExecute policy active normal J mesh).history ≤ cuts mesh.history+J*k^3 := by
  induction J generalizing mesh with
  | zero => simp [roundsExecute,floated]
  | succ J ih =>
    let ready := floated active normal mesh
    let next := refinePiecesExecute policy active ready.pieces ready.history
    have hv := floated_valid_count active normal mesh hvalid
    have hn := refinement_valid policy active ready.pieces ready.history hv.1
    have ht := ih next hn
    have hf := refinePieces_cut_bound policy active ready.pieces ready.history
    have hb : splitCount ready.pieces*k ≤ k^3 := by
      calc
        _ ≤ k^2*k := Nat.mul_le_mul_right _ hv.2
        _ = _ := by ring
    change cuts (roundsExecute policy active normal J next).history ≤ _
    change cuts next.history ≤ cuts mesh.history+splitCount ready.pieces*k at hf
    calc
      _ ≤ cuts next.history+J*k^3 := ht
      _ ≤ cuts mesh.history+k^3+J*k^3 := by omega
      _ = cuts mesh.history+(J+1)*k^3 := by ring

end EnvyFreeResearch.Full.UpperShrinkCarve
