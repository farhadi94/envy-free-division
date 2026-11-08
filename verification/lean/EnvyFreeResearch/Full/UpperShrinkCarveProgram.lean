import EnvyFreeResearch.Full.UpperShrinkMedian
import EnvyFreeResearch.Full.UpperFloating

/-! Concrete deterministic carving programs. Each fractional logical cell
is queried at all active medians of the same parent domain. Children inherit
its fractions before the deterministic floating selector runs again. Every
call passes the entire accumulated history, including earlier refinement.
No response policy is an input to any program definition. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperQueryPrograms
  Chores.QueryProgram

structure Piece (k : ℕ) where
  cells : List Component
  fraction : Option (Fin k) → ℝ

structure Mesh (n k : ℕ) where
  pieces : List (Piece k)
  history : History n

def split (piece : Piece k) : Prop := ∃ c, 0 < piece.fraction c ∧ piece.fraction c < 1

def medianChain (cutters : List (Fin n)) (state : State n) : QProgram n (State n) :=
  match cutters with
  | [] => .returned state
  | i :: rest => (UpperShrink.medianProgram state i).bind (fun out => medianChain rest out.2)

def medianChainExecute (policy : Policy n) (cutters : List (Fin n)) (state : State n) : State n :=
  match cutters with
  | [] => state
  | i :: rest => medianChainExecute policy rest (UpperShrink.median policy state i).2

def children (piece : Piece k) (state : State n) : List (Piece k) :=
  state.cells.map (fun c => ⟨[c],piece.fraction⟩)

def refinePieces (active : Fin k → Fin n) (pieces : List (Piece k)) (history : History n) :
    QProgram n (Mesh n k) :=
  match pieces with
  | [] => .returned ⟨[],history⟩
  | piece :: rest =>
    if split piece then
      (medianChain (List.ofFn active) ⟨piece.cells,history⟩).bind (fun out =>
        (refinePieces active rest out.history).bind (fun tail =>
          .returned ⟨children piece out ++ tail.pieces,tail.history⟩))
    else (refinePieces active rest history).bind (fun tail =>
      .returned ⟨piece :: tail.pieces,tail.history⟩)

def weights (active : Fin k → Fin n) (normal : Fin k → ℝ) (mesh : Mesh n k)
    (i : Fin k) (e : Fin mesh.pieces.length) : ℝ :=
  total (⟨(mesh.pieces.get e).cells,mesh.history⟩ : State n) (active i) / normal i

def floated (active : Fin k → Fin n) (normal : Fin k → ℝ) (mesh : Mesh n k) : Mesh n k :=
  let plan := UpperFloating.select (weights active normal mesh)
    (fun c : Fin mesh.pieces.length × Option (Fin k) => (mesh.pieces.get c.1).fraction c.2)
  ⟨List.ofFn (fun e : Fin mesh.pieces.length =>
    ⟨(mesh.pieces.get e).cells,fun j => plan (e,j)⟩),mesh.history⟩

def rounds (active : Fin k → Fin n) (normal : Fin k → ℝ) : ℕ → Mesh n k → QProgram n (Mesh n k)
  | 0, mesh => .returned (floated active normal mesh)
  | J+1, mesh =>
    let ready := floated active normal mesh
    (refinePieces active ready.pieces ready.history).bind (fun next => rounds active normal J next)

def initial (origin : State n) (f : ℝ) : Mesh n k :=
  ⟨origin.cells.map (fun c => ⟨[c],fun j => match j with
    | none => 1 - (k : ℝ)*f
    | some _ => f⟩),origin.history⟩

theorem medianChain_executes (policy : Policy n) (cutters : List (Fin n)) (state : State n) :
    ∃ trace, Executes (totalPolicy policy) (medianChain cutters state) state.history
      (medianChainExecute policy cutters state) trace ∧
      (medianChainExecute policy cutters state).history = state.history ++ trace := by
  induction cutters generalizing state with
  | nil => exact ⟨[],Executes.returned _ _,by simp [medianChainExecute]⟩
  | cons i rest ih =>
    obtain ⟨first,hfirst,hh⟩ := UpperShrink.median_executes policy state i
    obtain ⟨tail,htail,hhtail⟩ := ih (UpperShrink.median policy state i).2
    refine ⟨first++tail,?_,?_⟩
    · have h := hfirst.bind (fun out => medianChain rest out.2) (hh ▸ htail)
      exact h
    · change (medianChainExecute policy rest (UpperShrink.median policy state i).2).history = _
      rw [hhtail,hh,List.append_assoc]

theorem medianChain_query_bound (policy : Policy n) (cutters : List (Fin n)) (state : State n) :
    (medianChainExecute policy cutters state).history.length ≤ state.history.length + cutters.length*(n+1) := by
  induction cutters generalizing state with
  | nil => simp [medianChainExecute]
  | cons i rest ih =>
    have h := ih (UpperShrink.median policy state i).2
    have hfirst := UpperShrink.median_query_bound policy state i
    simp only [medianChainExecute,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end EnvyFreeResearch.Full.UpperShrinkCarve
