import EnvyFreeResearch.Full.UpperGlobalNormalizeCore

/-! The normalization request is interpreted as an ordinary finite query
program. Sink/zero bookkeeping makes no queries; at most one terminal half-cut
is performed. All original observers' endpoint records remain in the trace. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalNormalize
open UpperGlobalPhysical UpperCorrectionExecution UpperCircularStage UpperQueryPrograms UpperBaseCases
open Chores.QueryProgram
variable {n : ℕ}

theorem positiveCore_history (fallback : Fin n) (chores : Bool) (fuel : ℕ) (a : Anchor n) :
    (positiveCore fallback chores fuel a).anchor.residue.history = a.residue.history := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    unfold positiveCore
    split_ifs
    · rfl
    · rfl
    · exact ih _
    · rfl

theorem normalize_history (fallback : Fin n) (chores : Bool) (fuel : ℕ) (a : Anchor n) :
    (normalize fallback chores fuel a).anchor.residue.history = a.residue.history := by
  unfold normalize
  split_ifs
  · rfl
  · exact positiveCore_history _ _ _ _
  · exact positiveCore_history _ _ _ _
  · rfl

def requestProgram (chores : Bool) : Request n → QProgram n (Phase n)
  | .done a => .returned (.done a)
  | .snapshot a => .returned (.snapshot a)
  | .two a cutter chooser => (halfProgram a.residue cutter).bind (fun out =>
      .returned (.done (terminal a (finish chores cutter chooser out) out.2.history)))

def requestExecute (policy : Policy n) (chores : Bool) : Request n → Phase n
  | .done a => .done a
  | .snapshot a => .snapshot a
  | .two a cutter chooser => .done (twoAgentTerminal policy chores a cutter chooser)

def program (fallback : Fin n) (chores : Bool) (a : Anchor n) : QProgram n (Phase n) :=
  requestProgram chores (normalize fallback chores n a)

def execute (policy : Policy n) (fallback : Fin n) (chores : Bool) (a : Anchor n) : Phase n :=
  requestExecute policy chores (normalize fallback chores n a)

theorem request_executes (policy : Policy n) (chores : Bool) (request : Request n) :
    ∃ trace, Executes (totalPolicy policy) (requestProgram chores request) request.anchor.residue.history
      (requestExecute policy chores request) trace ∧
      (requestExecute policy chores request).anchor.residue.history = request.anchor.residue.history++trace ∧
      trace.length ≤ n+1 ∧ (trace.map Prod.fst).countP isCut ≤ 1 := by
  cases request with
  | done a => exact ⟨[],Executes.returned _ _,by simp [requestExecute,Request.anchor,Phase.anchor],by simp,by simp⟩
  | snapshot a => exact ⟨[],Executes.returned _ _,by simp [requestExecute,Request.anchor,Phase.anchor],by simp,by simp⟩
  | two a cutter chooser =>
    obtain ⟨trace,hex,hh,hq,hc⟩ := half_executes policy a.residue cutter
    refine ⟨trace,?_,hh,hq,hc⟩
    have h := hex.bind (fun out => Program.returned
      (Phase.done (terminal a (finish chores cutter chooser out) out.2.history)))
      (Executes.returned _ (a.residue.history++trace))
    simpa only [requestProgram,Request.anchor,requestExecute,twoAgentTerminal,cutAndChoose,List.append_nil] using h

theorem program_executes (policy : Policy n) (fallback : Fin n) (chores : Bool) (a : Anchor n) :
    ∃ trace, Executes (totalPolicy policy) (program fallback chores a) a.residue.history
      (execute policy fallback chores a) trace ∧
      (execute policy fallback chores a).anchor.residue.history = a.residue.history++trace ∧
      trace.length ≤ n+1 ∧ (trace.map Prod.fst).countP isCut ≤ 1 := by
  obtain ⟨trace,hex,hh,hq,hc⟩ := request_executes policy chores (normalize fallback chores n a)
  rw [normalize_history] at hex hh
  exact ⟨trace,hex,hh,hq,hc⟩

end EnvyFreeResearch.Full.UpperGlobalNormalize
