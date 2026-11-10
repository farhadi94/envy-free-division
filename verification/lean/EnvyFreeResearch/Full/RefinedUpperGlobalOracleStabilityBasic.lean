import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.ChoresProgram

/-! Observable actions survive a continuation that absorbs terminal values.
The result holds for every supplied finite history, including histories that
do not arise from a legal execution. -/
namespace EnvyFreeResearch.Full.RefinedUpperGlobalOracleStability
open OracleProtocol Chores.QueryProgram
variable {Q R A B C : Type*}

def Observable (terminal : A → Prop) : Action Q A → Prop
  | .ask _ => True
  | .diverge => True
  | .returned a => terminal a

theorem bind_associative (p : Program Q R A) (f : A → Program Q R B)
    (g : B → Program Q R C) : (p.bind f).bind g=p.bind (fun a => (f a).bind g) := by
  induction p with
  | returned a => rfl
  | failed => rfl
  | ask q next ih =>
    simp only [Program.bind]
    congr 1
    funext r
    exact ih r

theorem after_bind_action_eq (terminal : A → Prop) (p : Program Q R A)
    (f : A → Program Q R A) (habsorb : ∀ a, terminal a → f a=.returned a)
    (history : History Q R) (hobs : Observable terminal (p.after history).action) :
    ((p.bind f).after history).action=(p.after history).action := by
  induction history generalizing p with
  | nil =>
    cases p with
    | returned a =>
      change terminal a at hobs
      simp only [Program.bind,Program.after,Program.action]
      rw [habsorb a hobs]
    | ask q next => rfl
    | failed => rfl
  | cons qr history ih =>
    cases p with
    | returned a =>
      change terminal a at hobs
      rw [Program.bind,habsorb a hobs]
    | ask q next => exact ih (next qr.2) hobs
    | failed => rfl

theorem after_bind_observable (terminal : A → Prop) (p : Program Q R A)
    (f : A → Program Q R A) (habsorb : ∀ a, terminal a → f a=.returned a)
    (history : History Q R) (hobs : Observable terminal (p.after history).action) :
    Observable terminal ((p.bind f).after history).action := by
  rw [after_bind_action_eq terminal p f habsorb history hobs]
  exact hobs

end EnvyFreeResearch.Full.RefinedUpperGlobalOracleStability
