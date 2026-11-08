import EnvyFreeResearch.Full.UpperSnapshotRepetitionProgram
import EnvyFreeResearch.Full.UpperSnapshotRepetitionInvariant

/-! The rejection event of the actual first-accepting loop equals the
fresh-product recursive event used in the amplification proof. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition

def drawList {Draw : Type} : {m : ℕ} → Tape Draw m → List Draw
  | 0, _ => []
  | _+1, t => t.1 :: drawList t.2

theorem drawList_length {Draw : Type} (m : ℕ) (t : Tape Draw m) :
    (drawList t).length=m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [drawList,List.length_cons,ih]

theorem failed_iff_run_none {State Draw Output : Type}
    (step : State → Draw → State × Option Output) (m : ℕ)
    (s : State) (t : Tape Draw m) :
    failed (fun s d => (step s d).1) (fun s d => (step s d).2.isNone) m s t ↔
      (run step (drawList t) s).2=none := by
  induction m generalizing s with
  | zero => simp [failed,drawList,run]
  | succ m ih =>
    cases ho : (step s t.1).2 with
    | none => simpa only [failed,drawList,run,ho,Option.isNone_none,true_and] using ih (step s t.1).1 t.2
    | some a => simp [failed,drawList,run,ho]

theorem run_failure_sixteen {State Draw Output : Type}
    [MeasurableSpace State] [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho]
    (step : State → Draw → State × Option Output)
    (hn : Measurable (fun p : State × Draw => (step p.1 p.2).1))
    (hr : Measurable (fun p : State × Draw => (step p.1 p.2).2.isNone))
    (Inv : State → Prop)
    (hnext : ∀ s d, Inv s → (step s d).2=none → Inv (step s d).1)
    (k : ℕ) (hk : 1 ≤ k)
    (hchance : ∀ s, Inv s → rho {d | (step s d).2=none} ≤ ENNReal.ofReal (1-1/(8*(k:ℝ))))
    (s : State) (hs : Inv s) :
    law rho (16*k) {t | (run step (drawList t) s).2=none} ≤ ENNReal.ofReal ((1:ℝ)/4) := by
  have heq : {t : Tape Draw (16*k) | (run step (drawList t) s).2=none} =
      {t | failed (fun s d => (step s d).1) (fun s d => (step s d).2.isNone) (16*k) s t} := by
    ext t
    exact (failed_iff_run_none step (16*k) s t).symm
  rw [heq]
  apply sixteen_trials_failure rho _ _ hn hr Inv ?_ k hk ?_ s hs
  · intro state d hg hd
    exact hnext state d hg (Option.isNone_iff_eq_none.mp hd)
  · intro state hg
    simpa only [Option.isNone_iff_eq_none] using hchance state hg

end EnvyFreeResearch.Full.UpperSnapshotRepetition
