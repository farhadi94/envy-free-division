import EnvyFreeResearch.Full.UpperRecordedGridProgramMeasurable
import EnvyFreeResearch.Full.UpperCorrectionStageProgramMeasurable
import EnvyFreeResearch.Full.UpperPreparedTrialProgram

/-! Joint Borel certification of the compiled grid/preparation/correction
trial. Only the policy-free finite preparation computations remain inputs. -/

noncomputable section

open MeasureTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperPreparedTrialProgramMeasurable

open Chores.QueryProgram ProgramMeasurable ProtocolMeasurable UpperRecordedDomain
  UpperCorrectionExecution UpperCircularStage UpperQueryPrograms UpperGridData
  UpperPreparedTrialProgram

variable {n k q m : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem rollback_measurable (origin : X → State n)
    (result : X → UpperCorrectionStageProgram.Result n k)
    (horigin : Measurable origin) (hresult : Measurable result) :
    Measurable (fun x => rollback (origin x) (result x)) := by
  have hrestore : Measurable (fun x => (⟨(origin x).cells, (result x).2.1.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ((origin x).cells, (result x).2.1.history))
    exact (state_cells_measurable.comp horigin).prodMk
      (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp hresult)))
  have hstopped := measurable_snd.comp (measurable_snd.comp hresult)
  exact (measurable_const.prodMk (hrestore.prodMk measurable_const)).ite
    (measurableSet_eq_fun hstopped (measurable_const (a := true))) hresult

theorem continuation_certified (active : Fin k → Fin n) (origin : X → State n)
    (data : X → Grid n k q m) (theta : I)
    (labels : X → Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : X → ℝ) (targets : X → Grid n k q m → Fin k → ℝ)
    (approved : X → Grid n k q m → Bool) (starts : X → Fin k → UpperCircular.Circle)
    (horigin : Measurable origin) (hdata : Measurable data)
    (hlabels : ∀ p, Measurable (fun x => labels x p)) (heta : Measurable eta) (hlam : Measurable lam)
    (htargets : ∀ j, Measurable (fun x => targets x (data x) j))
    (happroved : Measurable (fun x => approved x (data x)))
    (hstarts : ∀ j, Measurable (fun x => starts x j)) :
    Certified (fun x => continuation active (origin x) (data x) theta (labels x)
      (eta x) (lam x) (targets x) (approved x) (starts x)) := by
  have hreserve := reserve_measurable data theta labels hdata hlabels
  have hcuts := cuts_measurable data hdata
  have hstage := UpperCorrectionStageProgramMeasurable.program_certified active
    _ _ _ eta lam starts hreserve (fun e => (measurable_pi_apply e).comp hcuts)
    htargets heta hlam hstarts
  have hwrapped : Measurable (fun z : X × UpperCorrectionStageProgram.Result n k =>
      (data z.1, rollback (origin z.1) z.2)) :=
    (hdata.comp measurable_fst).prodMk
      (rollback_measurable _ _ (horigin.comp measurable_fst) measurable_snd)
  have hyes := hstage.bind _ (Certified.returned _ hwrapped)
  have habortState : Measurable (fun x => (⟨(origin x).cells, (data x).2.2.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ((origin x).cells, (data x).2.2.history))
    exact (state_cells_measurable.comp horigin).prodMk
      (state_history_measurable.comp (measurable_snd.comp (measurable_snd.comp hdata)))
  have hno : Certified (fun x => (Program.returned
      (data x, (fun _ : Fin k => ([] : List Component)),
        (⟨(origin x).cells, (data x).2.2.history⟩ : State n), true) : QProgram n (Result n k q m))) :=
    Certified.returned _ (hdata.prodMk
      (measurable_const.prodMk (habortState.prodMk (measurable_const (a := true)))))
  exact Certified.branch _ happroved _ _ hyes hno

theorem program_certified (active : Fin k → Fin n) (origin : X → State n)
    (q m : ℕ) (draw : X → Fin m → Fin k × I) (theta : I)
    (labels : X → Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : X → ℝ) (targets : X → Grid n k q m → Fin k → ℝ)
    (approved : X → Grid n k q m → Bool) (starts : X → Fin k → UpperCircular.Circle)
    (horigin : Measurable origin) (hdraw : ∀ i, Measurable (fun x => draw x i))
    (hlabels : ∀ p, Measurable (fun x => labels x p)) (heta : Measurable eta) (hlam : Measurable lam)
    (htargets : ∀ j, Measurable (fun z : X × Grid n k q m => targets z.1 z.2 j))
    (happroved : Measurable (fun z : X × Grid n k q m => approved z.1 z.2))
    (hstarts : ∀ j, Measurable (fun x => starts x j)) :
    Certified (fun x => program active (origin x) q m (draw x) theta (labels x)
      (eta x) (lam x) (targets x) (approved x) (starts x)) := by
  have hgrid := UpperRecordedGridProgramMeasurable.prepare_certified active origin q m draw horigin hdraw
  have htail := continuation_certified active (fun z : X × Grid n k q m => origin z.1)
    (fun z => z.2) theta (fun z => labels z.1) (fun z => eta z.1) (fun z => lam z.1)
    (fun z => targets z.1) (fun z => approved z.1) (fun z => starts z.1)
    (horigin.comp measurable_fst) measurable_snd (fun p => (hlabels p).comp measurable_fst)
    (heta.comp measurable_fst) (hlam.comp measurable_fst) htargets happroved
    (fun j => (hstarts j).comp measurable_fst)
  exact hgrid.bind _ htail

end EnvyFreeResearch.Full.UpperPreparedTrialProgramMeasurable
