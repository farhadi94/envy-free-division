import EnvyFreeResearch.Full.UpperQueryProgramsMeasurable
import EnvyFreeResearch.Full.UpperCorrectionProgram

/-! Structural Borel certificates for the actual two-endpoint circular
transaction, including its physical recorded-domain update. -/

noncomputable section

open MeasureTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperCorrectionProgramMeasurable

open Chores.QueryProgram ProgramMeasurable ProtocolMeasurable UpperQueryPrograms
  UpperQueryProgramsMeasurable UpperCircularStage UpperRecordedDomain UpperDomainDifference
  UpperCorrectionExecution UpperCorrectionProgram

abbrev Circle := UpperCircular.Circle

variable {n : ℕ} {X : Type} [MeasurableSpace X]

theorem circular_certified
    (history : X → History n) (cutter : X → Fin n) (cache : X → Component → ℝ)
    (total : X → ℝ) (cells : X → List Component) (amount : X → I) (start : X → Circle)
    (hhistory : Measurable history) (hcutter : Measurable cutter)
    (hcache : Measurable (fun p : X × Component => cache p.1 p.2))
    (htotal : Measurable total) (hcells : Measurable cells)
    (hamount : Measurable amount) (hstart : Measurable start) :
    Certified (fun x => circular (history x) (cutter x) (cache x) (total x) (cells x) (amount x) (start x)) := by
  have hfirst := sample_certified history cutter cache total cells
    (fun x => UpperCircular.value (start x)) hhistory hcutter hcache htotal hcells
    (UpperCircular.measurable_value.comp hstart)
  have hlast : Certified (fun z : X × (ℝ × History n) =>
      sample z.2.2 (cutter z.1) (cache z.1) (total z.1) (cells z.1)
        (UpperCircular.value (start z.1 + UpperCircular.project (amount z.1)))) :=
    sample_certified _ _ _ _ _ _ (measurable_snd.comp measurable_snd)
      (hcutter.comp measurable_fst)
      (hcache.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (htotal.comp measurable_fst) (hcells.comp measurable_fst)
      (UpperCircular.measurable_value.comp
        ((hstart.comp measurable_fst).add (UpperCircular.measurable_project.comp (hamount.comp measurable_fst))))
  have htail := hlast.bind
    (fun z : (X × (ℝ × History n)) × (ℝ × History n) =>
      Program.returned (z.1.2.1, z.2.1, z.2.2))
    (Certified.returned _ ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))
  exact hfirst.bind _ htail

theorem correction_certified (state : X → State n) (cutter : X → Fin n)
    (eps : X → ℝ) (start : X → Circle)
    (hstate : Measurable state) (hcutter : Measurable cutter)
    (heps : Measurable eps) (hstart : Measurable start) :
    Certified (fun z => correction (state z) (cutter z) (eps z) (start z)) := by
  have htotal := total_measurable state cutter hstate hcutter
  have hamount := amount_measurable eps _ heps htotal
  have hcircular := circular_certified (fun x => (state x).history) cutter
    (fun x => values (state x) (cutter x)) (fun x => total (state x) (cutter x))
    (fun x => (state x).cells) (fun x => amount (eps x) (total (state x) (cutter x))) start
    (state_history_measurable.comp hstate) hcutter (values_measurable state cutter hstate hcutter)
    htotal (state_cells_measurable.comp hstate) hamount hstart
  let record : X × (ℝ × ℝ × History n) → Correction := fun z =>
    ⟨amount (eps z.1) (total (state z.1) (cutter z.1)), start z.1, z.2.1, z.2.2.1⟩
  have hrecord : Measurable record := by
    apply measurable_comap_iff.mpr
    exact (hamount.comp measurable_fst).prodMk ((hstart.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have hresult : Measurable (fun z : X × (ℝ × ℝ × History n) =>
      (record z, (⟨applyCorrection (state z.1).cells (record z), z.2.2.2⟩ : State n))) := by
    apply hrecord.prodMk
    apply measurable_comap_iff.mpr
    exact (applyCorrection_measurable _ _
      (state_cells_measurable.comp (hstate.comp measurable_fst)) hrecord).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact hcircular.bind _ (Certified.returned _ hresult)

end EnvyFreeResearch.Full.UpperCorrectionProgramMeasurable
