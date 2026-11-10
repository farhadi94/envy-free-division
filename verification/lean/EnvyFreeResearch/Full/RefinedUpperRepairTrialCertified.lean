import EnvyFreeResearch.Full.RefinedUpperRepairTrial

/-! Joint Borel next-action certification for the literal new Repair trial. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairTrial
open UpperRecordedDomain UpperCorrectionExecution UpperCorrectionLoop UpperCircularStage UpperStageMeasurable
  UpperRepairJobs UpperQueryPrograms Chores.QueryProgram ProgramMeasurable RefinedUpperPreparationProgram
  RefinedUpperRepairTargets RefinedUpperCorrectionSetup
variable {n k coarse fine r : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

lemma rejected_measurable (origin : X → State n) (p : X → Prepared n k coarse fine)
    (ho : Measurable origin) (hp : Measurable p) : Measurable (fun x => rejected (origin x) (p x)) := by
  apply loop_mk_measurable _ _ _ _ measurable_const measurable_const
  apply measurable_comap_iff.mpr
  change Measurable (fun x => ((origin x).cells,(p x).2.1.history))
  exact (state_cells_measurable.comp ho).prodMk
    (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp hp)))

theorem continuation_certified (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (p : X → Prepared n k coarse fine) (eta lam : ℝ)
    (tape : X → Fin k → Fin r → UpperCircular.Circle)
    (ho : Measurable origin) (hp : Measurable p) (htape : ∀ i, Measurable (fun x => tape x i)) :
    Certified (fun x => continuation chores active (origin x) (p x) eta lam (tape x)) := by
  have hres := measurable_fst.comp (measurable_snd.comp hp)
  have hcuts (e) := (measurable_pi_apply e).comp (UpperGridData.cuts_measurable _ (measurable_fst.comp hp))
  have htargets := targets_measurable chores active p eta lam hp
  have hjobs := tasks_measurable active _ _ _ (fun _ => eta) (fun _ => lam)
    hres hcuts htargets measurable_const measurable_const
  have hstart := startState_measurable active _ _ _ (fun _ => eta)
    hres hcuts htargets measurable_const
  have hbase := RefinedUpperRepairBatchCertified.program_certified _ _ tape
    (fun j => (measurable_pi_apply j).comp hjobs) hstart htape
  have htail := hbase.bind (fun z => .returned (p z.1,z.2.2))
    (Certified.returned _ ((hp.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  exact Certified.branch _ (approved_measurable chores active p lam hp) _ _ htail
    (Certified.returned _ (hp.prodMk (rejected_measurable origin p ho hp)))

theorem program_certified (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q m L : ℕ)
    (draw : X → Fin m → Fin k × I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : X → Fin k → Fin r → UpperCircular.Circle)
    (ho : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hd : ∀ j, Measurable (fun x => draw x j)) (hpi : Measurable pi)
    (ht : ∀ j, Measurable (fun x => threshold x j)) (htape : ∀ j, Measurable (fun x => tape x j)) :
    Certified (fun x => program hk chores active (origin x) (old x) q m L (draw x) (pi x) (threshold x) eta lam (tape x)) := by
  have hbase := RefinedUpperPreparationProgram.program_certified hk chores active origin old q m L draw pi threshold ho hold hd hpi ht
  exact hbase.bind _
    (continuation_certified chores active
      (fun z : X × Prepared n k (UpperRecordedQuantiles.count (Agent := Fin k) q) m => origin z.1)
      Prod.snd eta lam (fun z => tape z.1) (ho.comp measurable_fst) measurable_snd
      (fun j => (htape j).comp measurable_fst))

end EnvyFreeResearch.Full.RefinedUpperRepairTrial
