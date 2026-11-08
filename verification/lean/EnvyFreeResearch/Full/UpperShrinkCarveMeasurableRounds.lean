import EnvyFreeResearch.Full.UpperShrinkCarveMeasurableRefine
import EnvyFreeResearch.Full.UpperShrinkCarveMeasurableFloat
import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyBorel

/-! Actual all-round and final-assembly Borel query-program certificates. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperDomainDifference
  UpperQueryPrograms ProgramMeasurable ProtocolMeasurable Chores.QueryProgram
variable {n k : ℕ}

def carvedCode (out : UpperShrink.Carved n k) := (out.old,out.buffer)
instance carvedMeasurableSpace : MeasurableSpace (UpperShrink.Carved n k) :=
  MeasurableSpace.comap carvedCode inferInstance

theorem meshCarve_measurable : Measurable (meshCarve (n := n) (k := k)) := by
  apply measurable_comap_iff.mpr
  exact (Measurable.of_eval (fun j => meshCarve_old_measurable j)).prodMk meshCarve_buffer_measurable

theorem initial_measurable {X : Type} [MeasurableSpace X]
    (origin : X → State n) (f : X → ℝ) (ho : Measurable origin) (hf : Measurable f) :
    Measurable (fun x => initial (k := k) (origin x) (f x)) := by
  have hfrac : Measurable (fun x => fun j : Option (Fin k) => match j with
      | none => 1-(k : ℝ)*f x
      | some _ => f x) := by
    apply Measurable.of_eval
    intro j
    cases j
    · exact measurable_const.sub (measurable_const.mul hf)
    · exact hf
  apply mesh_mk_measurable
  · apply list_map_measurable
    · exact piece_mk_measurable _ _ (measurable_list_singleton.comp measurable_snd)
        (hfrac.comp measurable_fst)
    · exact state_cells_measurable.comp ho
  · exact state_history_measurable.comp ho

theorem rounds_certified (active : Fin k → Fin n) (J : ℕ) :
    ∀ {X : Type} [MeasurableSpace X] (normal : X → Fin k → ℝ) (mesh : X → Mesh n k),
      Measurable normal → Measurable mesh →
      Certified (fun x => rounds active (normal x) J (mesh x)) := by
  induction J with
  | zero =>
    intro X _ normal mesh hn hm
    exact Certified.returned _ ((floated_measurable active).comp (hn.prodMk hm))
  | succ J ih =>
    intro X _ normal mesh hn hm
    have hready := (floated_measurable active).comp (hn.prodMk hm)
    have hfirst := refinePieces_certified active _ _
      (mesh_pieces_measurable.comp hready) (mesh_history_measurable.comp hready)
    have hnext := ih (fun z : X × Mesh n k => normal z.1) (fun z => z.2)
      (hn.comp measurable_fst) measurable_snd
    exact hfirst.bind _ hnext

theorem rounds_variable_certified {X : Type} [MeasurableSpace X]
    (active : Fin k → Fin n) (normal : X → Fin k → ℝ) (mesh : X → Mesh n k) (J : X → ℕ)
    (hn : Measurable normal) (hm : Measurable mesh) (hJ : Measurable J) :
    Certified (fun x => rounds active (normal x) (J x) (mesh x)) :=
  Certified.natCases J hJ _ (fun j => rounds_certified active j normal mesh hn hm)

theorem rounds_assembled_certified {X : Type} [MeasurableSpace X]
    (active : Fin k → Fin n) (normal : X → Fin k → ℝ) (mesh : X → Mesh n k) (J : X → ℕ)
    (hn : Measurable normal) (hm : Measurable mesh) (hJ : Measurable J) :
    Certified (fun x => (rounds active (normal x) (J x) (mesh x)).bind
      (fun out => Program.returned (meshCarve out))) := by
  exact (rounds_variable_certified active normal mesh J hn hm hJ).bind _
    (Certified.returned _ (meshCarve_measurable.comp measurable_snd))

end EnvyFreeResearch.Full.UpperShrinkCarve
