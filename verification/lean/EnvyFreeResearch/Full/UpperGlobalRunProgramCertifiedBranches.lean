import EnvyFreeResearch.Full.UpperGlobalRunProgramCertifiedCases
import EnvyFreeResearch.Full.UpperGlobalRunProgramCertifiedStages
import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableTapes

noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.ProgramCertified
open MeasureTheory UpperGlobalPhysical UpperGlobalTape UpperCircularStage UpperStageMeasurable
  UpperQueryPrograms Chores.QueryProgram ProgramMeasurable DispatchMeasurable
open scoped Classical
variable {n : ℕ}

def snapshotBranchProgram (active : Finset (Fin n)) (chores : Bool)
    (a : Anchor n) (draw : Universal n) : QProgram n (Phase n) :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    snapshotAtProgram active hk chores a (snapshotTape active (by omega) draw)
  else .returned (.done a)

def firstBranchProgram (active : Finset (Fin n)) (chores : Bool)
    (p : Pending n) (G : ℝ) (draw : Universal n) : QProgram n (Phase n) :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    firstAtProgram active (by omega) chores p G (shrinkTape active (by omega) draw)
  else .returned (.done p.anchor)

def secondBranchProgram (active : Finset (Fin n)) (chores : Bool)
    (p : Pending n) (draw : Universal n) : QProgram n (Phase n) :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    secondAtProgram active (by omega) chores p (shrinkTape active (by omega) draw)
  else .returned (.done p.anchor)

def repairBranchProgram (active : Finset (Fin n)) (chores : Bool)
    (p : Pending n) (draw : Universal n) : QProgram n (Phase n) :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    repairAtProgram active (by omega) chores p (repairTape active (by omega) draw)
  else .returned (.done p.anchor)

theorem snapshotBranchProgram_certified (active : Finset (Fin n)) (chores : Bool) :
    Certified (Function.uncurry (snapshotBranchProgram active chores)) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : Anchor n × Universal n =>
        (z.1,snapshotTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((snapshotTape_measurable active (by omega)).comp measurable_snd)
    have h := (snapshotAtProgram_certified active hk chores).comp _ hm
    apply h.congr
    intro z
    simp only [Function.uncurry,Function.comp_def,snapshotBranchProgram,dite_eq_left hk]
  · have h : Certified (Query:=Query n) (Reply:=ℝ) (fun z : Anchor n × Universal n => Program.returned (Phase.done z.1)) :=
      Certified.returned _ (phase_done_measurable.comp measurable_fst)
    apply h.congr
    intro z
    simp only [Function.uncurry,snapshotBranchProgram,dite_eq_right hk]

theorem firstBranchProgram_certified (active : Finset (Fin n)) (chores : Bool) :
    Certified (fun z : (Pending n × ℝ) × Universal n => firstBranchProgram active chores z.1.1 z.1.2 z.2) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : (Pending n × ℝ) × Universal n =>
        (z.1,shrinkTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((shrinkTape_measurable active (by omega)).comp measurable_snd)
    have h := (firstAtProgram_certified active (by omega) chores).comp _ hm
    apply h.congr
    intro z
    simp only [Function.comp_def,firstBranchProgram,dite_eq_left hk]
  · have h : Certified (Query:=Query n) (Reply:=ℝ) (fun z : (Pending n × ℝ) × Universal n => Program.returned (Phase.done z.1.1.anchor)) :=
      Certified.returned _ (phase_done_measurable.comp (pending_anchor_measurable.comp (measurable_fst.comp measurable_fst)))
    apply h.congr
    intro z
    simp only [firstBranchProgram,dite_eq_right hk]

theorem secondBranchProgram_certified (active : Finset (Fin n)) (chores : Bool) :
    Certified (Function.uncurry (secondBranchProgram active chores)) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : Pending n × Universal n =>
        (z.1,shrinkTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((shrinkTape_measurable active (by omega)).comp measurable_snd)
    have h := (secondAtProgram_certified active (by omega) chores).comp _ hm
    apply h.congr
    intro z
    simp only [Function.uncurry,Function.comp_def,secondBranchProgram,dite_eq_left hk]
  · have h : Certified (Query:=Query n) (Reply:=ℝ) (fun z : Pending n × Universal n => Program.returned (Phase.done z.1.anchor)) :=
      Certified.returned _ (phase_done_measurable.comp (pending_anchor_measurable.comp measurable_fst))
    apply h.congr
    intro z
    simp only [Function.uncurry,secondBranchProgram,dite_eq_right hk]

theorem repairBranchProgram_certified (active : Finset (Fin n)) (chores : Bool) :
    Certified (Function.uncurry (repairBranchProgram active chores)) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : Pending n × Universal n =>
        (z.1,repairTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((repairTape_measurable active (by omega)).comp measurable_snd)
    have h := (repairAtProgram_certified active (by omega) chores).comp _ hm
    apply h.congr
    intro z
    simp only [Function.uncurry,Function.comp_def,repairBranchProgram,dite_eq_left hk]
  · have h : Certified (Query:=Query n) (Reply:=ℝ) (fun z : Pending n × Universal n => Program.returned (Phase.done z.1.anchor)) :=
      Certified.returned _ (phase_done_measurable.comp (pending_anchor_measurable.comp measurable_fst))
    apply h.congr
    intro z
    simp only [Function.uncurry,repairBranchProgram,dite_eq_right hk]

def stepAtProgram (active : Finset (Fin n)) (fallback : Fin n) (chores : Bool) :=
  DispatchMeasurable.phaseCases (fun a _ => UpperGlobalNormalize.program fallback chores a)
    (snapshotBranchProgram active chores) (fun a _ => .returned (Phase.done a))
    (firstBranchProgram active chores) (secondBranchProgram active chores) (repairBranchProgram active chores)

theorem stepAtProgram_certified (active : Finset (Fin n)) (fallback : Fin n) (chores : Bool) :
    Certified (Function.uncurry (stepAtProgram active fallback chores)) :=
  phaseCases_certified _ _ _ _ _ _
    ((UpperGlobalNormalize.program_certified fallback chores).comp Prod.fst measurable_fst)
    (snapshotBranchProgram_certified active chores)
    (Certified.returned _ (phase_done_measurable.comp measurable_fst))
    (firstBranchProgram_certified active chores)
    (secondBranchProgram_certified active chores)
    (repairBranchProgram_certified active chores)
end EnvyFreeResearch.Full.UpperGlobalRun.ProgramCertified
