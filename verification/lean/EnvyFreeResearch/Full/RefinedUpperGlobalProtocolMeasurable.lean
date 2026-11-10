import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolState
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalCommit

/-! Measurable recorded anchors and cached numerical decisions. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

def Anchor.code (a : Anchor n) := (a.bundles,a.residue,a.active)
instance : MeasurableSpace (Anchor n) := MeasurableSpace.comap Anchor.code inferInstance

theorem anchor_code_measurable : Measurable (Anchor.code (n := n)) := comap_measurable _

theorem anchor_bundles_measurable : Measurable (Anchor.bundles (n := n)) :=
  measurable_fst.comp anchor_code_measurable

theorem anchor_residue_measurable : Measurable (Anchor.residue (n := n)) :=
  measurable_fst.comp (measurable_snd.comp anchor_code_measurable)

theorem anchor_active_measurable : Measurable (Anchor.active (n := n)) :=
  measurable_snd.comp (measurable_snd.comp anchor_code_measurable)

variable {X : Type*} [MeasurableSpace X]

theorem anchor_mk_measurable (bundles : X → Fin n → State n) (residue : X → State n)
    (active : X → Finset (Fin n)) (hb : ∀ j, Measurable (fun x => bundles x j))
    (hr : Measurable residue) (ha : Measurable active) :
    Measurable (fun x => (⟨bundles x,residue x,active x⟩ : Anchor n)) := by
  apply measurable_comap_iff.mpr
  exact (measurable_pi_lambda hb).prodMk (hr.prodMk ha)

theorem anchor_bundle_measurable (a : X → Anchor n) (ha : Measurable a) (j : Fin n) :
    Measurable (fun x => (a x).bundles j) :=
  (measurable_pi_apply j).comp (anchor_bundles_measurable.comp ha)

theorem cachedValue_measurable (a : X → Anchor n) (ha : Measurable a) (i j : Fin n) :
    Measurable (fun x => (a x).cachedValue i j) :=
  total_measurable _ (fun _ => i) (anchor_bundle_measurable a ha j) measurable_const

theorem cachedResidue_measurable (a : X → Anchor n) (ha : Measurable a) (i : Fin n) :
    Measurable (fun x => (a x).cachedResidue i) :=
  total_measurable _ (fun _ => i) (anchor_residue_measurable.comp ha) measurable_const

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
