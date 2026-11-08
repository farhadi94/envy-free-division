import EnvyFreeResearch.Full.UpperGlobalProtocolMachine

/-! Borel coding of the actual pending state. -/
noncomputable section
open MeasureTheory
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCorrectionExecution
variable {n : ℕ}

def Pending.code (p : Pending n) :=
  (p.anchor,(p.snapshot,(p.shrunk,(p.buffer,(p.permutation,(p.witness,p.target))))))

instance : MeasurableSpace (Pending n) := MeasurableSpace.comap Pending.code inferInstance

theorem pending_code_measurable : Measurable (Pending.code (n:=n)) := comap_measurable _

theorem pending_anchor_measurable : Measurable (Pending.anchor (n:=n)) :=
  measurable_fst.comp pending_code_measurable

theorem pending_snapshot_measurable : Measurable (Pending.snapshot (n:=n)) :=
  measurable_fst.comp (measurable_snd.comp pending_code_measurable)

theorem pending_shrunk_measurable : Measurable (Pending.shrunk (n:=n)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp pending_code_measurable))

theorem pending_buffer_measurable : Measurable (Pending.buffer (n:=n)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp pending_code_measurable)))

theorem pending_permutation_measurable : Measurable (Pending.permutation (n:=n)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp pending_code_measurable))))

theorem pending_witness_measurable : Measurable (Pending.witness (n:=n)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp pending_code_measurable)))))

theorem pending_target_measurable : Measurable (Pending.target (n:=n)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp pending_code_measurable)))))

theorem pending_mk_measurable {X : Type} [MeasurableSpace X]
    (a : X → Anchor n) (snapshot shrunk : X → Fin n → State n) (buffer : X → State n)
    (f : X → Equiv.Perm (Fin n)) (b h : X → Fin n)
    (ha : Measurable a) (hs : Measurable snapshot) (hh : Measurable shrunk)
    (hr : Measurable buffer) (hf : Measurable f) (hb : Measurable b) (ht : Measurable h) :
    Measurable (fun x => (⟨a x,snapshot x,shrunk x,buffer x,f x,b x,h x⟩ : Pending n)) :=
  measurable_comap_iff.mpr (ha.prodMk (hs.prodMk (hh.prodMk (hr.prodMk (hf.prodMk (hb.prodMk ht))))))

def Phase.code : Phase n → (Fin 3 × Anchor n) ⊕ (Fin 3 × Pending n × ℝ)
  | .normalize a => .inl (0,a)
  | .snapshot a => .inl (1,a)
  | .done a => .inl (2,a)
  | .firstShrink p G => .inr (0,p,G)
  | .secondShrink p => .inr (1,p,0)
  | .finalRepair p => .inr (2,p,0)

instance : MeasurableSpace (Phase n) := MeasurableSpace.comap Phase.code inferInstance

theorem phase_normalize_measurable : Measurable (Phase.normalize (n:=n)) :=
  measurable_comap_iff.mpr (measurable_inl.comp (measurable_const.prodMk measurable_id))
theorem phase_snapshot_measurable : Measurable (Phase.snapshot (n:=n)) :=
  measurable_comap_iff.mpr (measurable_inl.comp (measurable_const.prodMk measurable_id))
theorem phase_done_measurable : Measurable (Phase.done (n:=n)) :=
  measurable_comap_iff.mpr (measurable_inl.comp (measurable_const.prodMk measurable_id))
theorem phase_secondShrink_measurable : Measurable (Phase.secondShrink (n:=n)) :=
  measurable_comap_iff.mpr (measurable_inr.comp (measurable_const.prodMk
    (measurable_id.prodMk measurable_const)))
theorem phase_finalRepair_measurable : Measurable (Phase.finalRepair (n:=n)) :=
  measurable_comap_iff.mpr (measurable_inr.comp (measurable_const.prodMk
    (measurable_id.prodMk measurable_const)))
theorem phase_firstShrink_measurable :
    Measurable (fun x : Pending n × ℝ => Phase.firstShrink x.1 x.2) :=
  measurable_comap_iff.mpr (measurable_inr.comp (measurable_const.prodMk measurable_id))

end EnvyFreeResearch.Full.UpperGlobalPhysical
