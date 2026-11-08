import EnvyFreeResearch.Full.UpperDomainDifferenceDynamic

/-!
# Literal recorded component output for each correction

The correction's physical payment is constructed from the same recorded
endpoint refinement as its complement. This supplies an actual finite union
output, including every endpoint fragment, without any additional queries.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperCorrectionPieces

open UpperRecordedDomain UpperDomainDifference UpperPhysical UpperCircular

/-- The exact complement branch of the existing remaining-domain filter. -/
def take (cs : List Component) (r : Correction) : List Component :=
  if r.amount = 0 then [] else if r.amount = 1 then cs else
    let refined := refineAt r.last (refineAt r.first cs)
    if value r.start < value (r.start + project r.amount) then intervalAtoms r.first r.last refined
    else outsideAtoms r.last r.first refined

theorem take_domain (cs : List Component) (r : Correction) : domain (take cs r) = correctionPiece cs r := by
  have hfirst := refineAt_preserves_separated r.last r.first (refineAt r.first cs)
    (refineAt_separated r.first cs)
  have hlast := refineAt_separated r.last (refineAt r.first cs)
  unfold take correctionPiece physicalPiece
  dsimp only
  split_ifs with hz ho hw
  · rfl
  · rfl
  · rw [intervalAtoms_domain _ _ _ hfirst hlast, refineAt_domain, refineAt_domain]
  · rw [outsideAtoms_domain _ _ _ hlast hfirst, refineAt_domain, refineAt_domain]

theorem take_subset (cs : List Component) (r : Correction) : domain (take cs r) ⊆ domain cs := by
  rw [take_domain]
  exact physicalPiece_subset _ _ _ _ _

theorem take_remaining_disjoint (cs : List Component) (r : Correction) :
    Disjoint (domain (take cs r)) (domain (applyCorrection cs r)) := by
  rw [take_domain]
  change Disjoint (correctionPiece cs r) (domain (removeCorrection cs r.amount r.start r.first r.last))
  rw [removeCorrection_domain]
  exact disjoint_sdiff_self_right

theorem take_remaining_union (cs : List Component) (r : Correction) :
    domain (take cs r) ∪ domain (applyCorrection cs r) = domain cs := by
  rw [take_domain]
  change correctionPiece cs r ∪ domain (removeCorrection cs r.amount r.start r.first r.last) = _
  rw [removeCorrection_domain]
  exact union_sdiff_cancel (physicalPiece_subset _ _ _ _ _)

theorem take_ordered (cs : List Component) (hcs : Ordered cs) (r : Correction) : Ordered (take cs r) := by
  have hr := refineAt_ordered r.last _ (refineAt_ordered r.first cs hcs)
  unfold take
  split_ifs
  · simp [Ordered]
  · exact hcs
  · exact hr.filter _
  · exact hr.filter _

theorem take_disjoint (cs : List Component) (hcs : DisjointComponents cs) (r : Correction) :
    DisjointComponents (take cs r) := by
  have hr := refineAt_disjoint r.last _ (refineAt_disjoint r.first cs hcs)
  unfold take
  split_ifs
  · simp [DisjointComponents]
  · exact hcs
  · exact hr.filter _
  · exact hr.filter _

theorem take_recorded (cs : List Component) (r : Correction) {p : ℝ}
    (hp : Recorded (take cs r) p) : p = r.first ∨ p = r.last ∨ Recorded cs p := by
  unfold take at hp
  split_ifs at hp with hz ho hw
  · obtain ⟨c, hc, _⟩ := hp
    simp at hc
  · exact Or.inr (Or.inr hp)
  · obtain ⟨c, hc, hp⟩ := hp
    have hc' := (List.mem_filter.mp hc).1
    have h := refineAt_recorded r.last (refineAt r.first cs) ⟨c, hc', hp⟩
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · rcases refineAt_recorded r.first cs h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · obtain ⟨c, hc, hp⟩ := hp
    have hc' := (List.mem_filter.mp hc).1
    have h := refineAt_recorded r.last (refineAt r.first cs) ⟨c, hc', hp⟩
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · rcases refineAt_recorded r.first cs h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

def payments : List Component → List Correction → List (List Component)
  | _, [] => []
  | cs, r :: rest => take cs r :: payments (applyCorrection cs r) rest

theorem payments_length (cs : List Component) (records : List Correction) :
    (payments cs records).length = records.length := by
  induction records generalizing cs with
  | nil => rfl
  | cons r rest ih => simp only [payments, List.length_cons, ih]

theorem payments_domain_subset (cs : List Component) (records : List Correction)
    (out : List Component) (hout : out ∈ payments cs records) : domain out ⊆ domain cs := by
  induction records generalizing cs with
  | nil => simp [payments] at hout
  | cons r rest ih =>
    rcases List.mem_cons.mp hout with h | h
    · subst out
      exact take_subset cs r
    · have hs : domain (applyCorrection cs r) ⊆ domain cs := by
        change domain (removeCorrection cs r.amount r.start r.first r.last) ⊆ _
        rw [removeCorrection_domain]
        exact sdiff_subset
      exact (ih _ h).trans hs

/-- All physically reconstructed correction outputs are literally disjoint. -/
theorem payments_disjoint (cs : List Component) (records : List Correction) :
    (payments cs records).Pairwise (fun a b => Disjoint (domain a) (domain b)) := by
  induction records generalizing cs with
  | nil => simp [payments]
  | cons r rest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih _⟩
    intro out hout
    exact (take_remaining_disjoint cs r).mono_right
      (payments_domain_subset (applyCorrection cs r) rest out hout)

/-- Each correction output keeps all cache endpoints within the original
recorded boundary set and the actual two-endpoint records. -/
theorem payments_recorded (cs : List Component) (records : List Correction)
    (out : List Component) (hout : out ∈ payments cs records) {p : ℝ} (hp : Recorded out p) :
    p ∈ endpoints records ∨ Recorded cs p := by
  induction records generalizing cs with
  | nil => simp [payments] at hout
  | cons r rest ih =>
    rcases List.mem_cons.mp hout with h | h
    · subst out
      rcases take_recorded cs r hp with h | h | h
      · exact Or.inl (by simp [endpoints, h])
      · exact Or.inl (by simp [endpoints, h])
      · exact Or.inr h
    · rcases ih _ h with h | h
      · exact Or.inl (by simp [endpoints] at h ⊢; exact Or.inr (Or.inr h))
      · rcases removeCorrection_recorded cs r.amount r.start r.first r.last h with h | h | h
        · exact Or.inl (by simp [endpoints, h])
        · exact Or.inl (by simp [endpoints, h])
        · exact Or.inr h

theorem remaining_append (cs : List Component) (first last : List Correction) :
    remaining cs (first ++ last) = remaining (remaining cs first) last := by
  induction first generalizing cs with
  | nil => rfl
  | cons r rest ih => exact ih _

theorem payments_append (cs : List Component) (first last : List Correction) :
    payments cs (first ++ last) = payments cs first ++ payments (remaining cs first) last := by
  induction first generalizing cs with
  | nil => rfl
  | cons r rest ih => simp only [List.cons_append, payments, remaining, ih]

theorem payments_flatten_domain (cs : List Component) (records : List Correction) :
    domain (payments cs records).flatten = excluded cs records := by
  induction records generalizing cs with
  | nil => rfl
  | cons r rest ih => rw [payments, List.flatten_cons, domain_append, take_domain, ih]; rfl

def collect (state : List Component × List (List Component)) (r : Correction) :
    List Component × List (List Component) :=
  (applyCorrection state.1 r, state.2 ++ [take state.1 r])

theorem collect_eq (cs : List Component) (output : List (List Component)) (records : List Correction) :
    records.foldl collect (cs, output) = (remaining cs records, output ++ payments cs records) := by
  induction records generalizing cs output with
  | nil => simp [remaining, payments]
  | cons r rest ih =>
    rw [List.foldl_cons]
    change rest.foldl collect (applyCorrection cs r, output ++ [take cs r]) = _
    rw [ih]
    simp [remaining, payments, List.append_assoc]

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem take_measurable (cs : X → List Component) (r : X → Correction)
    (hcs : Measurable cs) (hr : Measurable r) : Measurable (fun z => take (cs z) (r z)) := by
  have ha := correction_amount_measurable.comp hr
  have hs := correction_start_measurable.comp hr
  have hf := correction_first_measurable.comp hr
  have hl := correction_last_measurable.comp hr
  have href := refineAt_measurable _ _ (refineAt_measurable cs _ hcs hf) hl
  have hval := UpperCircular.measurable_value.comp hs
  have hshift := UpperCircular.measurable_value.comp
    (hs.add (UpperCircular.measurable_project.comp ha))
  exact measurable_const.ite (measurableSet_eq_fun ha measurable_const)
    (hcs.ite (measurableSet_eq_fun ha measurable_const)
      ((intervalAtoms_measurable _ _ _ href hf hl).ite (measurableSet_lt hval hshift)
        (outsideAtoms_measurable _ _ _ href hl hf)))

theorem payments_measurable (cs : X → List Component) (records : X → List Correction)
    (hcs : Measurable cs) (hrecords : Measurable records) :
    Measurable (fun z => payments (cs z) (records z)) := by
  have hstep : Measurable (fun p : X × (List Component × List (List Component)) × Correction =>
      collect p.2.1 p.2.2) := by
    exact (applyCorrection_measurable _ _
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
      (measurable_snd.comp measurable_snd)).prodMk
        (ProtocolMeasurable.measurable_list_append.comp
          ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
            (ProtocolMeasurable.measurable_list_singleton.comp
              (take_measurable _ _
                (measurable_fst.comp (measurable_fst.comp measurable_snd))
                (measurable_snd.comp measurable_snd)))))
  have h := measurable_snd.comp (list_foldl_measurable (fun (_ : X) state r => collect state r)
    (fun z => (cs z, [])) records hstep (hcs.prodMk measurable_const) hrecords)
  convert h using 1
  funext z
  simp [collect_eq]

end Measurability

end EnvyFreeResearch.Full.UpperCorrectionPieces
