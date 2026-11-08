import EnvyFreeResearch.Full.UpperComponentAssemblyMeasurable

/-! Query-free joining of recorded disjoint states, with explicit complete
history provenance, and literal reconstruction of a full-buffer residue. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperComponentAssembly

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperEndpointCache
  UpperCircularStage ProtocolMeasurable

variable {n : ℕ}

def join (left right : State n) (history : History n) : State n :=
  state (left.cells ++ right.cells) history

theorem join_history (left right : State n) (history : History n) :
    (join left right history).history = history := rfl

theorem join_domain (left right : State n) (history : History n) :
    domain (join left right history).cells = domain left.cells ∪ domain right.cells :=
  (assemble_domain _).trans (domain_append _ _)

theorem append_recorded (cs ds : List Component) (history : History n)
    (hc : RecordedHistory cs history) (hd : RecordedHistory ds history) :
    RecordedHistory (cs ++ ds) history := by
  intro i p hp
  obtain ⟨c, hm, he⟩ := hp
  rcases List.mem_append.mp hm with hm | hm
  · exact hc i p ⟨c, hm, he⟩
  · exact hd i p ⟨c, hm, he⟩

theorem join_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (left right : State n) (history : History n)
    (hl : WellFormed μ left) (hr : WellFormed μ right)
    (hd : Disjoint (domain left.cells) (domain right.cells)) (ht : Truthful μ history)
    (hleft : left.history ⊆ history) (hright : right.history ⊆ history) :
    WellFormed μ (join left right history) :=
  state_wellFormed μ _ history (append_disjoint _ _ hl.2.1 hr.2.1 hd) ht
    (append_recorded _ _ history (recordedHistory_mono _ hl.2.2.2 hleft)
      (recordedHistory_mono _ hr.2.2.2 hright))

theorem join_mass (μ : Measure ℝ) [IsFiniteMeasure μ] (left right : State n) (history : History n)
    (hd : Disjoint (domain left.cells) (domain right.cells)) :
    μ.real (domain (join left right history).cells) = μ.real (domain left.cells) + μ.real (domain right.cells) := by
  rw [join_domain]
  exact measureReal_union hd (domain_measurable right.cells)

theorem join_measurable {X : Type} [MeasurableSpace X]
    (left right : X → State n) (history : X → History n)
    (hl : Measurable left) (hr : Measurable right) (hh : Measurable history) :
    Measurable (fun x => join (left x) (right x) (history x)) :=
  state_measurable.comp ((measurable_list_append.comp
    ((state_cells_measurable.comp hl).prodMk (state_cells_measurable.comp hr))).prodMk hh)

/-- Reserve processing does not discard the original material outside the
reserve. The two actual recorded pieces reconstitute the full complement. -/
theorem full_residue_domain (outside final : State n) (history : History n)
    (buffer reserve seeds payment : Set ℝ)
    (houtside : domain outside.cells = buffer \ (reserve ∪ seeds))
    (hfinal : domain final.cells = reserve \ payment)
    (hreserve : reserve ⊆ buffer) (hseeds : Disjoint seeds reserve) (hpayment : payment ⊆ reserve) :
    domain (join outside final history).cells = buffer \ (seeds ∪ payment) := by
  rw [join_domain, houtside, hfinal]
  ext x
  simp only [mem_union, mem_diff]
  have hd := Set.disjoint_left.mp hseeds
  constructor
  · rintro (⟨hb, hn⟩ | ⟨hr, hp⟩)
    · refine ⟨hb, ?_⟩
      rintro (hs | hp)
      · exact hn (Or.inr hs)
      · exact hn (Or.inl (hpayment hp))
    · exact ⟨hreserve hr, fun h => h.elim (fun hs => hd hs hr) hp⟩
  · rintro ⟨hb, hn⟩
    by_cases hr : x ∈ reserve
    · exact Or.inr ⟨hr, fun hp => hn (Or.inr hp)⟩
    · exact Or.inl ⟨hb, fun h => h.elim hr (fun hs => hn (Or.inl hs))⟩

theorem outside_final_disjoint (outside final : State n)
    (buffer reserve seeds payment : Set ℝ)
    (houtside : domain outside.cells = buffer \ (reserve ∪ seeds))
    (hfinal : domain final.cells = reserve \ payment) :
    Disjoint (domain outside.cells) (domain final.cells) := by
  rw [houtside, hfinal]
  exact Set.disjoint_left.mpr (fun _ ho hf => ho.2 (Or.inl hf.1))

end EnvyFreeResearch.Full.UpperComponentAssembly
