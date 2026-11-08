import EnvyFreeResearch.Full.UpperComponentJoin

/-! Finite recorded piece assembly preserves literal material, cached
endpoint provenance, and the complete current history. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperComponentAssembly

open UpperRecordedDomain UpperCorrectionExecution UpperEndpointCache UpperCircularStage ProtocolMeasurable

variable {n r : ℕ}

def familyComponents (pieces : Fin r → State n) : List Component :=
  (List.ofFn (fun j => (pieces j).cells)).flatten

def family (pieces : Fin r → State n) (history : History n) : State n :=
  state (familyComponents pieces) history

theorem familyComponents_domain (pieces : Fin r → State n) :
    domain (familyComponents pieces) = ⋃ j, domain (pieces j).cells := by
  ext x
  simp only [mem_domain, familyComponents, List.mem_flatten, List.mem_ofFn, mem_iUnion]
  constructor
  · rintro ⟨c, ⟨cs, ⟨j, rfl⟩, hc⟩, hx⟩
    exact ⟨j, c, hc, hx⟩
  · rintro ⟨j, c, hc, hx⟩
    exact ⟨c, ⟨(pieces j).cells, ⟨j, rfl⟩, hc⟩, hx⟩

theorem family_domain (pieces : Fin r → State n) (history : History n) :
    domain (family pieces history).cells = ⋃ j, domain (pieces j).cells :=
  (assemble_domain _).trans (familyComponents_domain pieces)

theorem familyComponents_disjoint (pieces : Fin r → State n)
    (hpieces : ∀ j, DisjointComponents (pieces j).cells)
    (hpair : Pairwise (fun i j => Disjoint (domain (pieces i).cells) (domain (pieces j).cells))) :
    DisjointComponents (familyComponents pieces) := by
  induction r with
  | zero => simp [familyComponents, DisjointComponents]
  | succ r ih =>
    rw [familyComponents, List.ofFn_succ, List.flatten_cons]
    apply append_disjoint
    · exact hpieces 0
    · exact ih _ (fun j => hpieces j.succ) (fun i j hij => hpair (by simpa using hij))
    · change Disjoint (domain (pieces 0).cells) (domain (familyComponents (fun j => pieces j.succ)))
      rw [familyComponents_domain]
      exact disjoint_iUnion_right.mpr (fun j => hpair (Fin.succ_ne_zero j).symm)

theorem familyComponents_recorded (pieces : Fin r → State n) (history : History n)
    (hpieces : ∀ j, RecordedHistory (pieces j).cells history) :
    RecordedHistory (familyComponents pieces) history := by
  intro i p hp
  obtain ⟨c, hc, he⟩ := hp
  obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hcs
  exact hpieces j i p ⟨c, hc, he⟩

theorem family_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (pieces : Fin r → State n) (history : History n)
    (hpieces : ∀ j, WellFormed μ (pieces j))
    (hpair : Pairwise (fun i j => Disjoint (domain (pieces i).cells) (domain (pieces j).cells)))
    (htruth : Truthful μ history) (hhistory : ∀ j, (pieces j).history ⊆ history) :
    WellFormed μ (family pieces history) :=
  state_wellFormed μ _ history
    (familyComponents_disjoint pieces (fun j => (hpieces j).2.1) hpair) htruth
    (familyComponents_recorded pieces history (fun j =>
      recordedHistory_mono _ (hpieces j).2.2.2 (hhistory j)))

theorem familyComponents_measurable {X : Type} [MeasurableSpace X] (pieces : X → Fin r → State n)
    (hpieces : ∀ j, Measurable (fun x => pieces x j)) :
    Measurable (fun x => familyComponents (pieces x)) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    have htail := ih (fun x j => pieces x j.succ) (fun j => hpieces j.succ)
    simpa only [familyComponents, List.ofFn_succ, List.flatten_cons, Function.comp_def] using
      measurable_list_append.comp ((state_cells_measurable.comp (hpieces 0)).prodMk htail)

theorem family_measurable {X : Type} [MeasurableSpace X] (pieces : X → Fin r → State n)
    (history : X → History n) (hpieces : ∀ j, Measurable (fun x => pieces x j))
    (hhistory : Measurable history) : Measurable (fun x => family (pieces x) (history x)) :=
  state_measurable.comp ((familyComponents_measurable pieces hpieces).prodMk hhistory)

end EnvyFreeResearch.Full.UpperComponentAssembly
