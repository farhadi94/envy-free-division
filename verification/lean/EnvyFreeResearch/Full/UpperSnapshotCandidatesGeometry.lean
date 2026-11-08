import EnvyFreeResearch.Full.UpperSnapshotCandidatesGuard

/-! Literal large-disagreement candidates are filtered from recorded atoms.
Their full complement and all old endpoints are retained without new queries. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperRecordedDomain UpperCorrectionExecution UpperLogicalPreparation UpperLogicalCells UpperDomainDifference
variable {n k m : ℕ}

def cellState (state : State n) (cuts : Fin (m + 2) → ℝ) (e : Fin (m + 1)) : State n :=
  retain state cuts {e}

def largeEndowment (state : State n) (cuts : Fin (m + 2) → ℝ) (F G : Fin (m + 1)) (j : Fin k) : State n :=
  if j.val = 0 then cellState state cuts F else if j.val = 1 then cellState state cuts G else retain state cuts ∅

def largeBuffer (state : State n) (cuts : Fin (m + 2) → ℝ) (F G : Fin (m + 1)) : State n :=
  retain state cuts (Finset.univ \ {F, G})

theorem cellState_domain (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells) (e : Fin (m + 1)) :
    domain (cellState state cuts e).cells = cell (domain state.cells) cuts e := by
  rw [cellState, retain_domain state cuts hzero hmono hsep]
  ext x
  simp only [mem_selectedUnion, Finset.mem_singleton, exists_eq_left]

theorem retain_empty_domain (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells) :
    domain (retain state cuts ∅).cells = ∅ := by
  rw [retain_domain state cuts hzero hmono hsep]
  ext x
  simp only [mem_selectedUnion, Finset.notMem_empty, false_and, exists_false, mem_empty_iff_false]

theorem largeEndowment_domain (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (F G : Fin (m + 1)) (j : Fin k) :
    domain (largeEndowment state cuts F G j).cells =
      if j.val = 0 then cell (domain state.cells) cuts F else if j.val = 1 then cell (domain state.cells) cuts G else ∅ := by
  unfold largeEndowment
  split_ifs
  · exact cellState_domain state cuts hzero hmono hsep F
  · exact cellState_domain state cuts hzero hmono hsep G
  · exact retain_empty_domain state cuts hzero hmono hsep

/-- Filtering the complementary logical indices preserves the literal full
complement, including all endpoints owned by the original component list. -/
theorem selected_complement_pair {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (cells : Cell → Set ℝ) (buffer : Set ℝ) (hcover : (⋃ e, cells e) = buffer)
    (hdisjoint : Pairwise (fun e f => Disjoint (cells e) (cells f))) (F G : Cell) :
    selectedUnion cells (Finset.univ \ {F, G}) = buffer \ (cells F ∪ cells G) := by
  ext x
  rw [mem_selectedUnion]
  constructor
  · rintro ⟨e, he, hx⟩
    have hne : e ≠ F ∧ e ≠ G := by simpa using he
    refine ⟨?_, ?_⟩
    · rw [← hcover]
      exact mem_iUnion.mpr ⟨e, hx⟩
    · rintro (hf | hg)
      · exact Set.disjoint_left.mp (hdisjoint hne.1) hx hf
      · exact Set.disjoint_left.mp (hdisjoint hne.2) hx hg
  · rintro ⟨hx, hnot⟩
    rw [← hcover] at hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    refine ⟨e, ?_, he⟩
    have hf : e ≠ F := by intro heq; subst e; exact hnot (Or.inl he)
    have hg : e ≠ G := by intro heq; subst e; exact hnot (Or.inr he)
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, hf, hg, or_self, not_false_eq_true, and_self]

theorem largeBuffer_domain (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
    (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells) (F G : Fin (m + 1)) :
    domain (largeBuffer state cuts F G).cells = domain state.cells \ (cell (domain state.cells) cuts F ∪ cell (domain state.cells) cuts G) := by
  rw [largeBuffer, retain_domain state cuts hzero hmono hsep]
  exact selected_complement_pair _ _ (cells_cover _ cuts hmono (by rw [hzero, hone]; exact domain_subset_unit state.cells))
    (cells_disjoint _ cuts hmono) F G

theorem largeEndowment_history (state : State n) (cuts : Fin (m + 2) → ℝ) (F G : Fin (m + 1)) (j : Fin k) :
    (largeEndowment state cuts F G j).history = state.history := by
  unfold largeEndowment
  split_ifs <;> rfl

theorem largeBuffer_history (state : State n) (cuts : Fin (m + 2) → ℝ) (F G : Fin (m + 1)) :
    (largeBuffer state cuts F G).history = state.history := rfl

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem largeEndowment_wellFormed (state : State n) (hstate : WellFormed μ state)
    (cuts : Fin (m + 2) → ℝ) (F G : Fin (m + 1)) (j : Fin k) :
    WellFormed μ (largeEndowment state cuts F G j) := by
  unfold largeEndowment cellState
  split_ifs <;> exact retain_wellFormed μ state hstate cuts _

theorem largeBuffer_wellFormed (state : State n) (hstate : WellFormed μ state)
    (cuts : Fin (m + 2) → ℝ) (F G : Fin (m + 1)) :
    WellFormed μ (largeBuffer state cuts F G) := retain_wellFormed μ state hstate cuts _

variable {X : Type*} [MeasurableSpace X]

theorem cellState_measurable (state : X → State n) (cuts : X → Fin (m + 2) → ℝ) (e : X → Fin (m + 1))
    (hstate : Measurable state) (hcuts : ∀ j, Measurable (fun x => cuts x j)) (he : Measurable e) :
    Measurable (fun x => cellState (state x) (cuts x) (e x)) :=
  retain_measurable state cuts (fun x => {e x}) hstate hcuts
    ((measurable_of_countable (fun j : Fin (m + 1) => ({j} : Finset (Fin (m + 1))))).comp he)

theorem largeEndowment_measurable (state : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (F G : X → Fin (m + 1)) (hstate : Measurable state) (hcuts : ∀ j, Measurable (fun x => cuts x j))
    (hF : Measurable F) (hG : Measurable G) (j : Fin k) :
    Measurable (fun x => largeEndowment (state x) (cuts x) (F x) (G x) j) := by
  unfold largeEndowment
  split_ifs
  · exact cellState_measurable state cuts F hstate hcuts hF
  · exact cellState_measurable state cuts G hstate hcuts hG
  · exact retain_measurable state cuts (fun _ => ∅) hstate hcuts measurable_const

theorem largeBuffer_measurable (state : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (F G : X → Fin (m + 1)) (hstate : Measurable state) (hcuts : ∀ j, Measurable (fun x => cuts x j))
    (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun x => largeBuffer (state x) (cuts x) (F x) (G x)) :=
  retain_measurable state cuts (fun x => Finset.univ \ {F x, G x}) hstate hcuts
    ((measurable_of_countable (fun p : Fin (m + 1) × Fin (m + 1) => (Finset.univ \ {p.1, p.2}))).comp (hF.prodMk hG))

end EnvyFreeResearch.Full.UpperSnapshotCandidates
