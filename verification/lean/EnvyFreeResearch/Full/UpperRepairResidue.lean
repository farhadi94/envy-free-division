import EnvyFreeResearch.Full.UpperComponentJoin
import EnvyFreeResearch.Full.UpperLogicalPreparationSeedState

/-! Pure reconstruction of the complete Repair buffer after seed removal
and reserve corrections. The material outside the reserve is retained. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperRepairResidue

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperEndpointCache
  UpperCircularStage UpperLogicalPreparation UpperLogicalCells UpperComponentAssembly

variable {n m : ℕ} {Job : Type} [Fintype Job]

def excluded (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1))) :
    Option Job → Finset (Fin (m + 1))
  | none => reserved
  | some j => seeds j

def outside (origin : State n) (cuts : Fin (m + 2) → ℝ)
    (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1))) : State n :=
  UpperPendingExclusion.remove origin cuts (excluded reserved seeds)

def finish (origin : State n) (cuts : Fin (m + 2) → ℝ)
    (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1)))
    (final : State n) : State n :=
  join (outside origin cuts reserved seeds) final final.history

theorem excluded_union (cells : Fin (m + 1) → Set ℝ) (reserved : Finset (Fin (m + 1)))
    (seeds : Job → Finset (Fin (m + 1))) :
    (⋃ j, UpperWholePaymentsPhysical.piece cells (excluded reserved seeds) j) =
      selectedUnion cells reserved ∪ ⋃ j, selectedUnion cells (seeds j) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hx⟩ := mem_iUnion.mp hx
    cases j with
    | none => exact Or.inl hx
    | some j => exact Or.inr (mem_iUnion.mpr ⟨j, hx⟩)
  · rintro (hx | hx)
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some j, hx⟩

theorem outside_domain (origin : State n) (cuts : Fin (m + 2) → ℝ)
    (hdis : DisjointComponents origin.cells) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1))) :
    domain (outside origin cuts reserved seeds).cells = domain origin.cells \
      (selectedUnion (cell (domain origin.cells) cuts) reserved ∪
        ⋃ j, selectedUnion (cell (domain origin.cells) cuts) (seeds j)) := by
  rw [outside, UpperPendingExclusion.remove_domain origin hdis cuts hzero hmono hsep, excluded_union]

theorem outside_history (origin : State n) (cuts : Fin (m + 2) → ℝ)
    (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1))) :
    (outside origin cuts reserved seeds).history = origin.history := rfl

theorem finish_history (origin : State n) (cuts : Fin (m + 2) → ℝ)
    (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1))) (final : State n) :
    (finish origin cuts reserved seeds final).history = final.history := rfl

theorem finish_domain (origin : State n) (cuts : Fin (m + 2) → ℝ)
    (hdis : DisjointComponents origin.cells) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1)))
    (final : State n) (payment : Set ℝ)
    (hfinal : domain final.cells = selectedUnion (cell (domain origin.cells) cuts) reserved \ payment)
    (hseeds : Disjoint (⋃ j, selectedUnion (cell (domain origin.cells) cuts) (seeds j))
      (selectedUnion (cell (domain origin.cells) cuts) reserved))
    (hpayment : payment ⊆ selectedUnion (cell (domain origin.cells) cuts) reserved) :
    domain (finish origin cuts reserved seeds final).cells = domain origin.cells \
      ((⋃ j, selectedUnion (cell (domain origin.cells) cuts) (seeds j)) ∪ payment) := by
  apply full_residue_domain _ _ _ _ _ _ _
    (outside_domain origin cuts hdis hzero hmono hsep reserved seeds) hfinal _ hseeds hpayment
  intro x hx
  obtain ⟨e, _, he⟩ := (mem_selectedUnion _ _ x).mp hx
  exact (cell_subset _ _ _) he

theorem finish_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)]
    (origin : State n) (hgood : WellFormed μ origin) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (reserved : Finset (Fin (m + 1))) (seeds : Job → Finset (Fin (m + 1)))
    (final : State n) (hfinalGood : WellFormed μ final) (payment : Set ℝ)
    (hfinal : domain final.cells = selectedUnion (cell (domain origin.cells) cuts) reserved \ payment)
    (hhistory : origin.history ⊆ final.history) : WellFormed μ (finish origin cuts reserved seeds final) := by
  have hout := UpperPendingExclusion.remove_wellFormed μ origin hgood cuts (excluded reserved seeds)
  have hd := outside_final_disjoint (outside origin cuts reserved seeds) final _ _ _ _
    (outside_domain origin cuts hgood.2.1 hzero hmono hsep reserved seeds) hfinal
  exact join_wellFormed μ _ _ _ hout hfinalGood hd hfinalGood.2.2.1 hhistory Subset.rfl

theorem finish_measurable {X : Type} [MeasurableSpace X]
    (origin : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (reserved : X → Finset (Fin (m + 1))) (seeds : X → Job → Finset (Fin (m + 1)))
    (final : X → State n) (horigin : Measurable origin)
    (hcuts : ∀ e, Measurable (fun x => cuts x e)) (hreserved : Measurable reserved)
    (hseeds : ∀ j, Measurable (fun x => seeds x j)) (hfinal : Measurable final) :
    Measurable (fun x => finish (origin x) (cuts x) (reserved x) (seeds x) (final x)) := by
  have hout : Measurable (fun x => outside (origin x) (cuts x) (reserved x) (seeds x)) := by
    apply UpperPendingExclusion.remove_measurable _ _ _ horigin hcuts
    intro j
    cases j with
    | none => exact hreserved
    | some j => exact hseeds j
  exact join_measurable _ final (fun x => (final x).history) hout hfinal (state_history_measurable.comp hfinal)

end EnvyFreeResearch.Full.UpperRepairResidue
