import EnvyFreeResearch.Full.UpperComponentGroups
import EnvyFreeResearch.Full.UpperWholePaymentsPhysical
import EnvyFreeResearch.Full.UpperShrinkCarveRounding
import EnvyFreeResearch.Full.UpperShrinkCarved

/-! Query-free assembly of final integral colors. Fractional cells and the
dummy color remain in the buffer; no null or singleton material is lost. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperComponentAssembly UpperEndpointCache

variable {n r k : ℕ}

def selectedState (pieces : Fin r → State n) (history : History n)
    (selected : Finset (Fin r)) : State n :=
  family (fun e => if e ∈ selected then pieces e else empty history) history

theorem selected_domain (pieces : Fin r → State n) (history : History n)
    (selected : Finset (Fin r)) :
    domain (selectedState pieces history selected).cells =
      UpperWholePaymentsPhysical.piece (fun e => domain (pieces e).cells) (fun _ : Unit => selected) () := by
  rw [selectedState,family_domain]
  apply iUnion_congr
  intro e
  split_ifs <;> rfl

theorem selected_mem (pieces : Fin r → State n) (history : History n)
    (selected : Finset (Fin r)) (z : ℝ) :
    z ∈ domain (selectedState pieces history selected).cells ↔
      ∃ e ∈ selected, z ∈ domain (pieces e).cells := by
  rw [selected_domain]
  exact UpperWholePaymentsPhysical.mem_piece _ _ () z

theorem selected_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (pieces : Fin r → State n) (history : History n)
    (selected : Finset (Fin r)) (hpieces : ∀ e, WellFormed μ (pieces e))
    (hpair : Pairwise (fun e f => Disjoint (domain (pieces e).cells) (domain (pieces f).cells)))
    (htruth : Truthful μ history) (hhistory : ∀ e, (pieces e).history ⊆ history) :
    WellFormed μ (selectedState pieces history selected) := by
  apply family_wellFormed μ _ history
  · intro e
    split_ifs
    · exact hpieces e
    · exact empty_wellFormed μ history htruth
  · intro e f hef
    split_ifs <;> first | exact hpair hef | simp [empty,domain]
  · exact htruth
  · intro e
    split_ifs
    · exact hhistory e
    · exact Subset.rfl

theorem selected_disjoint (pieces : Fin r → State n) (history : History n)
    (hpair : Pairwise (fun e f => Disjoint (domain (pieces e).cells) (domain (pieces f).cells)))
    (a b : Finset (Fin r)) (hab : Disjoint a b) :
    Disjoint (domain (selectedState pieces history a).cells)
      (domain (selectedState pieces history b).cells) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  obtain ⟨e,he,hze⟩ := (selected_mem pieces history a z).mp hza
  obtain ⟨f,hf,hzf⟩ := (selected_mem pieces history b z).mp hzb
  have hef : e ≠ f := by
    intro h
    subst f
    exact Finset.disjoint_left.mp hab he hf
  exact Set.disjoint_left.mp (hpair hef) hze hzf

theorem selected_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (pieces : Fin r → State n) (history : History n) (selected : Finset (Fin r))
    (hpair : Pairwise (fun e f => Disjoint (domain (pieces e).cells) (domain (pieces f).cells))) :
    μ.real (domain (selectedState pieces history selected).cells) =
      ∑ e ∈ selected, μ.real (domain (pieces e).cells) := by
  rw [selected_domain]
  exact UpperWholePaymentsPhysical.piece_mass μ _ (fun e => domain_measurable _) hpair _ ()

def dummyCells (x : Fin r → Option (Fin k) → ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun e => ∀ j, x e (some j) ≠ 1)

def assembledCarve (pieces : Fin r → State n) (history : History n)
    (x : Fin r → Option (Fin k) → ℝ) : UpperShrink.Carved n k where
  old j := selectedState pieces history (UpperWholePayments.integralCells x j)
  buffer := selectedState pieces history (dummyCells x)

theorem integral_dummy_disjoint (x : Fin r → Option (Fin k) → ℝ) (j : Fin k) :
    Disjoint (UpperWholePayments.integralCells x j) (dummyCells x) := by
  apply Finset.disjoint_left.mpr
  intro e he hd
  exact (Finset.mem_filter.mp hd).2 j (Finset.mem_filter.mp he).2

theorem assembled_material (pieces : Fin r → State n) (history : History n)
    (x : Fin r → Option (Fin k) → ℝ) :
    (⋃ j, domain ((assembledCarve pieces history x).old j).cells) ∪
      domain (assembledCarve pieces history x).buffer.cells = ⋃ e, domain (pieces e).cells := by
  ext z
  simp only [mem_union,mem_iUnion,assembledCarve,selected_mem]
  constructor
  · rintro (⟨j,e,_,he⟩ | ⟨e,_,he⟩) <;> exact ⟨e,he⟩
  · rintro ⟨e,he⟩
    by_cases hex : ∃ j, x e (some j)=1
    · obtain ⟨j,hj⟩ := hex
      exact Or.inl ⟨j,e,by simp [UpperWholePayments.integralCells,hj],he⟩
    · exact Or.inr ⟨e,by simpa [dummyCells] using hex,he⟩

end EnvyFreeResearch.Full.UpperShrinkCarve
