import EnvyFreeResearch.Full.UpperGridCells
import EnvyFreeResearch.Full.UpperComponentGroups

/-! A literal leftState/complement split of a recorded domain, including every
zero-mass endpoint. The midpoint will be supplied by one actual ordinary Cut. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperBaseCases
open UpperRecordedDomain UpperCorrectionExecution UpperDomainDifference UpperGridCells
open UpperEndpointCache
variable {n : ℕ}

def leftState (state : State n) (point : ℝ) : State n :=
  ⟨prefixAtoms point state.cells, state.history⟩

def rightState (state : State n) (point : ℝ) : State n :=
  ⟨state.cells.filter (fun c => !decide (c.right ≤ point)),state.history⟩

theorem prefix_domain (state : State n) (point : ℝ)
    (hsep : SeparatedAt point state.cells) :
    domain (leftState state point).cells = domain state.cells ∩ Iic point :=
  prefixAtoms_domain state.cells point hsep

theorem suffix_domain (state : State n) (point : ℝ)
    (hdis : DisjointComponents state.cells) :
    domain (rightState state point).cells = domain state.cells \ domain (leftState state point).cells :=
  whole_filter_domain state.cells hdis _

theorem split_disjoint (state : State n) (point : ℝ)
    (hdis : DisjointComponents state.cells) :
    Disjoint (domain (leftState state point).cells) (domain (rightState state point).cells) := by
  rw [suffix_domain state point hdis]
  exact disjoint_sdiff_self_right

theorem split_complete (state : State n) (point : ℝ)
    (hdis : DisjointComponents state.cells) (hsep : SeparatedAt point state.cells) :
    domain (leftState state point).cells ∪ domain (rightState state point).cells = domain state.cells := by
  rw [suffix_domain state point hdis, prefix_domain state point hsep]
  exact union_sdiff_cancel inter_subset_left

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem filter_wellFormed (state : State n) (hgood : WellFormed μ state)
    (keep : Component → Bool) :
    WellFormed μ (⟨state.cells.filter keep,state.history⟩ : State n) := by
  refine ⟨hgood.1.filter _,hgood.2.1.filter _,hgood.2.2.1,?_⟩
  intro i p hp
  exact hgood.2.2.2 i p (filter_recorded state.cells keep hp)

theorem prefix_wellFormed (state : State n) (hgood : WellFormed μ state) (point : ℝ) :
    WellFormed μ (leftState state point) := filter_wellFormed μ state hgood _

theorem suffix_wellFormed (state : State n) (hgood : WellFormed μ state) (point : ℝ) :
    WellFormed μ (rightState state point) := filter_wellFormed μ state hgood _

theorem split_mass (state : State n) (hgood : WellFormed μ state) (point : ℝ)
    (hsep : SeparatedAt point state.cells) (i : Fin n) :
    (μ i).real (domain (leftState state point).cells) +
      (μ i).real (domain (rightState state point).cells) = (μ i).real (domain state.cells) := by
  rw [← measureReal_union (split_disjoint state point hgood.2.1)
    (domain_measurable (rightState state point).cells),split_complete state point hgood.2.1 hsep]

end EnvyFreeResearch.Full.UpperBaseCases
