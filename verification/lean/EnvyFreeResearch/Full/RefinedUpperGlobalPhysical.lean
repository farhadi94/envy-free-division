import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.UpperComponentJoin
import EnvyFreeResearch.GlobalCompletion

/-! Literal recorded anchors and physical whole-bundle transport. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly

structure Anchor (n : ℕ) where
  bundles : Fin n → State n
  residue : State n
  active : Finset (Fin n)

variable {n : ℕ}

def value (μ : Fin n → Measure ℝ) (bundles : Fin n → State n) : GlobalCompletion.Table (Fin n) :=
  fun i j => (μ i).real (domain (bundles j).cells)

def Anchor.table (μ : Fin n → Measure ℝ) (a : Anchor n) : GlobalCompletion.State (Fin n) where
  value := value μ a.bundles
  residue i := (μ i).real (domain a.residue.cells)
  active := a.active

structure Anchor.Physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (a : Anchor n) : Prop where
  bundles_wellFormed : ∀ j, WellFormed μ (a.bundles j)
  residue_wellFormed : WellFormed μ a.residue
  pairwise : Pairwise (fun i j => Disjoint (domain (a.bundles i).cells) (domain (a.bundles j).cells))
  separate : ∀ j, Disjoint (domain (a.bundles j).cells) (domain a.residue.cells)
  cover : (⋃ j, domain (a.bundles j).cells) ∪ domain a.residue.cells = whole

def Anchor.Committed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)]
    (direction : GlobalCompletion.Direction) (whole : Set ℝ) (a : Anchor n) : Prop :=
  a.Physical μ whole ∧ GlobalCompletion.Valid direction (a.table μ)

/-- Computed transport joins whole old labels and recorded additions. -/
def transport (old addition : Fin n → State n) (f : Equiv.Perm (Fin n))
    (history : UpperCircularStage.History n) : Fin n → State n :=
  fun j => join (old (f.symm j)) (addition (f.symm j)) history

theorem transport_domain (old addition : Fin n → State n) (f : Equiv.Perm (Fin n))
    (history : UpperCircularStage.History n) (j : Fin n) :
    domain (transport old addition f history (f j)).cells =
      domain (old j).cells ∪ domain (addition j).cells := by
  simp only [transport, Equiv.symm_apply_apply, join_domain]

theorem transport_value (μ : Measure ℝ) [IsFiniteMeasure μ]
    (old addition : Fin n → State n) (f : Equiv.Perm (Fin n))
    (history : UpperCircularStage.History n)
    (hdis : ∀ j, Disjoint (domain (old j).cells) (domain (addition j).cells)) (j : Fin n) :
    μ.real (domain (transport old addition f history (f j)).cells) =
      μ.real (domain (old j).cells) + μ.real (domain (addition j).cells) := by
  rw [transport_domain]
  exact measureReal_union (hdis j) (domain_measurable _)

theorem partition_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (addition : Fin n → State n) (remaining origin : State n)
    (hpair : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
    (hsep : ∀ j, Disjoint (domain (addition j).cells) (domain remaining.cells))
    (hcover : (⋃ j, domain (addition j).cells) ∪ domain remaining.cells = domain origin.cells) :
    (∑ j, μ.real (domain (addition j).cells)) + μ.real (domain remaining.cells) =
      μ.real (domain origin.cells) := by
  rw [← measureReal_iUnion_fintype hpair (fun j => domain_measurable (addition j).cells),
    ← measureReal_union (disjoint_iUnion_left.mpr hsep) (domain_measurable remaining.cells), hcover]

/-- All-observer finite identities follow from literal disjoint partition. -/
def wholeAddition (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (old addition : Fin n → State n) (remaining origin : State n)
    (active : Set (Fin n)) (f : Equiv.Perm (Fin n)) (history : UpperCircularStage.History n)
    (hfix : ∀ j ∉ active, f j = j)
    (hfrozen : ∀ j ∉ active, domain (addition j).cells = ∅)
    (hdis : ∀ j, Disjoint (domain (old j).cells) (domain (addition j).cells))
    (hpair : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
    (hsep : ∀ j, Disjoint (domain (addition j).cells) (domain remaining.cells))
    (hcover : (⋃ j, domain (addition j).cells) ∪ domain remaining.cells = domain origin.cells) :
    GlobalCompletion.WholeAddition (value μ old) (value μ (transport old addition f history)) active
      (fun i => (μ i).real (domain origin.cells)) (fun i => (μ i).real (domain remaining.cells)) where
  permutation := f
  addition := value μ addition
  addition_nonnegative := fun _ _ => measureReal_nonneg
  fixed := hfix
  frozen_addition := by intro i j hj; simp [value, hfrozen j hj]
  value_identity := fun i j => transport_value (μ i) old addition f history hdis j
  mass_partition := fun i => partition_mass (μ i) addition remaining origin hpair hsep hcover
  remaining_nonnegative := fun _ => measureReal_nonneg

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
