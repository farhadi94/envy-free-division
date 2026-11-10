import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalInvariant

/-! Whole-label preservation for an already executed output. Only the
actual output caches must be well formed; addition caches need not be
reconstructed merely to prove semantic conservation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution
variable {n : ℕ}

def received (a : Anchor n) (output : Fin n → State n) (remaining : State n) : Anchor n :=
  ⟨output,remaining,a.active⟩

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n)
  (ha : a.Physical μ whole) (output addition : Fin n → State n) (remaining : State n)
  (f : Equiv.Perm (Fin n))
  (hlabel : ∀ j, domain (output (f j)).cells = domain (a.bundles j).cells ∪ domain (addition j).cells)
  (hpair : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
  (hsep : ∀ j, Disjoint (domain (addition j).cells) (domain remaining.cells))
  (hcover : (⋃ j, domain (addition j).cells) ∪ domain remaining.cells = domain a.residue.cells)
include ha hlabel hpair hsep hcover

theorem received_physical (hout : ∀ j, WellFormed μ (output j)) (hr : WellFormed μ remaining) :
    (received a output remaining).Physical μ whole := by
  have hsub (j : Fin n) : domain (addition j).cells ⊆ domain a.residue.cells := by
    rw [← hcover]
    exact (subset_iUnion (fun j => domain (addition j).cells) j).trans subset_union_left
  have hrs : domain remaining.cells ⊆ domain a.residue.cells := by
    rw [← hcover]
    exact subset_union_right
  have hcross (i j : Fin n) := (ha.separate i).mono_right (hsub j)
  have hdom (j : Fin n) : domain (output j).cells =
      domain (transport a.bundles addition f remaining.history j).cells := by
    obtain ⟨j,rfl⟩ := f.surjective j
    rw [hlabel,transport_domain]
  refine ⟨hout,hr,?_,?_,?_⟩
  · intro i j hij
    change Disjoint (domain (output i).cells) (domain (output j).cells)
    rw [hdom,hdom]
    exact transport_pairwise a.bundles addition f remaining.history ha.pairwise hpair hcross hij
  · intro j
    change Disjoint (domain (output j).cells) (domain remaining.cells)
    obtain ⟨j,rfl⟩ := f.surjective j
    rw [hlabel]
    exact disjoint_union_left.mpr ⟨(ha.separate _).mono_right hrs,hsep _⟩
  · change (⋃ j, domain (output j).cells) ∪ domain remaining.cells = whole
    simp_rw [hdom]
    rw [transport_union,union_assoc,hcover,ha.cover]

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
