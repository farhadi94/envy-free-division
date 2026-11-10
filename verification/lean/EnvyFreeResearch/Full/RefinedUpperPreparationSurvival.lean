import EnvyFreeResearch.Full.RefinedUpperPreparationRetained
import EnvyFreeResearch.Full.RefinedUpperStabilityParents

/-! Membership in the actual retained buffer forces survival of the enclosing
coarse parent. Permanent coarse endpoints form a finite exceptional set. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRecordedQuantiles UpperLogicalCells RefinedUpperPeeling Chores
open scoped Classical unitInterval

lemma cell_mem_interval_of_not_endpoint {a : ℕ} (buffer : Set ℝ) (coarse : Fin (a+2) → ℝ)
    (p : Fin (a+1)) (t : ℝ) (ht : t ∈ cell buffer coarse p)
    (hzero : t ≠ coarse 0) : coarse p.castSucc < t ∧ t ≤ coarse p.succ := by
  rcases ht with ht | ht
  · exact ht.2
  · split_ifs at ht with hp
    · exact False.elim (hzero ht.2)
    · exact False.elim ht

/-- A positive-length enclosing cell has a unique parent; if its interior
point is retained, that parent was not removed. -/
lemma retained_union_parent_survives {a : ℕ} (buffer : Set ℝ)
    (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse)
    (removed : Finset (Fin (a+1))) (l t r : ℝ) (hlt : l < t) (htr : t < r)
    (hfit : intervalFits coarse (l,r) (intervalParent coarse (l,r)))
    (ht : t ∈ ⋃ p, if p ∉ removed then cell buffer coarse p else ∅)
    (hzero : t ≠ coarse 0) : intervalParent coarse (l,r) ∉ removed := by
  obtain ⟨p,hp⟩ := mem_iUnion.mp ht
  by_cases hpr : p ∈ removed
  · simp [hpr] at hp
  · have hm : t ∈ cell buffer coarse p := by simpa [hpr] using hp
    have hi := cell_mem_interval_of_not_endpoint buffer coarse p t hm hzero
    have he : intervalParent coarse (l,r) = p := by
      by_contra hne
      have hd := consecutive_disjoint coarse hc hne
      exact Set.disjoint_left.mp hd ⟨hfit.1.trans_lt hlt,htr.le.trans hfit.2⟩ hi
    simpa [he] using hpr

variable {n : ℕ} {Agent : Type*} [Fintype Agent]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem retainedState_parent_survives (q m : ℕ) (draw : Fin m → Agent × I)
    (removed : Finset (Fin (count (Agent := Agent) q + 1))) (l t r : ℝ)
    (hlt : l < t) (htr : t < r)
    (hfit : intervalFits (cuts policy active origin q) (l,r)
      (intervalParent (cuts policy active origin q) (l,r)))
    (ht : t ∈ domain (retainedState policy active origin q m draw removed).cells)
    (hzero : t ≠ cuts policy active origin q 0) :
    intervalParent (cuts policy active origin q) (l,r) ∉ removed := by
  rw [retainedState_domain μ policy hpolicy active origin hgood hpositive] at ht
  exact retained_union_parent_survives (domain origin.cells) (cuts policy active origin q)
    (UpperCommonGrid.grid_monotone _) removed l t r hlt htr hfit ht hzero

end EnvyFreeResearch.Full.RefinedUpperPreparation
