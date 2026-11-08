import FixedPointTheorems.kakutani
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic

/-!
# The proved Kakutani application for hungry Core local matching

The pinned MIT-licensed `FixedPointTheorems` dependency supplies the proved
finite-dimensional fixed-point theorem. Its upstream commit and axiom audit
are recorded in `formalization/notes/chores-gap-map.md`.

We use a simplex of increments together with all agents' probability rows.
Keeping the rows in the fixed-point space avoids projecting an existential
probability matrix through the column-demand correspondence. Every graph,
convexity and nonemptiness condition below is proved from finite continuous
cost functions and the permitted diagonal.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.FixedPoint

open Set
open scoped BigOperators

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]

def simplex : Set (Agent → ℝ) := {y | (∀ j, 0 ≤ y j) ∧ ∑ j, y j = 1}

def domain : Set ((Agent → ℝ) × (Agent → Agent → ℝ)) :=
  {z | z.1 ∈ (simplex : Set (Agent → ℝ)) ∧ ∀ i, z.2 i ∈ simplex}

def columnSum (r : Agent → Agent → ℝ) (j : Agent) : ℝ := ∑ i, r i j

def supportedMinima (cost : Agent → Agent → ℝ → ℝ)
    (permitted : Agent → Agent → Prop) (y : Agent → ℝ) (r : Agent → Agent → ℝ) : Prop :=
  ∀ i j, r i j = 0 ∨ (permitted i j ∧ ∀ k, permitted i k → cost i j (y j) ≤ cost i k (y k))

def response (cost : Agent → Agent → ℝ → ℝ) (permitted : Agent → Agent → Prop)
    (x : (domain : Set ((Agent → ℝ) × (Agent → Agent → ℝ)))) :
    Set ((Agent → ℝ) × (Agent → Agent → ℝ)) :=
  {z | z ∈ domain ∧
    (∀ w ∈ simplex, ∑ j, w j * columnSum x.1.2 j ≤ ∑ j, z.1 j * columnSum x.1.2 j) ∧
    supportedMinima cost permitted x.1.1 z.2}

lemma simplex_compact : IsCompact (simplex : Set (Agent → ℝ)) :=
  isCompact_stdSimplex ℝ Agent

lemma simplex_convex : Convex ℝ (simplex : Set (Agent → ℝ)) :=
  convex_stdSimplex ℝ Agent

lemma single_mem_simplex (i : Agent) : Pi.single i (1 : ℝ) ∈ (simplex : Set (Agent → ℝ)) :=
  single_mem_stdSimplex ℝ i

lemma domain_compact : IsCompact (domain : Set ((Agent → ℝ) × (Agent → Agent → ℝ))) :=
  simplex_compact.prod (isCompact_pi_infinite (fun _ : Agent => simplex_compact))

lemma domain_convex : Convex ℝ (domain : Set ((Agent → ℝ) × (Agent → Agent → ℝ))) := by
  intro x hx y hy a b ha hb hab
  refine ⟨simplex_convex hx.1 hy.1 ha hb hab, ?_⟩
  intro i
  exact simplex_convex (hx.2 i) (hy.2 i) ha hb hab

lemma domain_nonempty : (domain : Set ((Agent → ℝ) × (Agent → Agent → ℝ))).Nonempty := by
  inhabit Agent
  exact ⟨(Pi.single default 1, fun i => Pi.single i 1), single_mem_simplex _, fun i => single_mem_simplex i⟩

lemma closed_forall {X : Type*} [TopologicalSpace X] {Index : Sort*}
    (P : Index → X → Prop) (h : ∀ i, IsClosed {x | P i x}) : IsClosed {x | ∀ i, P i x} := by
  simpa only [ofPred_forall] using isClosed_iInter h

/-- The graph is closed directly on the probability-row state space. -/
lemma response_closedGraph (cost : Agent → Agent → ℝ → ℝ)
    (hcontinuous : ∀ i j, Continuous (cost i j)) (permitted : Agent → Agent → Prop) :
    closedGraph (response cost permitted) := by
  classical
  unfold closedGraph response
  apply IsClosed.inter (domain_compact.isClosed.preimage continuous_snd)
  apply IsClosed.inter
  · apply closed_forall
    intro w
    apply closed_forall
    intro _
    exact isClosed_le (by unfold columnSum; fun_prop) (by unfold columnSum; fun_prop)
  · apply closed_forall
    intro i
    apply closed_forall
    intro j
    apply IsClosed.union (isClosed_eq (by fun_prop) continuous_const)
    by_cases hp : permitted i j
    · simp only [hp, true_and]
      apply closed_forall
      intro k
      apply closed_forall
      intro _
      exact isClosed_le ((hcontinuous i j).comp (by fun_prop))
        ((hcontinuous i k).comp (by fun_prop))
    · simp only [hp, false_and]
      exact isClosed_empty

/-- Every response set is convex; support constraints are fixed at the input. -/
lemma response_convex (cost : Agent → Agent → ℝ → ℝ) (permitted : Agent → Agent → Prop)
    (x : (domain : Set ((Agent → ℝ) × (Agent → Agent → ℝ)))) :
    Convex ℝ (response cost permitted x) := by
  intro u hu v hv a b ha hb hab
  refine ⟨domain_convex hu.1 hv.1 ha hb hab, ?_, ?_⟩
  · intro w hw
    change (∑ j, w j * columnSum x.1.2 j) ≤
      ∑ j, (a * u.1 j + b * v.1 j) * columnSum x.1.2 j
    simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hu.2.1 w hw) ha
    have h2 := mul_le_mul_of_nonneg_left (hv.2.1 w hw) hb
    calc
      _ = (a + b) * (∑ j, w j * columnSum x.1.2 j) := by rw [hab, one_mul]
      _ = a * (∑ j, w j * columnSum x.1.2 j) + b * (∑ j, w j * columnSum x.1.2 j) := by ring
      _ ≤ _ := add_le_add h1 h2
  · intro i j
    by_cases hu0 : u.2 i j = 0
    · by_cases hv0 : v.2 i j = 0
      · left
        change a * u.2 i j + b * v.2 i j = 0
        rw [hu0, hv0]
        ring
      · right
        exact (hv.2.2 i j).resolve_left hv0
    · right
      exact (hu.2.2 i j).resolve_left hu0

/-- Allowed diagonal pairs make every row's permitted minimizer set nonempty. -/
lemma exists_permitted_minimizer (cost : Agent → Agent → ℝ → ℝ)
    (permitted : Agent → Agent → Prop) (hdiag : ∀ i, permitted i i) (y : Agent → ℝ) :
    ∀ i, ∃ j, permitted i j ∧ ∀ k, permitted i k → cost i j (y j) ≤ cost i k (y k) := by
  classical
  intro i
  let allowed := Finset.univ.filter (permitted i)
  have hne : allowed.Nonempty := ⟨i, by simp [allowed, hdiag i]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image allowed (fun j => cost i j (y j)) hne
  refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
  intro k hk
  exact hmin k (by simp [allowed, hk])

/-- A maximizing vertex and one permitted minimizer in every row give an
explicit member of every response set. -/
lemma response_nonempty (cost : Agent → Agent → ℝ → ℝ)
    (permitted : Agent → Agent → Prop) (hdiag : ∀ i, permitted i i)
    (x : (domain : Set ((Agent → ℝ) × (Agent → Agent → ℝ)))) :
    (response cost permitted x).Nonempty := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image (Finset.univ : Finset Agent)
    (columnSum x.1.2) Finset.univ_nonempty
  choose favorite hfavorite using exists_permitted_minimizer cost permitted hdiag x.1.1
  let z : (Agent → ℝ) × (Agent → Agent → ℝ) :=
    (Pi.single k 1, fun i => Pi.single (favorite i) 1)
  refine ⟨z, ⟨single_mem_simplex k, fun i => single_mem_simplex (favorite i)⟩, ?_, ?_⟩
  · intro w hw
    change (∑ j, w j * columnSum x.1.2 j) ≤ ∑ j, (Pi.single k (1 : ℝ) : Agent → ℝ) j * columnSum x.1.2 j
    have hvertex : (∑ j, (Pi.single k (1 : ℝ) : Agent → ℝ) j * columnSum x.1.2 j) = columnSum x.1.2 k := by
      rw [Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, one_mul]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    rw [hvertex]
    calc
      ∑ j, w j * columnSum x.1.2 j ≤ ∑ j, w j * columnSum x.1.2 k := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hk j (Finset.mem_univ j)) (hw.1 j)
      _ = columnSum x.1.2 k := by rw [← Finset.sum_mul, hw.2, one_mul]
  · intro i j
    by_cases hj : j = favorite i
    · right
      subst j
      exact hfavorite i
    · left
      simp [z, Pi.single_apply, hj]

/-- The correspondence's hypotheses have all been constructed. This theorem
uses the audited proved Kakutani theorem, not a project axiom. -/
theorem exists_equilibrium_rows (cost : Agent → Agent → ℝ → ℝ)
    (hcontinuous : ∀ i j, Continuous (cost i j))
    (permitted : Agent → Agent → Prop) (hdiag : ∀ i, permitted i i) :
    ∃ y : Agent → ℝ, ∃ r : Agent → Agent → ℝ,
      y ∈ simplex ∧ (∀ i, r i ∈ simplex) ∧
      (∀ w ∈ simplex, ∑ j, w j * columnSum r j ≤ ∑ j, y j * columnSum r j) ∧
      supportedMinima cost permitted y r := by
  obtain ⟨x, hx⟩ := kakutani_fixed_point domain domain_convex domain_compact domain_nonempty
    (response cost permitted) (response_closedGraph cost hcontinuous permitted)
    (fun x => ⟨fun _ h => h.1, response_convex cost permitted x,
      response_nonempty cost permitted hdiag x⟩)
  exact ⟨x.1.1, x.1.2, x.property.1, x.property.2, hx.2.1, hx.2.2⟩

end EnvyFreeResearch.Full.Chores.FixedPoint
