import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Simultaneous finite realization of chore cost records

The formal cost table uses a real primary value and a rational secondary
label.  One positive real perturbation realizes *all* comparisons in an
arbitrary finite completed table.  This is the comparison-preservation part
of Lemma `r6core:realization`; the dynamic-program replay and interpolation
remain separate obligations.
-/

noncomputable section

namespace EnvyFreeResearch.Full.Chores

open Filter Topology

/-- Strict lexicographic comparison of one recorded cost. -/
def recordLT (x y : ℝ × ℚ) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

/-- The ordinary real value used in the finite hungry realization. -/
def realizedCost (ε : ℝ) (x : ℝ × ℚ) : ℝ := x.1 + ε * (x.2 : ℝ)

/-- Every strict formal comparison holds eventually for positive perturbations. -/
theorem eventually_realized_lt (x y : ℝ × ℚ) (h : recordLT x y) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, realizedCost ε x < realizedCost ε y := by
  rcases h with h | ⟨hreal, hlabel⟩
  · have hc : Continuous (fun ε : ℝ => realizedCost ε y - realizedCost ε x) := by
      unfold realizedCost
      fun_prop
    have hp : 0 < realizedCost 0 y - realizedCost 0 x := by
      simp only [realizedCost, zero_mul, add_zero]
      linarith
    have he := hc.continuousAt.eventually (eventually_gt_nhds hp)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with ε hε
    linarith
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have he : (0 : ℝ) < ε := hε
    have hlabel' : (x.2 : ℝ) < (y.2 : ℝ) := by exact_mod_cast hlabel
    unfold realizedCost
    rw [hreal]
    exact add_lt_add_right (mul_lt_mul_of_pos_left hlabel' he) _

/-- One common positive perturbation preserves every strict comparison in a
finite table, including comparisons between different parents or observers. -/
theorem exists_common_perturbation {Record : Type*} [Fintype Record]
    (value : Record → ℝ × ℚ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j,
      recordLT (value i) (value j) →
      realizedCost ε (value i) < realizedCost ε (value j) := by
  have hpair : ∀ i j, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      recordLT (value i) (value j) →
      realizedCost ε (value i) < realizedCost ε (value j) := by
    intro i j
    by_cases h : recordLT (value i) (value j)
    · exact (eventually_realized_lt (value i) (value j) h).mono (fun _ hε _ => hε)
    · exact Eventually.of_forall (fun _ hi => (h hi).elim)
  have hall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ i j,
      recordLT (value i) (value j) →
      realizedCost ε (value i) < realizedCost ε (value j) := by
    exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hpair i))
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  exact (hpos.and hall).exists

/-- Lexicographic cost records have trichotomy. -/
theorem record_trichotomy (x y : ℝ × ℚ) :
    recordLT x y ∨ x = y ∨ recordLT y x := by
  rcases lt_trichotomy x.1 y.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy x.2 y.2 with hq | hq | hq
    · exact Or.inl (Or.inr ⟨h, hq⟩)
    · exact Or.inr (Or.inl (Prod.ext h hq))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, hq⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- The same perturbation realizes strict inequalities and exact equalities
simultaneously, so an entire finite transcript can share one real cost table. -/
theorem exists_exact_comparison_realization {Record : Type*} [Fintype Record]
    (value : Record → ℝ × ℚ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j,
      (recordLT (value i) (value j) ↔
        realizedCost ε (value i) < realizedCost ε (value j)) ∧
      (value i = value j ↔ realizedCost ε (value i) = realizedCost ε (value j)) := by
  obtain ⟨ε, hε, hpreserve⟩ := exists_common_perturbation value
  refine ⟨ε, hε, fun i j => ⟨⟨hpreserve i j, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · intro hij
    rcases record_trichotomy (value i) (value j) with h | h | h
    · exact h
    · rw [h] at hij
      exact (lt_irrefl _ hij).elim
    · exact (lt_asymm hij (hpreserve j i h)).elim
  · intro hij
    exact congrArg (realizedCost ε) hij
  · intro hij
    rcases record_trichotomy (value i) (value j) with h | h | h
    · have hlt := hpreserve i j h
      rw [hij] at hlt
      exact (lt_irrefl _ hlt).elim
    · exact h
    · have hlt := hpreserve j i h
      rw [hij] at hlt
      exact (lt_irrefl _ hlt).elim

end EnvyFreeResearch.Full.Chores
