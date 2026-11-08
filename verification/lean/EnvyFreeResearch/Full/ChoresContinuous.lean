import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Continuous physical cuts for chore protocols

These lemmas concern actual finite nonatomic Borel measures on the real line.
They establish physical prefix continuity and exact target existence.  They do
not assume a fair-allocation primitive, nor do they prove the general-n chore
scheduler.
-/

noncomputable section

namespace EnvyFreeResearch.Full.Chores

open Set MeasureTheory

variable (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]

/-- The physical cost of a closed interval prefix. Endpoints have zero cost. -/
def prefixCost (a x : ℝ) : ℝ := μ.real (Icc a x)

/-- Prefix costs are continuous, including at plateaus and at both endpoints. -/
theorem prefixCost_continuousOn (a b : ℝ) :
    ContinuousOn (prefixCost μ a) (Icc a b) := by
  have h := intervalIntegral.continuousOn_primitive_Icc
    (μ := μ) (a := a) (b := b)
    (f := fun _ : ℝ => (1 : ℝ)) ((integrable_const (1 : ℝ)).integrableOn)
  change ContinuousOn (fun x => (μ (Icc a x)).toReal) (Icc a b)
  simpa [integral_const, measureReal_def] using h

omit [IsFiniteMeasure μ] in
@[simp] theorem prefixCost_self (a : ℝ) : prefixCost μ a a = 0 := by
  simp [prefixCost, measureReal_def]

/-- Every legal target is realized by a physical interval endpoint. -/
theorem exists_physical_cut {a b t : ℝ} (hab : a ≤ b)
    (ht0 : 0 ≤ t) (htotal : t ≤ μ.real (Icc a b)) :
    ∃ x ∈ Icc a b, μ.real (Icc a x) = t := by
  have ht : t ∈ Icc (prefixCost μ a a) (prefixCost μ a b) := by
    rw [prefixCost_self]
    exact ⟨ht0, htotal⟩
  exact intermediate_value_Icc hab (prefixCost_continuousOn μ a b) ht

/-- Equal-cost cutting exists without hunger or a preferred plateau endpoint. -/
theorem exists_half_cut {a b : ℝ} (hab : a ≤ b) :
    ∃ x ∈ Icc a b, μ.real (Icc a x) = μ.real (Icc a b) / 2 := by
  apply exists_physical_cut μ hab
  · exact div_nonneg measureReal_nonneg (by norm_num)
  · have h : 0 ≤ μ.real (Icc a b) := measureReal_nonneg
    linarith

/-- The endpoint belongs to the left piece; the pieces are literally disjoint. -/
theorem physical_split_disjoint (a x b : ℝ) :
    Disjoint (Icc a x) (Ioc x b) := by
  apply Set.disjoint_left.mpr
  intro y hy hz
  exact (not_lt_of_ge hy.2) hz.1

/-- All material, including null endpoints, belongs to the two-piece split. -/
theorem physical_split_union {a x b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    Icc a x ∪ Ioc x b = Icc a b := by
  ext y
  simp only [mem_union, mem_Icc, mem_Ioc]
  constructor
  · rintro (hy | hy)
    · exact ⟨hy.1, hy.2.trans hxb⟩
    · exact ⟨hax.trans hy.1.le, hy.2⟩
  · intro hy
    by_cases hyx : y ≤ x
    · exact Or.inl ⟨hy.1, hyx⟩
    · exact Or.inr ⟨lt_of_not_ge hyx, hy.2⟩

omit [NullSingletonClass μ] in
/-- The physical complementary suffix has the remaining cost. -/
theorem physical_split_cost {a x b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    μ.real (Icc a x) + μ.real (Ioc x b) = μ.real (Icc a b) := by
  rw [← measureReal_union (physical_split_disjoint a x b) measurableSet_Ioc]
  rw [physical_split_union hax hxb]

omit [NullSingletonClass μ] in
/-- Every legal half root yields two pieces equal to the cutter. -/
theorem half_cut_equal {a x b : ℝ} (hx : x ∈ Icc a b)
    (hcut : μ.real (Icc a x) = μ.real (Icc a b) / 2) :
    μ.real (Icc a x) = μ.real (Ioc x b) := by
  have h := physical_split_cost μ hx.1 hx.2
  linarith

/-- Restricting to any measurable recorded domain preserves exact prefix cutting.
This includes disconnected finite unions; it is a physical existence statement,
not a claim that the whole union can be queried in one operation. -/
theorem exists_domain_cut {a b t : ℝ} (hab : a ≤ b) (U : Set ℝ)
    (_hU : MeasurableSet U) (hbound : U ⊆ Icc a b)
    (ht0 : 0 ≤ t) (htotal : t ≤ μ.real U) :
    ∃ x ∈ Icc a b, μ.real (U ∩ Icc a x) = t := by
  have htotal' : (μ.restrict U).real (Icc a b) = μ.real U := by
    rw [measureReal_restrict_apply measurableSet_Icc]
    rw [inter_eq_self_of_subset_right hbound]
  obtain ⟨x, hx, hcost⟩ := exists_physical_cut (μ.restrict U) hab ht0
    (by simpa only [htotal'] using htotal)
  refine ⟨x, hx, ?_⟩
  rw [measureReal_restrict_apply measurableSet_Icc, inter_comm] at hcost
  exact hcost

/-- Physical prefix/suffix splitting retains all points in a recorded domain. -/
theorem domain_split (U : Set ℝ) (x : ℝ) :
    Disjoint (U ∩ Iic x) (U ∩ Ioi x) ∧
      (U ∩ Iic x) ∪ (U ∩ Ioi x) = U := by
  constructor
  · apply Set.disjoint_left.mpr
    intro y hy hz
    exact (not_lt_of_ge (show y ≤ x from hy.2)) (show x < y from hz.2)
  · ext y
    simp only [mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
    by_cases h : y ≤ x
    · simp [h]
    · simp [h, lt_of_not_ge h]

/-- Cheaper choice by agent 1 after agent 0 makes an equal-cost cut. -/
def twoAgentAllocation (cost : Fin 2 → Measure ℝ) (a x b : ℝ) : Fin 2 → Set ℝ :=
  if (cost 1).real (Icc a x) ≤ (cost 1).real (Ioc x b) then
    fun i => if i = 0 then Ioc x b else Icc a x
  else
    fun i => if i = 0 then Icc a x else Ioc x b

/-- This is the complete two-agent chore allocation for every legal half Cut
reply, including arbitrary points in a zero-cost plateau. -/
theorem twoAgent_every_half_root (cost : Fin 2 → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] {a x b : ℝ} (hx : x ∈ Icc a b)
    (hcut : (cost 0).real (Icc a x) = (cost 0).real (Icc a b) / 2) :
    let A := twoAgentAllocation cost a x b
    Disjoint (A 0) (A 1) ∧ (A 0 ∪ A 1 = Icc a b) ∧
      ∀ i j, (cost i).real (A i) ≤ (cost i).real (A j) := by
  have heq : (cost 0).real (Icc a x) = (cost 0).real (Ioc x b) := by
    have h := physical_split_cost (cost 0) hx.1 hx.2
    linarith
  have hd := physical_split_disjoint a x b
  have hu := physical_split_union hx.1 hx.2
  dsimp only
  by_cases hc : (cost 1).real (Icc a x) ≤ (cost 1).real (Ioc x b)
  · simp only [twoAgentAllocation, hc, ite_true]
    refine ⟨?_, ?_, ?_⟩
    · simpa using hd.symm
    · simpa [union_comm] using hu
    · intro i j
      fin_cases i <;> fin_cases j <;> simp_all
  · simp only [twoAgentAllocation, hc, ite_false]
    refine ⟨?_, ?_, ?_⟩
    · simpa using hd
    · simpa using hu
    · intro i j
      fin_cases i <;> fin_cases j <;> simp_all [le_of_not_ge hc]

/-- Complete envy-free chore division for two arbitrary finite atomless costs. -/
theorem exists_complete_twoAgent (cost : Fin 2 → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    {a b : ℝ} (hab : a ≤ b) :
    ∃ x ∈ Icc a b,
      let A := twoAgentAllocation cost a x b
      Disjoint (A 0) (A 1) ∧ (A 0 ∪ A 1 = Icc a b) ∧
        ∀ i j, (cost i).real (A i) ≤ (cost i).real (A j) := by
  obtain ⟨x, hx, hcut⟩ := exists_half_cut (cost 0) hab
  exact ⟨x, hx, twoAgent_every_half_root cost hx hcut⟩

/-- The cumulative prefix cost is globally continuous, including to the left
of the parent where the physical interval is empty. -/
theorem prefixCost_continuous (a : ℝ) : Continuous (prefixCost μ a) := by
  let ν := μ.restrict (Ici a)
  have hcdf : Continuous (fun x : ℝ => ν.real (Iic x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have h := (show IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (x + 1)) ν from
      (integrable_const (1 : ℝ)).integrableOn).continuousOn_Iic_primitive_Iic
    have hx : x ∈ Iic (x + 1) := by simp only [mem_Iic]; linarith
    have hh := (h x hx).continuousAt (Iic_mem_nhds (by linarith : x < x + 1))
    simpa [integral_const, measureReal_def] using hh
  have heq : (fun x : ℝ => ν.real (Iic x)) = prefixCost μ a := by
    funext x
    rw [measureReal_restrict_apply measurableSet_Iic]
    simp only [prefixCost, Iic_inter_Ici]
  rw [← heq]
  exact hcdf

omit [NullSingletonClass μ] in
/-- An interval oracle's cumulative difference equals the physical interval
cost. Thus no query to a disconnected union is introduced by this adapter. -/
theorem prefix_difference_eq_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    prefixCost μ 0 b - prefixCost μ 0 a = μ.real (Ioc a b) := by
  have h := physical_split_cost μ ha hab
  unfold prefixCost
  linarith

end EnvyFreeResearch.Full.Chores
