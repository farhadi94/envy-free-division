import EnvyFreeResearch.Full.ChoresFixedPoint
import EnvyFreeResearch.Full.ChoresDemand

/-!
# Hungry local matching, derived from the proved Kakutani application

This is the continuous local-matching lemma used in the manuscript's anchored
existence argument. It constructs positive total increment and a perfect
matching of permitted minima; no fixed point or matching existence is assumed.
An existing permitted perfect matching is relabeled as the diagonal.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open Set
open scoped BigOperators

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]

/-- Unit-simplex local matching for globally continuous costs. -/
theorem local_matching_unit (cost : Agent → Agent → ℝ → ℝ)
    (hcontinuous : ∀ i j, Continuous (cost i j))
    (permitted : Agent → Agent → Prop) (hdiag : ∀ i, permitted i i)
    (hzero : ∀ i j, permitted i j → cost i j 0 = 0)
    (hstrict : ∀ i j, permitted i j → StrictMonoOn (cost i j) (Icc (0 : ℝ) 1)) :
    ∃ y : Agent → ℝ, y ∈ FixedPoint.simplex ∧ ∃ π : Equiv.Perm Agent,
      ∀ i, permitted i (π i) ∧
        ∀ k, permitted i k → cost i (π i) (y (π i)) ≤ cost i k (y k) := by
  obtain ⟨y, r, hy, hr, hmax, hsupport⟩ :=
    FixedPoint.exists_equilibrium_rows cost hcontinuous permitted hdiag
  have hybound : ∀ j, y j ∈ Icc (0 : ℝ) 1 := by
    intro j
    refine ⟨hy.1 j, ?_⟩
    rw [← hy.2]
    exact Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ j)
  have hzeroRows : ∀ i j, y i = 0 → 0 < y j → r i j = 0 := by
    intro i j hiy hjy
    rcases hsupport i j with h | ⟨hij, hmin⟩
    · exact h
    · have hcostpos : 0 < cost i j (y j) := by
        rw [← hzero i j hij]
        exact hstrict i j hij (by simp) (hybound j) hjy
      have hle := hmin i (hdiag i)
      rw [hiy, hzero i i (hdiag i)] at hle
      exact (not_le_of_gt hcostpos hle).elim
  have hmaxVertex : ∀ k, (∑ i, r i k) ≤ ∑ j, y j * (∑ i, r i j) := by
    intro k
    have h := hmax (Pi.single k 1) (FixedPoint.single_mem_simplex k)
    have hv : (∑ j, (Pi.single k (1 : ℝ) : Agent → ℝ) j * FixedPoint.columnSum r j) =
        FixedPoint.columnSum r k := by
      rw [Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, one_mul]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    rw [hv] at h
    exact h
  have hcolumns := equilibrium_columns_one y r hy.1 hy.2
    (fun i j => (hr i).1 j) (fun i => (hr i).2) hzeroRows hmaxVertex
  obtain ⟨π, hπ⟩ := demand_minimizer_matching (fun i j => cost i j (y j)) permitted r
    (fun i j => (hr i).1 j) (fun i => (hr i).2) hcolumns
    (fun i j hij => (hsupport i j).resolve_left (ne_of_gt hij))
  exact ⟨y, hy, π, hπ⟩

def unitClip (x : ℝ) : ℝ := min 1 (max 0 x)

lemma unitClip_continuous : Continuous unitClip := by unfold unitClip; fun_prop

lemma unitClip_mem (x : ℝ) : unitClip x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma unitClip_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : unitClip x = x := by
  rw [unitClip, max_eq_right hx.1, min_eq_right hx.2]

/-- Local matching on an arbitrary positive increment interval. All hypotheses
are about the given continuous costs; the increment vector and matching are
constructed by the proved compact-convex fixed-point argument. -/
theorem local_matching (δ : ℝ) (hδ : 0 < δ) (cost : Agent → Agent → ℝ → ℝ)
    (hcontinuous : ∀ i j, ContinuousOn (cost i j) (Icc 0 δ))
    (permitted : Agent → Agent → Prop) (hdiag : ∀ i, permitted i i)
    (hzero : ∀ i j, permitted i j → cost i j 0 = 0)
    (hstrict : ∀ i j, permitted i j → StrictMonoOn (cost i j) (Icc 0 δ)) :
    ∃ y : Agent → ℝ, (∀ j, y j ∈ Icc 0 δ) ∧ (∑ j, y j = δ) ∧
      ∃ π : Equiv.Perm Agent, ∀ i, permitted i (π i) ∧
        ∀ k, permitted i k → cost i (π i) (y (π i)) ≤ cost i k (y k) := by
  let g := fun i j x => cost i j (δ * unitClip x)
  have hscaled (x : ℝ) : δ * unitClip x ∈ Icc 0 δ := by
    refine ⟨mul_nonneg hδ.le (unitClip_mem x).1, ?_⟩
    simpa using mul_le_mul_of_nonneg_left (unitClip_mem x).2 hδ.le
  have hgcont : ∀ i j, Continuous (g i j) := by
    intro i j
    exact (hcontinuous i j).comp_continuous (continuous_const.mul unitClip_continuous)
      (fun x => hscaled x)
  have hgzero : ∀ i j, permitted i j → g i j 0 = 0 := by
    intro i j hij
    simpa [g, unitClip] using hzero i j hij
  have hgstrict : ∀ i j, permitted i j → StrictMonoOn (g i j) (Icc (0 : ℝ) 1) := by
    intro i j hij a ha b hb hab
    apply hstrict i j hij (hscaled a) (hscaled b)
    rw [unitClip_eq ha, unitClip_eq hb]
    exact mul_lt_mul_of_pos_left hab hδ
  obtain ⟨y, hy, π, hπ⟩ := local_matching_unit g hgcont permitted hdiag hgzero hgstrict
  have hybound : ∀ j, y j ∈ Icc (0 : ℝ) 1 := by
    intro j
    refine ⟨hy.1 j, ?_⟩
    rw [← hy.2]
    exact Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ j)
  refine ⟨fun j => δ * y j, ?_, ?_, π, ?_⟩
  · intro j
    simpa only [unitClip_eq (hybound j)] using hscaled (y j)
  · rw [← Finset.mul_sum, hy.2, mul_one]
  · intro i
    refine ⟨(hπ i).1, ?_⟩
    intro k hk
    simpa only [g, unitClip_eq (hybound (π i)), unitClip_eq (hybound k)] using (hπ i).2 k hk

end EnvyFreeResearch.Full.Chores
