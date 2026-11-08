import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Tactic

/-!
# Demand matrices and the matching extraction in hungry Core existence

These finite lemmas are the matching part of the local enlargement argument.
The probability rows will be constructed by the Kakutani correspondence;
they are not an oracle interface and do not assume an envy-free allocation.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open scoped BigOperators
open Finset Matrix

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

/-- A concrete permutation uses only positive entries of a doubly stochastic
matrix. This follows from mathlib's proved Birkhoff decomposition. -/
theorem demand_support_permutation (r : Agent → Agent → ℝ)
    (hnonnegative : ∀ i j, 0 ≤ r i j)
    (hrow : ∀ i, ∑ j, r i j = 1) (hcol : ∀ j, ∑ i, r i j = 1) :
    ∃ π : Equiv.Perm Agent, ∀ i, 0 < r i (π i) := by
  have hstochastic : r ∈ doublyStochastic ℝ Agent :=
    mem_doublyStochastic_iff_sum.mpr ⟨hnonnegative, hrow, hcol⟩
  obtain ⟨w, hw, hsum, hmatrix⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hstochastic
  have hpositive : ∃ π, 0 < w π := by
    by_contra! h
    have hsumzero : (∑ π, w π) ≤ 0 := Finset.sum_nonpos (fun π _ => h π)
    rw [hsum] at hsumzero
    norm_num at hsumzero
  obtain ⟨π, hπ⟩ := hpositive
  refine ⟨π, ?_⟩
  intro i
  have hentry : (∑ σ : Equiv.Perm Agent, w σ * σ.permMatrix ℝ i (π i)) = r i (π i) := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun M : Matrix Agent Agent ℝ => M i (π i)) hmatrix
  have hle : w π * π.permMatrix ℝ i (π i) ≤
      ∑ σ : Equiv.Perm Agent, w σ * σ.permMatrix ℝ i (π i) := by
    apply Finset.single_le_sum (f := fun σ : Equiv.Perm Agent => w σ * σ.permMatrix ℝ i (π i)) _ (Finset.mem_univ π)
    intro σ _
    apply mul_nonneg (hw σ)
    exact nonneg_of_mem_doublyStochastic (permMatrix_mem_doublyStochastic (σ := σ))
  have hdiag : π.permMatrix ℝ i (π i) = 1 := by simp [Equiv.toPEquiv_apply]
  rw [hdiag, mul_one, hentry] at hle
  exact hπ.trans_le hle

/-- A probability-supported minimizer correspondence supplies an actual
perfect matching of permitted minima. -/
theorem demand_minimizer_matching (cost : Agent → Agent → ℝ)
    (permitted : Agent → Agent → Prop) (r : Agent → Agent → ℝ)
    (hnonnegative : ∀ i j, 0 ≤ r i j)
    (hrow : ∀ i, ∑ j, r i j = 1) (hcol : ∀ j, ∑ i, r i j = 1)
    (hsupport : ∀ i j, 0 < r i j →
      permitted i j ∧ ∀ k, permitted i k → cost i j ≤ cost i k) :
    ∃ π : Equiv.Perm Agent, ∀ i,
      permitted i (π i) ∧ ∀ k, permitted i k → cost i (π i) ≤ cost i k := by
  obtain ⟨π, hπ⟩ := demand_support_permutation r hnonnegative hrow hcol
  exact ⟨π, fun i => hsupport i (π i) (hπ i)⟩

/-- Agents with a zero original matched coordinate send all their probability
mass into the zero-coordinate columns. Their total demand is therefore at
least the number of those columns, without assuming column balance. -/
theorem zero_columns_demand_lower (y : Agent → ℝ) (r : Agent → Agent → ℝ)
    (hy : ∀ j, 0 ≤ y j) (hr : ∀ i j, 0 ≤ r i j)
    (hrow : ∀ i, ∑ j, r i j = 1)
    (hzero : ∀ i j, y i = 0 → 0 < y j → r i j = 0) :
    (((Finset.univ.filter (fun j => y j = 0)).card : ℕ) : ℝ) ≤
      ∑ j ∈ Finset.univ.filter (fun j => y j = 0), ∑ i, r i j := by
  classical
  let Z := Finset.univ.filter (fun j => y j = 0)
  have hrows (i : Agent) (hi : i ∈ Z) : ∑ j ∈ Z, r i j = 1 := by
    rw [← hrow i]
    apply Finset.sum_subset (Finset.subset_univ Z)
    intro j _ hj
    have hjpos : 0 < y j := lt_of_le_of_ne (hy j) (Ne.symm (by simpa [Z] using hj))
    exact hzero i j (by simpa [Z] using hi) hjpos
  calc
    (Z.card : ℝ) = ∑ i ∈ Z, ∑ j ∈ Z, r i j := by
      rw [Finset.sum_congr rfl (fun i hi => hrows i hi)]
      simp
    _ = ∑ j ∈ Z, ∑ i ∈ Z, r i j := Finset.sum_comm
    _ ≤ ∑ j ∈ Z, ∑ i, r i j := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z) (fun i _ _ => hr i j)

/-- At an equilibrium, every positive increment is on a largest-demand column;
zero-increment rows force enough demand in zero columns. Together these facts
force every column demand to be one. -/
theorem equilibrium_columns_one [Nonempty Agent]
    (y : Agent → ℝ) (r : Agent → Agent → ℝ)
    (hy : ∀ j, 0 ≤ y j) (hysum : ∑ j, y j = 1)
    (hr : ∀ i j, 0 ≤ r i j) (hrow : ∀ i, ∑ j, r i j = 1)
    (hzero : ∀ i j, y i = 0 → 0 < y j → r i j = 0)
    (hmax : ∀ k, (∑ i, r i k) ≤ ∑ j, y j * (∑ i, r i j)) :
    ∀ j, ∑ i, r i j = 1 := by
  classical
  let d := fun j => ∑ i, r i j
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image (Finset.univ : Finset Agent) d Finset.univ_nonempty
  have hbound : ∀ j, d j ≤ d k := fun j => hk j (Finset.mem_univ j)
  have hdot : ∑ j, y j * d j = d k := by
    apply le_antisymm _ (hmax k)
    calc
      ∑ j, y j * d j ≤ ∑ j, y j * d k :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hy j))
      _ = d k := by rw [← Finset.sum_mul, hysum, one_mul]
  have hdeficit : ∑ j, y j * (d k - d j) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hysum, one_mul, hdot, sub_self]
  have hterm : ∀ j, y j * (d k - d j) = 0 :=
    fun j => (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hy j) (sub_nonneg.mpr (hbound j)))).mp hdeficit j (Finset.mem_univ j)
  have hpositive : ∀ j, 0 < y j → d j = d k := by
    intro j hj
    have hz := (mul_eq_zero.mp (hterm j)).resolve_left (ne_of_gt hj)
    linarith
  let Z := Finset.univ.filter (fun j => y j = 0)
  let P := Zᶜ
  have hP : P.Nonempty := by
    by_contra hn
    have hempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hyzero : ∀ j, y j = 0 := by
      intro j
      have hjnot : j ∉ P := by simp [hempty]
      simpa [P, Z] using hjnot
    have hbad : (∑ j, y j) = 0 := by simp [hyzero]
    rw [hysum] at hbad
    norm_num at hbad
  have hPon : ∀ j ∈ P, d j = d k := by
    intro j hj
    apply hpositive
    apply lt_of_le_of_ne (hy j)
    exact Ne.symm (by simpa [P, Z] using hj)
  have htotal : ∑ j, d j = (Fintype.card Agent : ℝ) := by
    dsimp only [d]
    rw [Finset.sum_comm]
    simp [hrow]
  have hPsum : ∑ j ∈ P, d j = (P.card : ℝ) * d k := by
    rw [Finset.sum_congr rfl hPon]
    simp
  have hsum : (∑ j ∈ Z, d j) + (P.card : ℝ) * d k = Fintype.card Agent := by
    rw [← hPsum]
    simpa only [P, Finset.sum_add_sum_compl] using htotal
  have hZ : (Z.card : ℝ) ≤ ∑ j ∈ Z, d j :=
    zero_columns_demand_lower y r hy hr hrow hzero
  have hcards : (Z.card : ℝ) + (P.card : ℝ) = Fintype.card Agent := by
    exact_mod_cast Finset.card_add_card_compl Z
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hkone : d k ≤ 1 := by nlinarith
  have hdle : ∀ j, d j ≤ 1 := fun j => (hbound j).trans hkone
  intro j
  apply le_antisymm (hdle j)
  by_contra h
  have hjlt : d j < 1 := lt_of_not_ge h
  have hsumlt : (∑ q, d q) < ∑ _q : Agent, (1 : ℝ) :=
    Finset.sum_lt_sum (fun q _ => hdle q) ⟨j, Finset.mem_univ j, hjlt⟩
  simpa [htotal] using hsumlt

end EnvyFreeResearch.Full.Chores
