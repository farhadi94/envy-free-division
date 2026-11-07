import Mathlib

/-!
# Round 3: finite certificates for the uniform-input query lower bound

This file proves finite mass transfer, a mixed-owner atom pigeonhole, and
endpoint/query counting. It does not formalize interval geometry, root
oracles, rational interior witnesses, random executions, or measurability.
-/

namespace EnvyFreeResearch.R3QueryLower

open scoped BigOperators

variable {Owner Atom Point : Type*}

/-- A positive total over finitely many atoms has a positive atom. -/
theorem positive_entry_of_positive_sum [Fintype Atom] (w : Atom → ℝ)
    (h : 0 < ∑ a, w a) : ∃ a, 0 < w a := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum : (∑ a, w a) ≤ 0 := Finset.sum_nonpos (fun a _ => hnone a)
  linarith

/-- If every positive owner uses an exclusive atom, owners inject into atoms. -/
theorem owners_le_atoms_of_pure [Fintype Owner] [Fintype Atom]
    (m : Atom → Owner → ℝ) (hpositive : ∀ j, 0 < ∑ a, m a j)
    (hpure : ∀ a j k, 0 < m a j → 0 < m a k → j = k) :
    Fintype.card Owner ≤ Fintype.card Atom := by
  classical
  have hex : ∀ j, ∃ a, 0 < m a j :=
    fun j => positive_entry_of_positive_sum (fun a => m a j) (hpositive j)
  let pick : Owner → Atom := fun j => Classical.choose (hex j)
  have hpick : ∀ j, 0 < m (pick j) j := fun j => Classical.choose_spec (hex j)
  have hinj : Function.Injective pick := by
    intro j k heq
    exact hpure (pick j) j k (hpick j) (by simpa [heq] using hpick k)
  exact Fintype.card_le_of_injective pick hinj

/-- Fewer information atoms than positive owners forces mixed ownership. -/
theorem mixed_atom_of_fewer_atoms [Fintype Owner] [Fintype Atom]
    (m : Atom → Owner → ℝ) (hpositive : ∀ j, 0 < ∑ a, m a j)
    (hcard : Fintype.card Atom < Fintype.card Owner) :
    ∃ a j k, j ≠ k ∧ 0 < m a j ∧ 0 < m a k := by
  classical
  by_contra hnone
  have hpure : ∀ a j k, 0 < m a j → 0 < m a k → j = k := by
    intro a j k hj hk
    by_contra hne
    exact hnone ⟨a, j, k, hne, hj, hk⟩
  have hle := owners_le_atoms_of_pure m hpositive hpure
  omega

/-- Of two owners of an atom, at least one differs from a designated observer. -/
theorem mixed_atom_with_rival [Fintype Owner] [Fintype Atom]
    (m : Atom → Owner → ℝ) (hpositive : ∀ j, 0 < ∑ a, m a j)
    (hcard : Fintype.card Atom < Fintype.card Owner) (i : Owner) :
    ∃ a j k, j ≠ i ∧ j ≠ k ∧ 0 < m a j ∧ 0 < m a k := by
  classical
  obtain ⟨a, j, k, hjk, hj, hk⟩ := mixed_atom_of_fewer_atoms m hpositive hcard
  by_cases hji : j = i
  · refine ⟨a, k, j, ?_, hjk.symm, hk, hj⟩
    intro hki
    exact hjk (hji.trans hki.symm)
  · exact ⟨a, j, k, hji, hjk, hj, hk⟩

/-- A bounded local bump can always have strictly positive transferred mass. -/
theorem bounded_bump_amplitude (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < min a b / 2 ∧ min a b / 2 ≤ a / 2 ∧ min a b / 2 ≤ b / 2 := by
  have hm : 0 < min a b := lt_min ha hb
  have hma := min_le_left a b
  have hmb := min_le_right a b
  constructor
  · positivity
  · constructor <;> linarith

/-- Both signs of a constant density correction stay in [1/2,3/2]. -/
theorem density_bounds (length amount : ℝ) (hlength : 0 < length)
    (hamount : 0 ≤ amount) (hsmall : amount ≤ length / 2) :
    (1 / 2 : ℝ) ≤ 1 + amount / length ∧ 1 + amount / length ≤ 3 / 2 ∧
      (1 / 2 : ℝ) ≤ 1 - amount / length ∧ 1 - amount / length ≤ 3 / 2 := by
  have hratio0 : 0 ≤ amount / length := div_nonneg hamount hlength.le
  have hratio : amount / length ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hlength).2 (by linarith)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Equal positive and negative integrated bumps preserve the containing atom's mass. -/
theorem bump_integral_preserved (a b amount : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * (1 + amount / a) + b * (1 - amount / b) = a + b := by
  field_simp
  ring

noncomputable def transfer (w : Owner → ℝ) (j k : Owner) (amount : ℝ) : Owner → ℝ := by
  classical
  exact fun h => w h + (if h = j then amount else 0) - (if h = k then amount else 0)

/-- A finite transfer changes no total mass. -/
theorem transfer_sum [Fintype Owner] (w : Owner → ℝ) (j k : Owner) (amount : ℝ) :
    (∑ h, transfer w j k amount h) = ∑ h, w h := by
  classical
  simp [transfer, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem transfer_at_receiver (w : Owner → ℝ) (j k : Owner) (amount : ℝ) (hjk : j ≠ k) :
    transfer w j k amount j = w j + amount := by
  classical
  simp [transfer, hjk]

theorem transfer_at_donor (w : Owner → ℝ) (j k : Owner) (amount : ℝ) (hjk : j ≠ k) :
    transfer w j k amount k = w k - amount := by
  classical
  simp [transfer, hjk.symm]

theorem transfer_nonnegative (w : Owner → ℝ) (j k : Owner) (amount : ℝ)
    (hw : ∀ h, 0 ≤ w h) (hamount : 0 ≤ amount) (hdonor : amount ≤ w k) :
    ∀ h, 0 ≤ transfer w j k amount h := by
  classical
  intro h
  have hplus : 0 ≤ (if h = j then amount else 0) := by
    split_ifs <;> linarith
  have hminus : (if h = k then amount else 0) ≤ w h := by
    split_ifs with hk
    · simpa only [hk] using hdonor
    · exact hw h
  unfold transfer
  linarith

/-- At equal old totals, cake envy increases by one or two transferred masses. -/
theorem cake_envy_gap [DecidableEq Owner] (w : Owner → ℝ) (i j k : Owner) (amount : ℝ)
    (hij : i ≠ j) (hjk : j ≠ k) (hequal : w i = w j) :
    transfer w j k amount j - transfer w j k amount i =
      amount * (1 + if i = k then 1 else 0) := by
  classical
  by_cases hik : i = k
  · subst i
    simp [transfer, hjk, hjk.symm]
    linarith
  · simp [transfer, hij, hjk, hik]
    linarith

/-- Reversing the transfer creates the same strict gap for chores. -/
theorem chore_envy_gap [DecidableEq Owner] (w : Owner → ℝ) (i j k : Owner) (amount : ℝ)
    (hij : i ≠ j) (hjk : j ≠ k) (hequal : w i = w j) :
    transfer w k j amount i - transfer w k j amount j =
      amount * (1 + if i = k then 1 else 0) := by
  classical
  by_cases hik : i = k
  · subst i
    simp [transfer, hjk, hjk.symm]
    linarith
  · simp [transfer, hij, hjk, hik]
    linarith

theorem cake_strict_envy (w : Owner → ℝ) (i j k : Owner) (amount : ℝ)
    (hij : i ≠ j) (hjk : j ≠ k) (hequal : w i = w j) (hamount : 0 < amount) :
    transfer w j k amount i < transfer w j k amount j := by
  classical
  have hg := cake_envy_gap w i j k amount hij hjk hequal
  by_cases hik : i = k
  · subst i
    simp at hg
    linarith
  · simp [hik] at hg
    linarith

theorem chore_strict_envy (w : Owner → ℝ) (i j k : Owner) (amount : ℝ)
    (hij : i ≠ j) (hjk : j ≠ k) (hequal : w i = w j) (hamount : 0 < amount) :
    transfer w k j amount j < transfer w k j amount i := by
  classical
  have hg := chore_envy_gap w i j k amount hij hjk hequal
  by_cases hik : i = k
  · subst i
    simp at hg
    linarith
  · simp [hik] at hg
    linarith

/-- A bump is supported in a single information atom and two owner pieces. -/
noncomputable def atomTransfer (m : Atom → Owner → ℝ) (a : Atom)
    (j k : Owner) (amount : ℝ) : Atom → Owner → ℝ := by
  classical
  exact fun x h => if x = a then transfer (m x) j k amount h else m x h

theorem atom_total_preserved [Fintype Owner] (m : Atom → Owner → ℝ)
    (a x : Atom) (j k : Owner) (amount : ℝ) :
    (∑ h, atomTransfer m a j k amount x h) = ∑ h, m x h := by
  classical
  by_cases hx : x = a
  · simpa [atomTransfer, hx] using transfer_sum (m a) j k amount
  · simp [atomTransfer, hx]

/-- Any query represented as a union of whole information atoms is unchanged. -/
theorem atom_union_preserved [Fintype Owner] (m : Atom → Owner → ℝ)
    (a : Atom) (j k : Owner) (amount : ℝ) (Q : Finset Atom) :
    (∑ x ∈ Q, ∑ h, atomTransfer m a j k amount x h) = ∑ x ∈ Q, ∑ h, m x h := by
  apply Finset.sum_congr rfl
  intro x _
  exact atom_total_preserved m a x j k amount

/-- Sum of the atom table after the perturbation is exactly the owner transfer. -/
theorem owner_totals_transfer [Fintype Atom] (m : Atom → Owner → ℝ)
    (a : Atom) (j k : Owner) (amount : ℝ) (h : Owner) :
    (∑ x, atomTransfer m a j k amount x h) =
      transfer (fun h => ∑ x, m x h) j k amount h := by
  classical
  have hpoint : ∀ x,
      atomTransfer m a j k amount x h = m x h +
        (if x = a then ((if h = j then amount else 0) -
          (if h = k then amount else 0)) else 0) := by
    intro x
    by_cases hx : x = a
    · simp [atomTransfer, transfer, hx]
      ring
    · simp [atomTransfer, hx]
  simp_rw [hpoint]
  simp [transfer, Finset.sum_add_distrib]
  ring

/-- At most c coordinates per query give at most c*q distinct constrained coordinates. -/
theorem endpoint_union_card [DecidableEq Point] (q c : ℕ)
    (E : Fin q → Finset Point) (hE : ∀ t, (E t).card ≤ c) :
    (Finset.univ.biUnion E).card ≤ c * q := by
  have h := Finset.card_biUnion_le_card_mul Finset.univ E c (fun t _ => hE t)
  simpa [Nat.mul_comm] using h

/-- The number of intervals is at most one more than the constrained interior coordinates. -/
theorem atom_count_from_endpoints [DecidableEq Point] (q c atoms : ℕ)
    (E : Fin q → Finset Point) (hE : ∀ t, (E t).card ≤ c)
    (hatoms : atoms ≤ (Finset.univ.biUnion E).card + 1) :
    atoms ≤ c * q + 1 := by
  have he := endpoint_union_card q c E hE
  omega

theorem row_query_threshold (n q c : ℕ) (hc : 0 < c)
    (hatoms : n ≤ c * q + 1) : (n - 1) ⌈/⌉ c ≤ q := by
  apply (ceilDiv_le_iff_le_mul hc).2
  omega

/-- Summing the rowwise information requirements gives the quadratic threshold. -/
theorem row_query_sum_lower [Fintype Owner] (q : Owner → ℕ) (c : ℕ) (hc : 0 < c)
    (hrow : ∀ i, Fintype.card Owner ≤ c * q i + 1) :
    Fintype.card Owner * ((Fintype.card Owner - 1) ⌈/⌉ c) ≤ ∑ i, q i := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => row_query_threshold (Fintype.card Owner) (q i) c hc (hrow i))
  simpa using hsum

/-- Pure atom tables with positive owner totals imply the query threshold. -/
theorem query_lower_of_pure_atoms [Fintype Owner]
    (q atomCount : Owner → ℕ) (c : ℕ) (hc : 0 < c)
    (m : (i : Owner) → Fin (atomCount i) → Owner → ℝ)
    (hpositive : ∀ i j, 0 < ∑ a, m i a j)
    (hpure : ∀ i a j k, 0 < m i a j → 0 < m i a k → j = k)
    (hatoms : ∀ i, atomCount i ≤ c * q i + 1) :
    Fintype.card Owner * ((Fintype.card Owner - 1) ⌈/⌉ c) ≤ ∑ i, q i := by
  apply row_query_sum_lower q c hc
  intro i
  have h := owners_le_atoms_of_pure (m i) (hpositive i) (hpure i)
  simp only [Fintype.card_fin] at h
  exact h.trans (hatoms i)

/-- A transcript below the total threshold has a mixed-owner row atom. -/
theorem short_total_has_mixed_atom [Fintype Owner]
    (q atomCount : Owner → ℕ) (c : ℕ) (hc : 0 < c)
    (m : (i : Owner) → Fin (atomCount i) → Owner → ℝ)
    (hpositive : ∀ i j, 0 < ∑ a, m i a j)
    (hatoms : ∀ i, atomCount i ≤ c * q i + 1)
    (hshort : (∑ i, q i) < Fintype.card Owner * ((Fintype.card Owner - 1) ⌈/⌉ c)) :
    ∃ i a j k, j ≠ k ∧ 0 < m i a j ∧ 0 < m i a k := by
  classical
  by_contra hnone
  have hpure : ∀ i a j k, 0 < m i a j → 0 < m i a k → j = k := by
    intro i a j k hj hk
    by_contra hne
    exact hnone ⟨i, a, j, k, hne, hj, hk⟩
  have hlower := query_lower_of_pure_atoms q atomCount c hc m hpositive hpure hatoms
  omega

/-- Ordinary Eval and forward-Cut accounting: at most two constrained coordinates. -/
theorem ordinary_query_sum_lower [Fintype Owner] (q : Owner → ℕ)
    (hrow : ∀ i, Fintype.card Owner ≤ 2 * q i + 1) :
    Fintype.card Owner * ((Fintype.card Owner - 1) ⌈/⌉ 2) ≤ ∑ i, q i :=
  row_query_sum_lower q 2 (by norm_num) hrow

/-- Conservative bracketed accounting also preserves a queried bracket endpoint. -/
theorem bracketed_query_sum_lower [Fintype Owner] (q : Owner → ℕ)
    (hrow : ∀ i, Fintype.card Owner ≤ 3 * q i + 1) :
    Fintype.card Owner * ((Fintype.card Owner - 1) ⌈/⌉ 3) ≤ ∑ i, q i :=
  row_query_sum_lower q 3 (by norm_num) hrow

/-- Fewer rational linear equations than unknowns leave a nonzero rational kernel vector. -/
theorem rational_kernel_exists (n rows : ℕ)
    (L : (Fin n → ℚ) →ₗ[ℚ] (Fin rows → ℚ)) (hrows : rows < n) :
    ∃ z, z ≠ 0 ∧ L z = 0 := by
  classical
  by_contra hnone
  have hzero : ∀ z, L z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    exact hnone ⟨z, hne, hz⟩
  have hinj : Function.Injective L := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun] at hd
  omega

/-- Include one all-ones normalization row along with the query incidence rows. -/
theorem rational_normalized_kernel (n q : ℕ)
    (A : Matrix (Fin (q + 1)) (Fin n) ℚ)
    (hnormal : ∀ j, A 0 j = 1) (hshort : q + 1 < n) :
    ∃ z : Fin n → ℚ, z ≠ 0 ∧ (∑ j, z j) = 0 ∧
      ∀ r, (∑ j, A r j * z j) = 0 := by
  obtain ⟨z, hz, hAz⟩ := rational_kernel_exists n (q + 1) A.mulVecLin hshort
  have hrow : ∀ r, (∑ j, A r j * z j) = 0 := by
    intro r
    have h := congrFun hAz r
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using h
  refine ⟨z, hz, ?_, hrow⟩
  simpa [hnormal] using hrow 0

/-- A nonzero zero-sum vector has some coordinate different from any designated coordinate. -/
theorem zero_sum_has_distinct_coordinate [Fintype Owner]
    (z : Owner → ℚ) (hz : z ≠ 0) (hsum : (∑ j, z j) = 0) (i : Owner) :
    ∃ j, z j ≠ z i := by
  classical
  by_contra hnone
  push Not at hnone
  have hconst : (∑ j, z j) = (Fintype.card Owner : ℚ) * z i := by
    calc
      _ = ∑ _j : Owner, z i := Finset.sum_congr rfl (fun j _ => hnone j)
      _ = _ := by simp
  have hcard : (Fintype.card Owner : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩))
  have hzi : z i = 0 := (mul_eq_zero.mp (hconst.symm.trans hsum)).resolve_left hcard
  apply hz
  funext j
  exact (hnone j).trans hzi

/-- Either sign of a nonzero contrast can be selected without changing homogeneous constraints. -/
theorem orient_nonzero_contrast (x y : ℚ) (hxy : x ≠ y) :
    ∃ s : ℚ, (s = 1 ∨ s = -1) ∧ 0 < s * (x - y) := by
  by_cases hpos : 0 < x - y
  · exact ⟨1, Or.inl rfl, by simpa using hpos⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hneg : x - y < 0 := by rcases lt_or_gt_of_ne hxy with h | h <;> linarith
    nlinarith

/-- A short normalized incidence table has a rational kernel direction creating a positive contrast. -/
theorem rational_oriented_kernel (n q : ℕ)
    (A : Matrix (Fin (q + 1)) (Fin n) ℚ) (i : Fin n)
    (hnormal : ∀ j, A 0 j = 1) (hshort : q + 1 < n) :
    ∃ z : Fin n → ℚ, ∃ j, (∑ h, z h) = 0 ∧
      (∀ r, (∑ h, A r h * z h) = 0) ∧ 0 < z j - z i := by
  obtain ⟨z, hz, hsum, hAz⟩ := rational_normalized_kernel n q A hnormal hshort
  obtain ⟨j, hj⟩ := zero_sum_has_distinct_coordinate z hz hsum i
  obtain ⟨s, _, hs⟩ := orient_nonzero_contrast (z j) (z i) hj
  refine ⟨fun h => s * z h, j, ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, hsum, mul_zero]
  · intro r
    calc
      (∑ h, A r h * (s * z h)) = ∑ h, s * (A r h * z h) :=
        Finset.sum_congr rfl (fun h _ => by ring)
      _ = s * ∑ h, A r h * z h := (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hAz r, mul_zero]
  · nlinarith

/-- A signed support correction with at most half the original mass keeps the density bounds. -/
theorem signed_density_bounds (length change : ℝ) (hlength : 0 < length)
    (hsmall : |change| ≤ length / 2) :
    (1 / 2 : ℝ) ≤ 1 + change / length ∧ 1 + change / length ≤ 3 / 2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hsmall
  have hratio_hi : change / length ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hlength).2 (by linarith)
  have hratio_lo : (-1 / 2 : ℝ) ≤ change / length :=
    (le_div_iff₀ hlength).2 (by linarith)
  constructor <;> linarith

/-- All homogeneous query equations survive an affine move along their kernel. -/
theorem linear_answers_preserved (n rows : ℕ)
    (L : (Fin n → ℚ) →ₗ[ℚ] (Fin rows → ℚ))
    (w z : Fin n → ℚ) (scale : ℚ) (hz : L z = 0) :
    L (w + scale • z) = L w := by
  simp [map_add, map_smul, hz]

/--
If every kernel vector must be constant across owners, normalized equations
require at least n-1 query rows. The oracle-to-kernel necessity is external.
-/
theorem normalized_equations_lower (n q : ℕ)
    (A : Matrix (Fin (q + 1)) (Fin n) ℚ) (i : Fin n)
    (hnormal : ∀ j, A 0 j = 1)
    (hcert : ∀ z : Fin n → ℚ, (∀ r, (∑ j, A r j * z j) = 0) →
      ∀ j, z j = z i) :
    n - 1 ≤ q := by
  by_contra hbound
  have hshort : q + 1 < n := by omega
  obtain ⟨z, hz, hsum, hAz⟩ := rational_normalized_kernel n q A hnormal hshort
  obtain ⟨j, hj⟩ := zero_sum_has_distinct_coordinate z hz hsum i
  exact hj (hcert z hAz j)

/-- Summing n-1 necessary scalar query equations per observer gives n(n-1). -/
theorem rank_query_sum_lower [Fintype Owner] (q : Owner → ℕ)
    (hrow : ∀ i, Fintype.card Owner - 1 ≤ q i) :
    Fintype.card Owner * (Fintype.card Owner - 1) ≤ ∑ i, q i := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simpa using hsum

#print axioms owners_le_atoms_of_pure
#print axioms mixed_atom_with_rival
#print axioms density_bounds
#print axioms bump_integral_preserved
#print axioms transfer_sum
#print axioms cake_strict_envy
#print axioms chore_strict_envy
#print axioms atom_union_preserved
#print axioms owner_totals_transfer
#print axioms endpoint_union_card
#print axioms short_total_has_mixed_atom
#print axioms ordinary_query_sum_lower
#print axioms bracketed_query_sum_lower
#print axioms rational_kernel_exists
#print axioms rational_normalized_kernel
#print axioms zero_sum_has_distinct_coordinate
#print axioms rational_oriented_kernel
#print axioms signed_density_bounds
#print axioms linear_answers_preserved
#print axioms normalized_equations_lower
#print axioms rank_query_sum_lower

end EnvyFreeResearch.R3QueryLower
