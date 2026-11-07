import Mathlib
import EnvyFreeResearch.R2OnlinePotential
import EnvyFreeResearch.R3QueryLower

/-!
# Round 4: global guards and anchored domination potential

The original agent type remains fixed throughout every count. Whole-label
transport is measured from the saved anchor, never from a temporary snapshot
allocation whose pieces are subsequently moved separately. Zero residue rows
use saturation, not a universal image inclusion into proper targets.
-/

namespace EnvyFreeResearch.R4GlobalPotential

open scoped BigOperators

variable {Agent : Type*}

abbrev Matrix (Agent : Type*) := Agent → Agent → ℝ

def CakeEF (V : Matrix Agent) : Prop := ∀ i j, V i j ≤ V i i
def ChoreEF (V : Matrix Agent) : Prop := ∀ i j, V i i ≤ V i j
def cakeGap (V : Matrix Agent) (i j : Agent) : ℝ := V i i - V i j
def choreGap (V : Matrix Agent) (i j : Agent) : ℝ := V i j - V i i

def CakeGuard (V : Matrix Agent) (A : Set Agent) (r : Agent → ℝ) : Prop :=
  ∀ f ∉ A, ∀ i ∈ A, r f ≤ cakeGap V f i

def ChoreGuard (V : Matrix Agent) (A : Set Agent) (r : Agent → ℝ) : Prop :=
  ∀ i ∈ A, ∀ f ∉ A, r i ≤ choreGap V i f

/-- A permutation fixing every frozen label preserves the active set. -/
theorem permutation_active_iff (f : Equiv.Perm Agent) (A : Set Agent)
    (hfixed : ∀ j ∉ A, f j = j) (j : Agent) : f j ∈ A ↔ j ∈ A := by
  constructor
  · intro hfj
    by_contra hj
    rw [hfixed j hj] at hfj
    exact hj hfj
  · intro hj
    by_contra hfj
    have heq : f (f j) = f j := hfixed (f j) hfj
    have hjf : f j = j := f.injective heq
    exact hfj (by simpa only [hjf] using hj)

/-- Frozen bundles are unchanged in every observer's row. -/
theorem frozen_value_unchanged (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (A : Set Agent) (hfixed : ∀ j ∉ A, f j = j)
    (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (hfrozen : ∀ i j, j ∉ A → B i j = 0) (i j : Agent) (hj : j ∉ A) :
    W i j = V i j := by
  have h := hwhole i j
  rw [hfixed j hj, hfrozen i j hj, add_zero] at h
  exact h

/-- Cake's frozen-observer guard uses the compared label's residual addition. -/
theorem cake_guard_preserved (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (A : Set Agent) (r r' : Agent → ℝ)
    (hfixed : ∀ j ∉ A, f j = j)
    (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (hfrozen : ∀ i j, j ∉ A → B i j = 0)
    (hbudget : ∀ i j, B i j + r' i ≤ r i)
    (hguard : CakeGuard V A r) : CakeGuard W A r' := by
  intro i hi j hj
  have hk : f.symm j ∈ A := (permutation_active_iff f A hfixed (f.symm j)).mp (by simpa using hj)
  have hg := hguard i hi (f.symm j) hk
  have hb := hbudget i (f.symm j)
  have hw := hwhole i (f.symm j)
  simp only [f.apply_symm_apply] at hw
  have hf := frozen_value_unchanged V W B f A hfixed hwhole hfrozen i i hi
  unfold cakeGap at *
  linarith

/-- Chore's active-observer guard charges its own old-label addition. -/
theorem chore_guard_preserved (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (A : Set Agent) (r r' : Agent → ℝ)
    (hfixed : ∀ j ∉ A, f j = j)
    (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (hfrozen : ∀ i j, j ∉ A → B i j = 0)
    (hbudget : ∀ i j, B i j + r' i ≤ r i)
    (hactive : ∀ i ∈ A, ∀ j ∈ A, W i i ≤ W i j)
    (hguard : ChoreGuard V A r) : ChoreGuard W A r' := by
  intro i hi j hj
  have hfi := (permutation_active_iff f A hfixed i).mpr hi
  have ha := hactive i hi (f i) hfi
  have hg := hguard i hi j hj
  have hb := hbudget i i
  have hw := hwhole i i
  have hf := frozen_value_unchanged V W B f A hfixed hwhole hfrozen i j hj
  unfold choreGap at *
  linarith

/-- All four active/frozen cake comparisons, before invoking global EF for transport. -/
theorem cake_global_EF (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (A : Set Agent) (r r' : Agent → ℝ)
    (hV : CakeEF V) (hguard : CakeGuard V A r)
    (hfixed : ∀ j ∉ A, f j = j)
    (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (hfrozen : ∀ i j, j ∉ A → B i j = 0)
    (hnonneg : ∀ i j, 0 ≤ B i j)
    (hbudget : ∀ i j, B i j + r' i ≤ r i)
    (hr' : ∀ i, 0 ≤ r' i)
    (hactive : ∀ i ∈ A, ∀ j ∈ A, W i j ≤ W i i) : CakeEF W := by
  have hnewguard := cake_guard_preserved V W B f A r r' hfixed hwhole hfrozen hbudget hguard
  intro i j
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · exact hactive i hi j hj
    · have ha := hactive i hi (f i) ((permutation_active_iff f A hfixed i).mpr hi)
      have hw := hwhole i i
      have hb := hnonneg i i
      have hv := hV i j
      have hf := frozen_value_unchanged V W B f A hfixed hwhole hfrozen i j hj
      linarith
  · by_cases hj : j ∈ A
    · have hg := hnewguard i hi j hj
      have hr := hr' i
      unfold cakeGap at hg
      linarith
    · rw [frozen_value_unchanged V W B f A hfixed hwhole hfrozen i i hi,
        frozen_value_unchanged V W B f A hfixed hwhole hfrozen i j hj]
      exact hV i j

/-- All four active/frozen chore comparisons; no own-cost preservation is assumed. -/
theorem chore_global_EF (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (A : Set Agent) (r r' : Agent → ℝ)
    (hV : ChoreEF V) (hguard : ChoreGuard V A r)
    (hfixed : ∀ j ∉ A, f j = j)
    (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (hfrozen : ∀ i j, j ∉ A → B i j = 0)
    (hnonneg : ∀ i j, 0 ≤ B i j)
    (hbudget : ∀ i j, B i j + r' i ≤ r i)
    (hr' : ∀ i, 0 ≤ r' i)
    (hactive : ∀ i ∈ A, ∀ j ∈ A, W i i ≤ W i j) : ChoreEF W := by
  have hnewguard := chore_guard_preserved V W B f A r r' hfixed hwhole hfrozen hbudget hactive hguard
  intro i j
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · exact hactive i hi j hj
    · have hg := hnewguard i hi j hj
      have hr := hr' i
      unfold choreGap at hg
      linarith
  · by_cases hj : j ∈ A
    · have hv := hV i (f.symm j)
      have hw := hwhole i (f.symm j)
      simp only [f.apply_symm_apply] at hw
      have hb := hnonneg i (f.symm j)
      have hf := frozen_value_unchanged V W B f A hfixed hwhole hfrozen i i hi
      linarith
    · rw [frozen_value_unchanged V W B f A hfixed hwhole hfrozen i i hi,
        frozen_value_unchanged V W B f A hfixed hwhole hfrozen i j hj]
      exact hV i j

/-- Cake freezes the separated sink; no allocation or residue changes. -/
theorem cake_guard_after_freeze (V : Matrix Agent) (A S : Set Agent) (r : Agent → ℝ)
    (hsub : S ⊆ A) (hguard : CakeGuard V A r)
    (hnew : ∀ f ∈ A, f ∉ S → ∀ i ∈ S, r f ≤ cakeGap V f i) : CakeGuard V S r := by
  intro f hf i hi
  by_cases hfA : f ∈ A
  · exact hnew f hfA hf i hi
  · exact hguard f hfA i (hsub hi)

/-- Chores continue with the separated sink and freeze its complement. -/
theorem chore_guard_after_freeze (V : Matrix Agent) (A S : Set Agent) (r : Agent → ℝ)
    (hsub : S ⊆ A) (hguard : ChoreGuard V A r)
    (hnew : ∀ i ∈ S, ∀ f ∈ A, f ∉ S → r i ≤ choreGap V i f) : ChoreGuard V S r := by
  intro i hi f hf
  by_cases hfA : f ∈ A
  · exact hnew i hi f hfA hf
  · exact hguard i (hsub hi) f hfA

theorem cake_whole_label_transport (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (hW : CakeEF W) (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (i j : Agent) (hown : 0 ≤ B i i) :
    cakeGap V i j - B i j ≤ cakeGap W i (f j) := by
  have ho := hW i (f i)
  rw [hwhole i i] at ho
  unfold cakeGap
  rw [hwhole i j]
  linarith

theorem chore_whole_label_transport (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (hW : ChoreEF W) (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (i j : Agent) (hother : 0 ≤ B i j) :
    choreGap V i j - B i i ≤ choreGap W i (f j) := by
  have ho := hW i (f i)
  rw [hwhole i i] at ho
  unfold choreGap
  rw [hwhole i j]
  linarith

theorem cake_residue_transport (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (hW : CakeEF W) (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (i j : Agent) (r r' : ℝ) (hown : 0 ≤ B i i)
    (hold : r ≤ cakeGap V i j) (hbudget : B i j + r' ≤ r) :
    r' ≤ cakeGap W i (f j) := by
  have h := cake_whole_label_transport V W B f hW hwhole i j hown
  linarith

theorem chore_residue_transport (V W B : Matrix Agent) (f : Equiv.Perm Agent)
    (hW : ChoreEF W) (hwhole : ∀ i j, W i (f j) = V i j + B i j)
    (i j : Agent) (r r' : ℝ) (hother : 0 ≤ B i j)
    (hold : r ≤ choreGap V i j) (hbudget : B i i + r' ≤ r) :
    r' ≤ choreGap W i (f j) := by
  have h := chore_whole_label_transport V W B f hW hwhole i j hother
  linarith

/-- Quarter expenditure keeps a participating observer's final residue strictly positive. -/
theorem quarter_leftover_positive (buffer used remaining : ℝ)
    (hb : 0 < buffer) (hused : used ≤ buffer / 4) (hpartition : used + remaining = buffer) :
    3 * buffer / 4 ≤ remaining ∧ 0 < remaining := by
  constructor <;> linarith

theorem repaired_witness_strict (buffer tolerance gap remaining : ℝ)
    (hb : 0 < buffer) (ht : tolerance < 3 / 4)
    (hgap : (7 / 4 - tolerance) * buffer ≤ gap) (hr : remaining ≤ buffer) :
    remaining < gap := by
  nlinarith

noncomputable def targets [Fintype Agent] (g : Matrix Agent) (r : Agent → ℝ)
    (i : Agent) : Finset Agent := by
  classical
  exact Finset.univ.filter (fun j => j ≠ i ∧ r i ≤ g i j)

theorem targets_proper [Fintype Agent] (g : Matrix Agent) (r : Agent → ℝ) :
    R2OnlinePotential.Proper (targets g r) := by
  classical
  intro i
  simp [targets]

theorem zero_row_saturated [Fintype Agent] [DecidableEq Agent] (g : Matrix Agent) (r : Agent → ℝ)
    (i : Agent) (hEF : ∀ j, 0 ≤ g i j) (hr : r i = 0) :
    targets g r i = Finset.univ.erase i := by
  classical
  ext j
  simp [targets, hr, hEF j]

/-- Only positive rows claim that every transported old target remains proper. -/
theorem positive_row_image_subset [Fintype Agent] [DecidableEq Agent] (g g' : Matrix Agent)
    (r r' : Agent → ℝ) (f : Equiv.Perm Agent) (i : Agent)
    (hpositive : 0 < r' i) (hself : g' i i = 0)
    (htransport : ∀ j ∈ targets g r i, r' i ≤ g' i (f j)) :
    (targets g r i).image f ⊆ targets g' r' i := by
  classical
  intro k hk
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
  have hm := htransport j hj
  have hne : f j ≠ i := by
    intro heq
    rw [heq, hself] at hm
    linarith
  simp [targets, hne, hm]

/-- Zero rows use saturation instead of a potentially false proper-target image inclusion. -/
theorem row_card_monotone [Fintype Agent] (g g' : Matrix Agent)
    (r r' : Agent → ℝ) (f : Equiv.Perm Agent)
    (hEF : ∀ i j, 0 ≤ g' i j) (hself : ∀ i, g' i i = 0)
    (hr' : ∀ i, 0 ≤ r' i)
    (htransport : ∀ i, 0 < r' i → ∀ j ∈ targets g r i, r' i ≤ g' i (f j))
    (i : Agent) : (targets g r i).card ≤ (targets g' r' i).card := by
  classical
  by_cases hi : 0 < r' i
  · have hsub := positive_row_image_subset g g' r r' f i hi (hself i) (htransport i hi)
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ f.injective] using hc
  · have hz : r' i = 0 := by have := hr' i; linarith
    rw [zero_row_saturated g' r' i (hEF i) hz]
    have hc := R2OnlinePotential.row_card_le (targets g r) (targets_proper g r) i
    simpa using hc

theorem fresh_positive_row_strict [Fintype Agent] (g g' : Matrix Agent)
    (r r' : Agent → ℝ) (f : Equiv.Perm Agent) (b h : Agent)
    (hpositive : 0 < r' b) (hself : g' b b = 0)
    (htransport : ∀ j ∈ targets g r b, r' b ≤ g' b (f j))
    (hfresh : h ∉ targets g r b) (hwitness : r' b ≤ g' b (f h)) :
    (targets g r b).card < (targets g' r' b).card := by
  classical
  have hsub := positive_row_image_subset g g' r r' f b hpositive hself htransport
  have hne : f h ≠ b := by
    intro heq
    rw [heq, hself] at hwitness
    linarith
  have hmem : f h ∈ targets g' r' b := by simp [targets, hne, hwitness]
  have hnot := R2OnlinePotential.fresh_target_not_in_image (targets g r) f b h hfresh
  have hstrict : (targets g r b).image f ⊂ targets g' r' b := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    exact hnot (by simpa only [heq] using hmem)
  have hc := Finset.card_lt_card hstrict
  simpa only [Finset.card_image_of_injective _ f.injective] using hc

theorem strict_global_progress [Fintype Agent] (g g' : Matrix Agent)
    (r r' : Agent → ℝ) (f : Equiv.Perm Agent)
    (hEF : ∀ i j, 0 ≤ g' i j) (hself : ∀ i, g' i i = 0)
    (hr' : ∀ i, 0 ≤ r' i)
    (htransport : ∀ i, 0 < r' i → ∀ j ∈ targets g r i, r' i ≤ g' i (f j))
    (b h : Agent) (hpositive : 0 < r' b)
    (hfresh : h ∉ targets g r b) (hwitness : r' b ≤ g' b (f h)) :
    R2OnlinePotential.potential (targets g r) + 1 ≤
      R2OnlinePotential.potential (targets g' r') := by
  classical
  apply Nat.succ_le_of_lt
  apply Finset.sum_lt_sum
  · intro i _
    exact row_card_monotone g g' r r' f hEF hself hr' htransport i
  · exact ⟨b, Finset.mem_univ b,
      fresh_positive_row_strict g g' r r' f b h hpositive (hself b)
        (htransport b hpositive) hfresh hwitness⟩

/-- Additive EF increments preserve the anchored targets without changing their labels. -/
theorem additive_targets_subset [Fintype Agent] (g g' : Matrix Agent)
    (r r' : Agent → ℝ) (hgap : ∀ i j, g i j ≤ g' i j)
    (hr : ∀ i, r' i ≤ r i) (i : Agent) : targets g r i ⊆ targets g' r' i := by
  classical
  intro j hj
  have hj' : j ≠ i ∧ r i ≤ g i j := by simpa [targets] using hj
  have hm : r' i ≤ g' i j := (hr i).trans (hj'.2.trans (hgap i j))
  simp [targets, hj'.1, hm]

/--
Identity whole-label transport preserves proper targets even in zero rows.
This is the global additive-commit interface: frozen/active gaps need not grow.
-/
theorem identity_targets_subset [Fintype Agent] (g g' : Matrix Agent)
    (r r' : Agent → ℝ)
    (htransport : ∀ i, ∀ j ∈ targets g r i, r' i ≤ g' i j)
    (i : Agent) : targets g r i ⊆ targets g' r' i := by
  classical
  intro j hj
  have hj' : j ≠ i ∧ r i ≤ g i j := by simpa [targets] using hj
  have hm := htransport i j hj
  simp [targets, hj'.1, hm]

/-- A zero-row early commit progresses from the saved anchor's missing edge. -/
theorem additive_zero_strict_progress [Fintype Agent] (g g' : Matrix Agent)
    (r r' : Agent → ℝ)
    (htransport : ∀ i, ∀ j ∈ targets g r i, r' i ≤ g' i j) (b h : Agent)
    (hEF : ∀ j, 0 ≤ g' b j) (hzero : r' b = 0)
    (hne : h ≠ b) (hmissing : h ∉ targets g r b) :
    R2OnlinePotential.potential (targets g r) + 1 ≤
      R2OnlinePotential.potential (targets g' r') := by
  classical
  apply Nat.succ_le_of_lt
  apply Finset.sum_lt_sum
  · intro i _
    exact Finset.card_le_card (identity_targets_subset g g' r r' htransport i)
  · refine ⟨b, Finset.mem_univ b, Finset.card_lt_card ?_⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨identity_targets_subset g g' r r' htransport b, ?_⟩
    intro heq
    apply hmissing
    rw [heq, zero_row_saturated g' r' b hEF hzero]
    simp [hne]

theorem global_potential_cap [Fintype Agent] (g : Matrix Agent) (r : Agent → ℝ) :
    R2OnlinePotential.potential (targets g r) ≤
      Fintype.card Agent * (Fintype.card Agent - 1) := by
  classical
  exact R2OnlinePotential.potential_le (targets g r) (targets_proper g r)

/-- Every row saturates when a globally EF allocation has no residue value. -/
theorem zero_residue_potential [Fintype Agent] (g : Matrix Agent) (r : Agent → ℝ)
    (hEF : ∀ i j, 0 ≤ g i j) (hr : ∀ i, r i = 0) :
    R2OnlinePotential.potential (targets g r) =
      Fintype.card Agent * (Fintype.card Agent - 1) := by
  classical
  unfold R2OnlinePotential.potential
  simp_rw [fun i => zero_row_saturated g r i (hEF i) (hr i)]
  simp

/--
Count only saved anchors at iteration starts, with the original Agent type.
The final iteration may terminate before producing another anchor. Provisional
snapshot potentials do not occur in the statement or in the proof.
-/
theorem anchored_iterations_le [Fintype Agent] (g : ℕ → Matrix Agent)
    (r : ℕ → Agent → ℝ) (rounds : ℕ)
    (hstep : ∀ t, t + 1 < rounds →
      R2OnlinePotential.potential (targets (g t) (r t)) + 1 ≤
        R2OnlinePotential.potential (targets (g (t + 1)) (r (t + 1))))
    (hmissing : ∀ t < rounds, ∃ a b, b ≠ a ∧ g t a b < r t a) :
    rounds ≤ Fintype.card Agent * (Fintype.card Agent - 1) := by
  classical
  apply R2OnlinePotential.all_rounds_le (fun t => targets (g t) (r t)) rounds
  · intro t _
    exact targets_proper (g t) (r t)
  · exact hstep
  · intro t ht
    obtain ⟨a, b, hne, hsmall⟩ := hmissing t ht
    refine ⟨a, b, hne, ?_⟩
    simp [targets, not_le.mpr hsmall]

/-- Non-counted freeze events may be interleaved, but they never reset the potential. -/
theorem interleaved_progress_bound (p charge : ℕ → ℕ) (events cap : ℕ)
    (hstep : ∀ t < events, p t + charge t ≤ p (t + 1)) (hcap : p events ≤ cap) :
    (∑ t ∈ Finset.range events, charge t) ≤ cap := by
  have hacc : p 0 + (∑ t ∈ Finset.range events, charge t) ≤ p events := by
    induction events with
    | zero => simp
    | succ events ih =>
      have hp := ih (fun t ht => hstep t (by omega))
      have hl := hstep events (by omega)
      rw [Finset.sum_range_succ]
      omega
  omega

/-- Regression: after a row reaches zero residue, an old proper target can map to self. -/
theorem zero_row_invalidates_universal_image :
    ¬ (targets (fun i j : Fin 2 => if i = j then 0 else 1) (fun _ => 1) 0).image
        (Equiv.swap (0 : Fin 2) 1) ⊆
      targets (fun _ _ : Fin 2 => 0) (fun _ => 0) 0 := by
  classical
  intro hsub
  have hold : (1 : Fin 2) ∈ targets (fun i j : Fin 2 => if i = j then 0 else 1)
      (fun _ => 1) 0 := by norm_num [targets]
  have himage : (0 : Fin 2) ∈
      (targets (fun i j : Fin 2 => if i = j then 0 else 1) (fun _ => 1) 0).image
        (Equiv.swap (0 : Fin 2) 1) := by
    exact Finset.mem_image.mpr ⟨1, hold, by simp⟩
  have hbad := hsub himage
  simp [targets] at hbad

/-- Zero-total public-basis perturbations have r(n-1) freely chosen coordinates. -/
theorem public_rank_coordinate_count (rank owners : ℕ) :
    Fintype.card (Fin rank × Fin (owners - 1)) = rank * (owners - 1) := by
  simp

/-- Fewer equations than public-model perturbation coordinates leave a rational kernel. -/
theorem public_rank_kernel (rank owners equations : ℕ)
    (L : (Fin (rank * (owners - 1)) → ℚ) →ₗ[ℚ] (Fin equations → ℚ))
    (hshort : equations < rank * (owners - 1)) :
    ∃ z, z ≠ 0 ∧ L z = 0 :=
  R3QueryLower.rational_kernel_exists (rank * (owners - 1)) equations L hshort

/-- One or several scalar equations per oracle call are accounted for explicitly. -/
theorem public_rank_query_count (rank owners equations queries perQuery : ℕ)
    (L : (Fin (rank * (owners - 1)) → ℚ) →ₗ[ℚ] (Fin equations → ℚ))
    (hcertificate : ∀ z, L z = 0 → z = 0)
    (hbudget : equations ≤ perQuery * queries) (hpositive : 0 < perQuery) :
    (rank * (owners - 1)) ⌈/⌉ perQuery ≤ queries := by
  have hdimension : rank * (owners - 1) ≤ equations := by
    by_contra hnot
    have hshort : equations < rank * (owners - 1) := by omega
    obtain ⟨z, hz, hLz⟩ := public_rank_kernel rank owners equations L hshort
    exact hz (hcertificate z hLz)
  exact (ceilDiv_le_iff_le_mul hpositive).2 (hdimension.trans hbudget)

#print axioms cake_guard_preserved
#print axioms chore_guard_preserved
#print axioms cake_global_EF
#print axioms chore_global_EF
#print axioms cake_whole_label_transport
#print axioms chore_whole_label_transport
#print axioms row_card_monotone
#print axioms strict_global_progress
#print axioms additive_zero_strict_progress
#print axioms anchored_iterations_le
#print axioms interleaved_progress_bound
#print axioms zero_row_invalidates_universal_image
#print axioms public_rank_query_count

end EnvyFreeResearch.R4GlobalPotential
