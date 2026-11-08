import EnvyFreeResearch.Full.ChoresCore
import EnvyFreeResearch.Full.ChoresLocalMatching

/-!
# Hungry anchored existence from an actual compact maximum

The local matching theorem is applied to each strictly separated group of
nonwhole owners. It produces a larger envy-free endpoint vector, so a compact
maximizer admits no such group. Finite reachability then supplies the anchored
rank used by the concrete Core search.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Core

open Set Filter
open scoped BigOperators Topology

/-- Clipping extends each given continuous parent function to the real line. -/
lemma HungryCosts.continuous_clip {n : ℕ} (C : HungryCosts n) (i p : Fin n) :
    Continuous (fun x => C.cost i p (unitClip x)) :=
  (C.continuous i p).comp_continuous unitClip_continuous unitClip_mem

/-- The feasible EF endpoint vectors form a compact set: finitely many closed
matching constraints inside the actual endpoint cube. -/
theorem exists_maximal_state {n : ℕ} (C : HungryCosts n) :
    ∃ s : State n, Feasible s ∧ EnvyFree C.cost s ∧
      ∀ t : State n, Feasible t → EnvyFree C.cost t →
        (∑ p, t.endpoint p) ≤ ∑ p, s.endpoint p := by
  classical
  let E : Set (Fin n → ℝ) := {x | ∃ π : Equiv.Perm (Fin n),
    ∀ i p, C.cost i (π i) (unitClip (x (π i))) ≤ C.cost i p (unitClip (x p))}
  have hE : IsClosed E := by
    dsimp only [E]
    rw [ofPred_exists]
    apply isClosed_iUnion_of_finite
    intro π
    apply FixedPoint.closed_forall
    intro i
    apply FixedPoint.closed_forall
    intro p
    exact isClosed_le ((C.continuous_clip i (π i)).comp (continuous_apply _))
      ((C.continuous_clip i p).comp (continuous_apply _))
  let K : Set (Fin n → ℝ) := Icc 0 1 ∩ E
  have hK : IsCompact K := isCompact_Icc.inter_right hE
  have hne : K.Nonempty := by
    refine ⟨0, ⟨by intro p; norm_num, by intro p; norm_num⟩, Equiv.refl _, ?_⟩
    intro i p
    simp [unitClip, C.zero]
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (show ContinuousOn (fun x => ∑ p, x p) K by fun_prop)
  obtain ⟨π, hπ⟩ := hx.2
  have hxbound : ∀ p, x p ∈ Icc (0 : ℝ) 1 := fun p => ⟨hx.1.1 p, hx.1.2 p⟩
  refine ⟨⟨x, π⟩, hxbound, ?_, ?_⟩
  · intro i p
    simpa only [unitClip_eq (hxbound _)] using hπ i p
  · intro t ht hEF
    apply hmax
    refine ⟨⟨fun p => (ht p).1, fun p => (ht p).2⟩, t.matching, ?_⟩
    intro i p
    simpa only [unitClip_eq (ht _)] using hEF i p

/-- A finite collection of old strict gaps stays strict after sufficiently
small growth of any currently tied parent. Endpoint slack is included in the
same neighborhood, so the later local matching stays on physical parents. -/
theorem exists_improvement_radius {n : ℕ} (C : HungryCosts n) (s : State n)
    (hs : Feasible s) (S : Finset (Fin n))
    (hwhole : ∀ i ∈ S, s.endpoint (s.matching i) < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ j ∈ S, s.endpoint (s.matching j) + δ < 1) ∧
      ∀ i ∈ S, ∀ j ∈ S, ∀ p,
        C.cost i (s.matching j) (s.endpoint (s.matching j)) =
          C.cost i (s.matching i) (s.endpoint (s.matching i)) →
        C.cost i (s.matching i) (s.endpoint (s.matching i)) < C.cost i p (s.endpoint p) →
        C.cost i (s.matching j) (s.endpoint (s.matching j) + δ) < C.cost i p (s.endpoint p) := by
  classical
  have hslack : ∀ᶠ δ : ℝ in 𝓝 0, ∀ j ∈ S, s.endpoint (s.matching j) + δ < 1 := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro hj
    exact (show ContinuousAt (fun δ : ℝ => s.endpoint (s.matching j) + δ) 0 by fun_prop).eventually_lt
      continuousAt_const (by simpa using hwhole j hj)
  have hgaps : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i ∈ S, ∀ j ∈ S, ∀ p,
      C.cost i (s.matching j) (s.endpoint (s.matching j)) =
        C.cost i (s.matching i) (s.endpoint (s.matching i)) →
      C.cost i (s.matching i) (s.endpoint (s.matching i)) < C.cost i p (s.endpoint p) →
      C.cost i (s.matching j) (unitClip (s.endpoint (s.matching j) + δ)) < C.cost i p (s.endpoint p) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro _
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro _
    apply Filter.eventually_all.mpr
    intro p
    apply Filter.eventually_all.mpr
    intro htie
    apply Filter.eventually_all.mpr
    intro hgap
    apply ((C.continuous_clip i (s.matching j)).comp
      (show Continuous (fun δ : ℝ => s.endpoint (s.matching j) + δ) by fun_prop)).continuousAt.eventually_lt continuousAt_const
    simpa only [Function.comp_apply, add_zero, unitClip_eq (hs _), htie] using hgap
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp (hslack.and hgaps)
  have hsmall : dist (ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨hslack', hgaps'⟩ := hεspec hsmall
  refine ⟨ε / 2, half_pos hε, hslack', ?_⟩
  intro i hi j hj p htie hgap
  have hcap : s.endpoint (s.matching j) + ε / 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨add_nonneg (hs _).1 (half_pos hε).le, (hslack' j hj).le⟩
  simpa only [unitClip_eq hcap] using hgaps' i hi j hj p htie hgap

/-- A strictly separated nonwhole group admits an actual larger EF state.
The new ownership permutation is extended by the identity outside the group. -/
theorem improve_separated_group {n : ℕ} (C : HungryCosts n) (s : State n)
    (hs : Feasible s) (hEF : EnvyFree C.cost s) (S : Finset (Fin n)) (hne : S.Nonempty)
    (hwhole : ∀ i ∈ S, s.endpoint (s.matching i) < 1)
    (hsep : ∀ i ∈ S, ∀ j ∉ S,
      C.cost i (s.matching i) (s.endpoint (s.matching i)) <
        C.cost i (s.matching j) (s.endpoint (s.matching j))) :
    ∃ t : State n, Feasible t ∧ EnvyFree C.cost t ∧
      (∑ p, s.endpoint p) < ∑ p, t.endpoint p := by
  classical
  let : Nonempty S := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨δ, hδ, hcap, hgap⟩ := exists_improvement_radius C s hs S hwhole
  let b := fun i => C.cost i (s.matching i) (s.endpoint (s.matching i))
  let allowed := fun i j : S => C.cost i (s.matching j) (s.endpoint (s.matching j)) = b i
  let f := fun i j : S => fun z => C.cost i (s.matching j) (s.endpoint (s.matching j) + z) - b i
  have hphysical (j : S) {z : ℝ} (hz : z ∈ Icc 0 δ) :
      s.endpoint (s.matching j) + z ∈ Icc (0 : ℝ) 1 := by
    refine ⟨add_nonneg (hs _).1 hz.1, ?_⟩
    linarith only [hz.2, hcap j j.property]
  have hfcont : ∀ i j, ContinuousOn (f i j) (Icc 0 δ) := by
    intro i j
    exact ((C.continuous i (s.matching j)).comp (by fun_prop)
      (fun _ hz => hphysical j hz)).sub continuousOn_const
  have hfzero : ∀ i j, allowed i j → f i j 0 = 0 := by
    intro i j hij
    simpa [f, add_zero] using sub_eq_zero.mpr hij
  have hfstrict : ∀ i j, allowed i j → StrictMonoOn (f i j) (Icc 0 δ) := by
    intro i j _ a ha z hz haz
    exact sub_lt_sub_right ((C.strict i (s.matching j)) (hphysical j ha)
      (hphysical j hz) (by linarith only [haz])) _
  obtain ⟨y, hy, hysum, π, hπ⟩ := local_matching δ hδ f hfcont allowed
    (fun _ => rfl) hfzero hfstrict
  let inc := fun i : Fin n => if h : i ∈ S then y ⟨i, h⟩ else 0
  let ρ : Equiv.Perm (Fin n) := π.subtypeCongr (Equiv.refl _)
  let t : State n := ⟨fun p => s.endpoint p + inc (s.matching.symm p), ρ.trans s.matching⟩
  have hinc (i : Fin n) : 0 ≤ inc i := by
    by_cases hi : i ∈ S
    · simpa [inc, hi] using (hy ⟨i, hi⟩).1
    · simp [inc, hi]
  have htend (j : Fin n) :
      t.endpoint (s.matching j) = s.endpoint (s.matching j) + inc j := by simp [t]
  have htendS (j : S) :
      t.endpoint (s.matching j) = s.endpoint (s.matching j) + y j := by
    rw [htend]
    simp [inc, j.property]
  have htmatchS (i : S) : t.matching i = s.matching (π i) := by
    change s.matching (ρ i) = _
    rw [Equiv.Perm.subtypeCongr.left_apply π (Equiv.refl _) i.property]
  have htmatchN (i : Fin n) (hi : i ∉ S) : t.matching i = s.matching i := by
    change s.matching (ρ i) = _
    rw [Equiv.Perm.subtypeCongr.right_apply π (Equiv.refl _) hi]
    rfl
  have htbound : Feasible t := by
    intro p
    obtain ⟨j, rfl⟩ := s.matching.surjective p
    by_cases hj : j ∈ S
    · rw [htendS ⟨j, hj⟩]
      exact hphysical ⟨j, hj⟩ (hy ⟨j, hj⟩)
    · rw [htend]
      simpa [inc, hj] using hs (s.matching j)
  have hmono (i : Fin n) (p : Fin n) :
      C.cost i p (s.endpoint p) ≤ C.cost i p (t.endpoint p) := by
    apply (C.strict i p).monotoneOn (hs p) (htbound p)
    exact le_add_of_nonneg_right (hinc _)
  have htEF : EnvyFree C.cost t := by
    intro i p
    by_cases hi : i ∈ S
    · let a : S := ⟨i, hi⟩
      rw [htmatchS a, htendS (π a)]
      obtain ⟨j, rfl⟩ := s.matching.surjective p
      by_cases htie : C.cost i (s.matching j) (s.endpoint (s.matching j)) = b i
      · have hj : j ∈ S := by
          by_contra hj
          have h := hsep i hi j hj
          change b i < _ at h
          rw [htie] at h
          exact (lt_irrefl _ h)
        rw [htendS ⟨j, hj⟩]
        have hm := (hπ a).2 ⟨j, hj⟩ htie
        exact (sub_le_sub_iff_right (b i)).mp hm
      · have hg : b i < C.cost i (s.matching j) (s.endpoint (s.matching j)) :=
          lt_of_le_of_ne (hEF i (s.matching j)) (Ne.symm htie)
        have hg' := hgap i hi (π a) (π a).property (s.matching j) (hπ a).1 hg
        apply le_trans (le_trans ?_ hg'.le) (hmono i (s.matching j))
        exact (C.strict i (s.matching (π a))).monotoneOn
          (hphysical (π a) (hy (π a))) (hphysical (π a) ⟨hδ.le, le_rfl⟩)
          (by linarith only [(hy (π a)).2])
    · rw [htmatchN i hi, htend]
      simp only [inc, dite_eq_right hi, add_zero]
      exact (hEF i p).trans (hmono i p)
  have hincsum : (∑ i, inc i) = δ := by
    calc
      (∑ i, inc i) = ∑ i ∈ S, inc i := (Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi => by simp [inc, hi])).symm
      _ = ∑ i : S, inc i := Finset.sum_subtype S (fun _ => Iff.rfl) inc
      _ = ∑ i : S, y i := by apply Finset.sum_congr rfl; intro i _; simp [inc, i.property]
      _ = δ := hysum
  refine ⟨t, htbound, htEF, ?_⟩
  change (∑ p, s.endpoint p) < (∑ p, (s.endpoint p + inc (s.matching.symm p)))
  rw [Finset.sum_add_distrib, s.matching.symm.sum_comp inc, hincsum]
  linarith

/-- Every nonempty owner group in a maximal state contains a whole owner or
an owner tied to an already external parent. -/
theorem maximal_group_anchor {n : ℕ} (C : HungryCosts n) (s : State n)
    (hs : Feasible s) (hEF : EnvyFree C.cost s)
    (hmax : ∀ t : State n, Feasible t → EnvyFree C.cost t →
      (∑ p, t.endpoint p) ≤ ∑ p, s.endpoint p) :
    ∀ S : Finset (Fin n), S.Nonempty → ∃ i ∈ S,
      s.endpoint (s.matching i) = 1 ∨ ∃ j ∉ S,
        C.cost i (s.matching j) (s.endpoint (s.matching j)) =
          C.cost i (s.matching i) (s.endpoint (s.matching i)) := by
  intro S hne
  by_contra h
  have hno : ∀ i ∈ S, s.endpoint (s.matching i) ≠ 1 ∧ ∀ j ∉ S,
      C.cost i (s.matching j) (s.endpoint (s.matching j)) ≠
        C.cost i (s.matching i) (s.endpoint (s.matching i)) := by
    intro i hi
    constructor
    · intro hw
      exact h ⟨i, hi, Or.inl hw⟩
    · intro j hj htie
      exact h ⟨i, hi, Or.inr ⟨j, hj, htie⟩⟩
  have hwhole : ∀ i ∈ S, s.endpoint (s.matching i) < 1 :=
    fun i hi => lt_of_le_of_ne (hs _).2 (hno i hi).1
  have hsep : ∀ i ∈ S, ∀ j ∉ S,
      C.cost i (s.matching i) (s.endpoint (s.matching i)) <
        C.cost i (s.matching j) (s.endpoint (s.matching j)) := by
    intro i hi j hj
    exact lt_of_le_of_ne (hEF i _) (Ne.symm ((hno i hi).2 j hj))
  obtain ⟨t, ht, htEF, hlt⟩ := improve_separated_group C s hs hEF S hne hwhole hsep
  exact (not_lt_of_ge (hmax t ht htEF)) hlt

/-- Length-bounded reachability from a whole parent along owner tie edges. -/
def Reached {n : ℕ} (cost : Fin n → Fin n → ℝ → ℝ) (s : State n) : ℕ → Fin n → Prop
  | 0, i => s.endpoint (s.matching i) = 1
  | k + 1, i => s.endpoint (s.matching i) = 1 ∨ ∃ j, Reached cost s k j ∧
      cost i (s.matching j) (s.endpoint (s.matching j)) =
        cost i (s.matching i) (s.endpoint (s.matching i))

/-- The finite group condition yields the actual strictly decreasing natural
rank required by `Anchored`, rather than an assumed ordering witness. -/
theorem anchored_of_group {n : ℕ} (cost : Fin n → Fin n → ℝ → ℝ) (s : State n)
    (hgroup : ∀ S : Finset (Fin n), S.Nonempty → ∃ i ∈ S,
      s.endpoint (s.matching i) = 1 ∨ ∃ j ∉ S,
        cost i (s.matching j) (s.endpoint (s.matching j)) =
          cost i (s.matching i) (s.endpoint (s.matching i))) : Anchored cost s := by
  classical
  have hreach : ∀ i, ∃ k, Reached cost s k i := by
    intro i
    by_contra hi
    let S := Finset.univ.filter (fun j => ¬∃ k, Reached cost s k j)
    have hne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    obtain ⟨j, hj, hw | ⟨k, hk, htie⟩⟩ := hgroup S hne
    · have hj' : ¬∃ a, Reached cost s a j := (Finset.mem_filter.mp hj).2
      exact hj' ⟨0, hw⟩
    · have hk' : ∃ a, Reached cost s a k := by simpa only [S, Finset.mem_filter,
        Finset.mem_univ, true_and, not_not] using hk
      obtain ⟨a, ha⟩ := hk'
      have hj' : ¬∃ a, Reached cost s a j := (Finset.mem_filter.mp hj).2
      exact hj' ⟨a + 1, Or.inr ⟨k, ha, htie⟩⟩
  let rank := fun i => Nat.find (hreach i)
  refine ⟨rank, ?_⟩
  intro i
  by_cases hw : s.endpoint (s.matching i) = 1
  · exact Or.inl hw
  · right
    have hr : Reached cost s (rank i) i := Nat.find_spec (hreach i)
    cases heq : rank i with
    | zero =>
      rw [heq] at hr
      exact (hw hr).elim
    | succ k =>
      rw [heq] at hr
      obtain ⟨j, hj, htie⟩ := hr.resolve_left hw
      refine ⟨j, ?_, htie⟩
      exact Nat.lt_succ_of_le (Nat.find_min' (hreach j) hj)

/-- Unconditional hungry anchored existence for every finite balanced parent
problem. Every analytic and combinatorial existence obligation is discharged. -/
theorem exists_anchored_state {n : ℕ} (C : HungryCosts n) :
    ∃ s : State n, Feasible s ∧ EnvyFree C.cost s ∧ Anchored C.cost s := by
  obtain ⟨s, hs, hEF, hmax⟩ := exists_maximal_state C
  exact ⟨s, hs, hEF, anchored_of_group C.cost s (maximal_group_anchor C s hs hEF hmax)⟩

/-- The actual finite Core candidate search succeeds on every hungry profile,
for every legal trim selector. Its returned vector dominates every feasible EF
vector. Memoization and physical query counts are separate from this theorem. -/
theorem solve_complete (n : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) (hcut : CutSpec C cut) :
    ∃ s, solve n C cut = some s ∧ Feasible s ∧ EnvyFree C.cost s ∧
      Anchored C.cost s ∧
      ∀ t : State n, Feasible t → EnvyFree C.cost t → ∀ p, t.endpoint p ≤ s.endpoint p := by
  obtain ⟨w, hw, hEFw, haw⟩ := exists_anchored_state C
  obtain ⟨s, hsolve, hs, hEF, ha, _⟩ := solve_complete_from_anchored n C cut hcut w hw hEFw haw
  exact ⟨s, hsolve, hs, hEF, ha, fun t ht hEFt => anchored_dominates C s t hs ht hEF hEFt ha⟩

end EnvyFreeResearch.Full.Chores.Core
