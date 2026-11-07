import EnvyFreeResearch.R3ChoreAncestry

/-!
# Round 5: visited-matching and reserve certificates

These finite theorems connect an admissible matching of visited owner--piece
pairs to exact own values and the existing paid-frontier reserves. The model
uses the actual recorded prefix cost table. Physical interval restoration,
nonatomic Cut realization, mask extraction and the complete query theorem
remain separate written proofs.
-/

namespace EnvyFreeResearch.R5ChoreMatching

open scoped BigOperators

def reserve (cost : ℕ → ℝ) (baseline : ℝ) (position frontier : ℕ) : ℝ :=
  max 0 (baseline - cost (min position frontier))

theorem visited_reserve_exact (cost : ℕ → ℝ) (baseline : ℝ)
    (position frontier : ℕ) (hvisited : position ≤ frontier) :
    reserve cost baseline position frontier = max 0 (baseline - cost position) := by
  simp [reserve, Nat.min_eq_left hvisited]

/-- Advancing a paid frontier only spends the cost of the new segment. -/
theorem frontier_reserve_growth (baseline oldCost newCost segment : ℝ)
    (hsegment : oldCost - newCost ≤ segment) (hnonnegative : 0 ≤ segment) :
    max 0 (baseline - newCost) ≤ max 0 (baseline - oldCost) + segment := by
  apply max_le
  · have h := le_max_left (0 : ℝ) (baseline - oldCost)
    linarith
  · have h := le_max_right (0 : ℝ) (baseline - oldCost)
    linarith

variable {Agent : Type*}

/-- Actual live value after assigning each label through a permutation. -/
def liveValue (pieceCost : Agent → Agent → ℕ → ℝ)
    (position : Agent → Agent → ℕ) (π : Equiv.Perm Agent)
    (observer recipient : Agent) : ℝ :=
  pieceCost observer (π.symm recipient) (position (π.symm recipient) recipient)

theorem visited_matching_own_value (pieceCost : Agent → Agent → ℕ → ℝ)
    (position : Agent → Agent → ℕ) (frontier : Agent → ℕ)
    (baseline : Agent → ℝ) (π : Equiv.Perm Agent)
    (hmatching : ∀ p, position p (π p) ≤ frontier p)
    (hequalizer : ∀ i p, position p i ≤ frontier p →
      pieceCost i p (position p i) = baseline i) (i : Agent) :
    liveValue pieceCost position π i i = baseline i := by
  apply hequalizer
  simpa using hmatching (π.symm i)

/-- No earlier *complete* permutation is needed: pairwise visitation suffices. -/
theorem visited_matching_deficit (pieceCost : Agent → Agent → ℕ → ℝ)
    (position : Agent → Agent → ℕ) (frontier : Agent → ℕ)
    (baseline : Agent → ℝ) (π : Equiv.Perm Agent)
    (hmatching : ∀ p, position p (π p) ≤ frontier p) (i j : Agent) :
    max 0 (baseline i - liveValue pieceCost position π i j) =
      reserve (pieceCost i (π.symm j)) (baseline i)
        (position (π.symm j) j) (frontier (π.symm j)) := by
  have h : position (π.symm j) j ≤ frontier (π.symm j) := by
    simpa using hmatching (π.symm j)
  simp [liveValue, reserve, Nat.min_eq_left h]

/-- A future observer's equalizer lies inside every retained paid prefix. -/
theorem future_observer_no_deficit (cost : ℕ → ℝ) (baseline : ℝ)
    (cutoff observerMark : ℕ) (horder : cutoff ≤ observerMark)
    (hcost : Antitone cost) (hequalizer : cost observerMark = baseline) :
    max 0 (baseline - cost cutoff) = 0 := by
  have h := hcost horder
  rw [hequalizer] at h
  exact max_eq_left (sub_nonpos.mpr h)

/-- Closing the live root consumes its own reserve and adds no own credit. -/
theorem close_root_reserve (credit frozenDeficit liveReserve actualDeficit : ℝ)
    (hold : frozenDeficit + liveReserve ≤ credit)
    (hactual : actualDeficit ≤ liveReserve) :
    frozenDeficit + actualDeficit ≤ credit := by linarith

/-- A matching reset preserves aggregate own cost through the exact baselines. -/
theorem frozen_plus_live_own_identity (frozenOwn frozenBaseline liveBaseline credit liveOwn : ℝ)
    (hfrozen : frozenOwn = frozenBaseline - credit)
    (hlive : liveOwn = liveBaseline) :
    frozenOwn + liveOwn = frozenBaseline + liveBaseline - credit := by
  linarith

/-- Old live-root reserves pay every root closed during filtering or merging. -/
theorem close_many_reserves {Root : Type*} (S : Finset Root)
    (credit deficit oldReserve actualDeficit : Root → ℝ)
    (hold : ∀ s ∈ S, deficit s + oldReserve s ≤ credit s)
    (hactual : ∀ s ∈ S, actualDeficit s ≤ oldReserve s) :
    (∑ s ∈ S, (deficit s + actualDeficit s)) ≤ ∑ s ∈ S, credit s := by
  apply Finset.sum_le_sum
  intro s hs
  exact close_root_reserve _ _ _ _ (hold s hs) (hactual s hs)

/-- The local large-gap/small-atom contradiction used for omitted marks. -/
theorem omitted_mark_contradiction (n r H gap : ℝ)
    (hr : 0 < r) (hH : 0 < H) (hscale : n < H * H)
    (hlarge : H * r ≤ gap) (hsmall : gap ≤ n * r / H) : False := by
  have hgap : gap * H ≤ n * r := (le_div_iff₀ hH).mp hsmall
  have hmul : H * r * H ≤ gap * H := mul_le_mul_of_nonneg_right hlarge (le_of_lt hH)
  nlinarith

/-- A positive atom inside the next observer's small suffix cannot mask her. -/
theorem next_observer_not_masked (r H atom gap : ℝ)
    (hr : 0 < r) (hH : 1 < H)
    (hcontained : atom ≤ gap) (hgap : gap ≤ r / H) : ¬ H * r ≤ atom := by
  intro hlarge
  have hpos : 0 < H := lt_trans zero_lt_one hH
  have hsmall : atom * H ≤ r := (le_div_iff₀ hpos).mp (hcontained.trans hgap)
  have hmul : H * r * H ≤ atom * H := mul_le_mul_of_nonneg_right hlarge (le_of_lt hpos)
  have hstep : r < H * r := by
    simpa using (mul_lt_mul_of_pos_right hH hr)
  have hsecond : H * r < H * r * H := by
    simpa [mul_comm] using (mul_lt_mul_of_pos_right hH (mul_pos hpos hr))
  exact (not_lt_of_ge (hmul.trans hsmall)) (hstep.trans hsecond)

/-- One intact large atom pays the mask bound even when source indices differ. -/
theorem one_whole_large_atom {Donor : Type*} (S : Finset Donor)
    (removed : Donor → ℝ) (threshold : ℝ)
    (hnonnegative : ∀ d ∈ S, 0 ≤ removed d)
    (w : Donor) (hw : w ∈ S) (hwhole : threshold ≤ removed w) :
    threshold ≤ ∑ d ∈ S, removed d := by
  exact hwhole.trans (Finset.single_le_sum hnonnegative hw)

/-- Off the common mask, every individual removal has a small-atom bound. -/
theorem sum_small_removals {Donor : Type*} (S : Finset Donor)
    (removed : Donor → ℝ) (small : ℝ)
    (hsmall : ∀ d ∈ S, removed d ≤ small) :
    (∑ d ∈ S, removed d) ≤ S.card * small := by
  calc
    (∑ d ∈ S, removed d) ≤ ∑ _d ∈ S, small := Finset.sum_le_sum hsmall
    _ = S.card * small := by simp

end EnvyFreeResearch.R5ChoreMatching
