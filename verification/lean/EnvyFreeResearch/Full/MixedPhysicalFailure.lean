import EnvyFreeResearch.Full.MixedFrontier
import EnvyFreeResearch.Full.MixedObstruction
import EnvyFreeResearch.Full.IntervalAllocation

/-! General-n physical obstruction, with arbitrary finite output intervals.
This module connects constructed signed-density states to actual complete
allocations. It does not yet assert the randomized finite-horizon capture. -/

namespace EnvyFreeResearch.Full.MixedPhysicalFailure
open Set TranscriptAdversary MixedFrontier MixedObstruction IntervalAllocation

variable {Agent : Type*} [Fintype Agent]

theorem exists_two_nonowners (c : Agent) (hn : 3 ≤ Fintype.card Agent) :
    ∃ a b : Agent, a ≠ c ∧ b ≠ c ∧ a ≠ b := by
  classical
  have hcard : 1 < (Finset.univ.erase c).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  exact ⟨a, b, (Finset.mem_erase.mp ha).1, (Finset.mem_erase.mp hb).1, hab⟩

/-- Envy comparison on normalized positive-net profiles. -/
def ApproximateEF {α : ℝ} (S : State Agent α) (A : Allocation Agent) (ε : ℝ) : Prop :=
  ∀ i j, α * value (S.rows i) (A.share j) - value (S.rows i) (A.share i) ≤ ε

/-- Every complete finite-interval output whose proper endpoints have been
frozen violates at least one actual signed envy comparison. -/
theorem frozen_output_failure {α ε : ℝ} (S : State Agent α) (A : Allocation Agent)
    (hn : 3 ≤ Fintype.card Agent) (hα : 0 ≤ α) (hε : ε < α)
    (hleft : ∀ k, FrozenCoordinate S.frontier (A.left k))
    (hright : ∀ k, FrozenCoordinate S.frontier (A.right k)) :
    ¬ ApproximateEF S A ε := by
  obtain ⟨c, htail⟩ := A.exists_tail_owner S.frontier S.nonnegative S.proper hleft hright
  obtain ⟨a, b, hac, hbc, hab⟩ := exists_two_nonowners c hn
  have h := physical_violation (S.rows a) (S.rows b) α ε S.frontier
    (A.share a) (A.share b) (A.share c) hα hε
    (A.share_measurable a) (A.share_measurable b) (A.share_measurable c)
    (A.share_disjoint hab) (A.share_disjoint hac) (A.share_disjoint hbc)
    (S.ceiling a).1 (S.ceiling b).1 (S.prefix_coefficients a b hab) htail
  intro hef
  rcases h with h | h
  · exact (not_lt_of_ge (hef a c)) h
  · exact (not_lt_of_ge (hef b c)) h

end EnvyFreeResearch.Full.MixedPhysicalFailure
