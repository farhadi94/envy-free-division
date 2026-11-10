import EnvyFreeResearch.ChoreComposition
import EnvyFreeResearch.Full.ChoresComponentGraph

/-!
Local reserve updates for a paid proposal that is not executed immediately.
The old owner permutation is kept.  Unlike `ChoresComponentFrames.advance`,
no common partition or cycle of proposals is needed for this update.

These are local ledger/graph statements, not an end-to-end query theorem.
-/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedChoresDeferredPayment
open ChoreComposition

variable {Agent Root : Type*} [DecidableEq Agent]

/-- Pay the proposal at `p` while retaining the actual owner matching. -/
def pay (f : Frame Agent Root) (C : Finset Agent) (p q : Agent) : Frame Agent Root :=
  { f with
    allowed := fun a => if a = p then insert q (f.allowed a) else f.allowed a
    forbidden := fun a => if a = p then f.forbidden a ∪ (C \ f.allowed a) else f.forbidden a
    frontierGap := fun i a => if a = p then f.gap i q a else f.frontierGap i a }

@[simp] theorem pay_owner (f : Frame Agent Root) (C : Finset Agent) (p q : Agent) :
    (pay f C p q).owner = f.owner := rfl

@[simp] theorem pay_allocation (f : Frame Agent Root) (C : Finset Agent) (p q : Agent) :
    (pay f C p q).allocation = f.allocation := rfl

theorem pay_good (f : Frame Agent Root) (hf : f.Good) (C : Finset Agent) (p q : Agent)
    (hequal : f.equalizerCost q p q = f.baseline q) : (pay f C p q).Good := by
  constructor
  · intro a
    by_cases h : a = p
    · simp only [pay, h, ite_true]
      exact Finset.mem_insert_of_mem (hf.1 p)
    · simpa only [pay, h, ite_false] using hf.1 a
  · intro a j hj
    by_cases h : a = p
    · subst a
      simp only [pay, ite_true, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hequal
      · exact hf.2 p j hj
    · exact hf.2 a j (by simpa only [pay, h, ite_false] using hj)

theorem reserve_other (f : Frame Agent Root) (C : Finset Agent) (p q a i j : Agent)
    (ha : a ≠ p) : (pay f C p q).reserve i j a = f.reserve i j a := by
  simp only [Frame.reserve, Frame.gap, pay, ha, ite_false]

theorem reserve_internal (f : Frame Agent Root) (C : Finset Agent) (p q i j : Agent)
    (hq : q ∉ C) (hj : j ∈ C) :
    (pay f C p q).reserve i j p ≤ f.reserve i j p := by
  simpa only [Frame.reserve, Frame.gap, pay, ite_true] using
    R7Chores.internal_skip_forbid_no_growth C (f.allowed p) (f.forbidden p)
      (fun j => f.gap i j p) (f.frontierGap i p) (f.gap i q p) q j hq hj

theorem reserve_external (f : Frame Agent Root) (C : Finset Agent) (p q i j : Agent)
    (ha : f.allowed p ⊆ C) (hf : f.forbidden p ⊆ C) (hj : j ∉ C) :
    (pay f C p q).reserve i j p = max 0 (f.gap i q p) := by
  simpa only [Frame.reserve, Frame.gap, pay, ite_true, R7Chores.clipped] using
    R7Chores.external_skip_forbid_reserve C (f.allowed p) (f.forbidden p)
      (fun j => f.gap i j p) (f.gap i q p) q j ha hf hj rfl

theorem reserve_protected (f : Frame Agent Root) (C : Finset Agent) (p q i j : Agent)
    (hnew : f.gap i q p ≤ 0)
    (hcontain : ∀ a ∈ f.allowed p, f.gap i a p ≤ f.gap i q p) :
    (pay f C p q).reserve i j p = 0 := by
  change R7Chores.recipientReserve _ _ _ _ _ = _
  simp only [pay, ite_true, Frame.gap]
  unfold R7Chores.recipientReserve R7Chores.clipped
  split_ifs with ha hf
  · rcases Finset.mem_insert.mp ha with rfl | ha
    · exact max_eq_left hnew
    · exact max_eq_left ((hcontain j ha).trans hnew)
  · rfl
  · exact max_eq_left hnew

/-- The concrete donor comparisons and the unused-parent threshold suffice
for payment; the target components and current owner matching are irrelevant.
The hypotheses concern the actual `Donation` values, not an assumed final
package invariant. -/
theorem exclusive_payment (s : Package Agent Root) (f : Frame Agent Root)
    (hs : s.live = some f) (donors : List (Donation Agent Root))
    (C : Finset Agent) (p q : Agent) (hq : q ∉ C)
    (ha : f.allowed p ⊆ C) (hf : f.forbidden p ⊆ C)
    (he : ∀ i j, j ∈ C → extras donors i j p ≤ payments donors i p)
    (heout : ∀ i j, j ∉ C → extras donors i j p = 0)
    (hthreshold : ∀ i, max 0 (f.gap i q p) ≤ payments donors i p)
    (hother : ∀ a, a ≠ p → ∀ i j, extras donors i j a = 0)
    (hpay : ∀ i a, 0 ≤ payments donors i a) :
    ExclusivePayment s donors (pay f C p q) := by
  intro i j a _
  by_cases hap : a = p
  · subst a
    by_cases hj : j ∈ C
    · refine Or.inl ⟨he i j hj, ?_⟩
      simpa only [Package.reserve, hs] using reserve_internal f C p q i j hq hj
    · refine Or.inr ⟨heout i j hj, ?_⟩
      rw [reserve_external f C p q i j ha hf hj]
      exact hthreshold i
  · refine Or.inl ⟨?_, ?_⟩
    · rw [hother a hap i j]
      exact hpay i a
    · rw [reserve_other f C p q a i j hap]
      simp only [Package.reserve, hs]
      exact le_rfl

theorem paid_package_valid (s : Package Agent Root) (hsvalid : s.Valid)
    (f : Frame Agent Root) (hs : s.live = some f)
    (donors : List (Donation Agent Root))
    (hd : ∀ d ∈ donors, d.WellFormed) (hv : ∀ d ∈ donors, d.package.Valid)
    (C : Finset Agent) (p q : Agent) (hq : q ∉ C)
    (ha : f.allowed p ⊆ C) (hf : f.forbidden p ⊆ C)
    (hequal : f.equalizerCost q p q = f.baseline q)
    (he : ∀ i j, j ∈ C → extras donors i j p ≤ payments donors i p)
    (heout : ∀ i j, j ∉ C → extras donors i j p = 0)
    (hthreshold : ∀ i, max 0 (f.gap i q p) ≤ payments donors i p)
    (hother : ∀ a, a ≠ p → ∀ i j, extras donors i j a = 0)
    (hpay : ∀ i a, 0 ≤ payments donors i a) :
    (mergeOpen s donors (pay f C p q)).Valid :=
  merge_open_valid s hsvalid donors hd hv _
    (pay_good f (hsvalid.live_good f hs) C p q hequal)
    (exclusive_payment s f hs donors C p q hq ha hf he heout hthreshold hother hpay)

/-- In an arbitrary directed graph, an edge used by a permitted permutation
has a return path. Thus a pending edge across distinct SCCs cannot be used by
any owner matching, even though it is already in the allowed-edge relation. -/
theorem matching_edge_strongly_connected [Finite Agent]
    (allowed : Agent → Agent → Prop) (owner : Equiv.Perm Agent)
    (hallowed : ∀ a, allowed a (owner a)) (a : Agent) :
    Relation.ReflTransGen allowed a (owner a) ∧
      Relation.ReflTransGen allowed (owner a) a := by
  refine ⟨.single (hallowed a), ?_⟩
  have he : Chores.Components.Edge [owner] a (owner a) := ⟨owner, by simp, rfl⟩
  have hr := Chores.Components.edge_reverse he
  have hmono : ∀ x y, Chores.Components.Edge [owner] x y → allowed x y := by
    intro x y h
    obtain ⟨σ, hσ, rfl⟩ := h
    have : σ = owner := by simpa using hσ
    subst σ
    exact hallowed x
  exact Relation.ReflTransGen.mono hmono _ _ hr

end EnvyFreeResearch.Full.RefinedChoresDeferredPayment

#print axioms EnvyFreeResearch.Full.RefinedChoresDeferredPayment.paid_package_valid
#print axioms EnvyFreeResearch.Full.RefinedChoresDeferredPayment.matching_edge_strongly_connected
