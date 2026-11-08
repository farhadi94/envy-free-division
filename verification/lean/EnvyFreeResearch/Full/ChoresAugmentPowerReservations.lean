import EnvyFreeResearch.Full.ChoresAugmentReservations
import EnvyFreeResearch.Full.ChoresAugmentReverseData
import Mathlib.Data.List.Nodup

/-! The actual forward reservation program supplies every hypothesis needed
by reverse augmentation. All remaining public identities and reservation
lists are disjoint sublists of the original labelled pieces. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Label : Type*} [LinearOrder Label]

def powerReservations (recipient : ℕ → Fin n) (k : ℕ) (original : Label → List (Parent n))
    (initial : List Label) : Reservations ℕ Label :=
  reserveAll (fun i p => OrderedUnion.cachedValue (original p) (recipient i))
    (fun i => 2^i) (List.range k) initial

theorem list_totalQuota (k : ℕ) : ((List.range k).map (fun i => (2 : ℕ)^i)).sum=totalQuota k := by
  induction k with
  | zero => simp [totalQuota]
  | succ k ih => rw [List.sum_range_succ,totalQuota_succ,ih]

theorem pairwise_disjoint_of_mem {α β : Type*} {xs : List α} (f : α → List β)
    (hp : xs.Pairwise (fun i j => List.Disjoint (f i) (f j)))
    {i j : α} (hi : i ∈ xs) (hj : j ∈ xs) (hne : i ≠ j) : List.Disjoint (f i) (f j) := by
  obtain ⟨a,ha⟩ := List.mem_iff_get.mp hi
  obtain ⟨b,hb⟩ := List.mem_iff_get.mp hj
  have hab : a ≠ b := fun h => hne (ha.symm.trans (h ▸ hb))
  rcases lt_or_gt_of_ne hab with h | h
  · simpa only [ha,hb] using hp.rel_get_of_lt h
  · exact (by simpa only [ha,hb] using hp.rel_get_of_lt h : List.Disjoint (f j) (f i)).symm

theorem power_reservations_correct (recipient : ℕ → Fin n) (k : ℕ)
    (original : Label → List (Parent n)) (initial : List Label)
    (hnd : initial.Nodup) (hlen : initial.length=2^(k+1)) :
    let out := powerReservations recipient k original initial
    out.available.Nodup ∧ out.available.length=2^k+1 ∧
      (∀ i < k, (out.reserved i).length=2^i ∧ (out.reserved i).Nodup) ∧
      (∀ i < k, ∀ r ∈ out.reserved i, ∀ p ∈ out.available, r ≠ p) ∧
      (∀ i < k, ∀ j < k, i ≠ j → ∀ r ∈ out.reserved i, ∀ s ∈ out.reserved j, r ≠ s) ∧
      (∀ i < k, ∀ p ∈ out.available, ∀ r ∈ out.reserved i,
        OrderedUnion.cachedValue (original p) (recipient i) ≤ OrderedUnion.cachedValue (original r) (recipient i)) := by
  have hbudget : ((List.range k).map (fun i => (2 : ℕ)^i)).sum ≤ initial.length := by
    rw [list_totalQuota,hlen,pow_succ]
    have h := totalQuota_add_one k
    omega
  let out := powerReservations recipient k original initial
  obtain ⟨hcounts,houtside,hperm,htotal,hdom⟩ :=
    reserve_all_correct (fun i p => OrderedUnion.cachedValue (original p) (recipient i))
      (fun i => 2^i) (List.range k) initial List.nodup_range hnd hbudget
  change ((List.range k).flatMap out.reserved++out.available).Perm initial at hperm
  change out.available.length+((List.range k).map (fun i => (2 : ℕ)^i)).sum=initial.length at htotal
  have hfullnd := hperm.nodup_iff.mpr hnd
  obtain ⟨hflatnd,havailnd,hdis⟩ := List.nodup_append.mp hfullnd
  obtain ⟨hresnd,hresdis⟩ := List.nodup_flatMap.mp hflatnd
  refine ⟨havailnd,?_,?_,?_,?_,?_⟩
  · change out.available.length=2^k+1
    rw [list_totalQuota,hlen,pow_succ] at htotal
    have h := totalQuota_add_one k
    omega
  · intro i hi
    exact ⟨hcounts i (List.mem_range.mpr hi),hresnd i (List.mem_range.mpr hi)⟩
  · intro i hi r hr p hp heq
    have hm : r ∈ (List.range k).flatMap out.reserved := List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hr⟩
    exact hdis r hm p hp heq
  · intro i hi j hj hij r hr s hs heq
    have hd := pairwise_disjoint_of_mem out.reserved hresdis (List.mem_range.mpr hi) (List.mem_range.mpr hj) hij
    exact List.disjoint_left.mp hd hr (heq.symm ▸ hs)
  · intro i hi p hp r hr
    exact hdom i (List.mem_range.mpr hi) r hr p hp

end EnvyFreeResearch.Full.Chores.Augment
