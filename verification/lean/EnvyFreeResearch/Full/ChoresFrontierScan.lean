import EnvyFreeResearch.Full.ChoresFrontierTail
import EnvyFreeResearch.Full.ChoresFrontierStop

/-! The cached scan selects the largest remaining non-small original atom.
Its absence certifies an entirely small suffix. Original gap and atom
separation are explicit inputs supplied by clearance, not by the scan. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open scoped Classical

variable {n : ℕ}

def Small (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) (a : Fin n) : Prop :=
  ∀ i, w i a ≤ r i/H

def AtomSeparated (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) : Prop :=
  ∀ i a, w i a ≤ r i/H ∨ H*r i ≤ w i a

def GapSeparated (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ) : Prop :=
  ∀ i, tailCost w i (rank i) ≤ r i/H ∨ H*r i ≤ tailCost w i (rank i)

def eligible (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => tailCost w i (rank i) ≤ r i/H)

def largeMask (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) (a : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => H*r i ≤ w i a)

def badAtoms (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => t ≤ a.val ∧ ¬ Small w r H a)

def largestBad (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) (t : ℕ) : Option (Fin n) :=
  if h : (badAtoms w r H t).Nonempty then some ((badAtoms w r H t).max' h) else none

theorem mem_eligible (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ) (i : Fin n) :
    i ∈ eligible w rank r H ↔ tailCost w i (rank i) ≤ r i/H := by simp [eligible]

theorem mem_largeMask (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) (a i : Fin n) :
    i ∈ largeMask w r H a ↔ H*r i ≤ w i a := by simp [largeMask]

theorem omitted_gap_large (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (hsep : GapSeparated w rank r H) (i : Fin n) (hi : i ∉ eligible w rank r H) :
    H*r i ≤ tailCost w i (rank i) :=
  (hsep i).resolve_left (fun h => hi ((mem_eligible w rank r H i).mpr h))

theorem owner_eligible (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (owner : Fin n) (howner : rank owner=n) (hr : 0 ≤ r owner) (hH : 0 < H) :
    owner ∈ eligible w rank r H := by
  rw [mem_eligible,howner,tail_end]
  exact div_nonneg hr hH.le

theorem largeMask_nonempty (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ)
    (hsep : AtomSeparated w r H) (a : Fin n) (hbad : ¬ Small w r H a) :
    (largeMask w r H a).Nonempty := by
  obtain ⟨i,hi⟩ := not_forall.mp hbad
  exact ⟨i,(mem_largeMask w r H a i).mpr ((hsep i a).resolve_left hi)⟩

theorem outside_mask_small (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ)
    (hsep : AtomSeparated w r H) (a i : Fin n) (hi : i ∉ largeMask w r H a) : w i a ≤ r i/H :=
  (hsep i a).resolve_right (fun h => hi ((mem_largeMask w r H a i).mpr h))

theorem largestBad_some (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) (t : ℕ)
    (a : Fin n) (ha : largestBad w r H t=some a) :
    t ≤ a.val ∧ ¬ Small w r H a ∧ ∀ b : Fin n, a < b → Small w r H b := by
  unfold largestBad at ha
  split_ifs at ha with h
  · have heq : (badAtoms w r H t).max' h=a := Option.some.inj ha
    have hmem : a ∈ badAtoms w r H t := heq ▸ Finset.max'_mem _ h
    obtain ⟨_,ht,hbad⟩ := Finset.mem_filter.mp hmem
    refine ⟨ht,hbad,?_⟩
    intro b hab
    by_contra hb
    have hbmem : b ∈ badAtoms w r H t := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,by change a.val < b.val at hab; exact ⟨ht.trans hab.le,hb⟩⟩
    have hle : b ≤ a := heq ▸ Finset.le_max' _ b hbmem
    exact not_lt_of_ge hle hab

theorem largestBad_none (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ) (t : ℕ)
    (ha : largestBad w r H t=none) : ∀ a : Fin n, t ≤ a.val → Small w r H a := by
  unfold largestBad at ha
  split_ifs at ha with h
  · intro a ht
    by_contra hb
    exact h ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht,hb⟩⟩

end EnvyFreeResearch.Full.Chores.Frontier
