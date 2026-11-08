import EnvyFreeResearch.Full.ChoresAugmentReverseInvariant

/-! Total query-free bundle selection from the computed designation lists.
Its correctness is derived from the executed reverse-loop invariant. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Label : Type*} [LinearOrder Label]

def selectFresh (D : ℕ → Finset Label) (i : ℕ) (fallback : Label) : Label :=
  if h : (freshSet D i).Nonempty then (freshSet D i).min' h else fallback

theorem selectFresh_eq (D : ℕ → Finset Label) (k : ℕ)
    (hcount : ∀ i < k, (D i).card=2^i) (i : Fin k) (fallback : Label) :
    selectFresh D i.val fallback=chooseFresh D k hcount i := by
  simp only [selectFresh,dif_pos (fresh_nonempty D k hcount i),chooseFresh]

def ReverseOutput.choice (out : ReverseOutput n Label) (k : ℕ) (fallback : Label) : Fin k → Label :=
  fun i => selectFresh (fun j => (out.designated j).toFinset) i.val fallback

theorem sound_choice (recipient : ℕ → Fin n) (available : List Label)
    (k : ℕ) (out : ReverseOutput n Label) (hs : out.Sound recipient available k) (fallback : Label) :
    Function.Injective (out.choice k fallback) ∧
      (∀ i, out.choice k fallback i ∈ available) ∧
      ∀ i j, OrderedUnion.cachedValue (out.pieces (out.choice k fallback i)) (recipient i.val) ≤
        OrderedUnion.cachedValue (out.pieces (out.choice k fallback j)) (recipient i.val) := by
  let D := fun i => (out.designated i).toFinset
  have hcount : ∀ i < k, (D i).card=2^i := by
    intro i hi
    exact (List.toFinset_card_of_nodup (hs.designated i hi).2.1).trans (hs.designated i hi).1
  have hchoice : out.choice k fallback=chooseFresh D k hcount :=
    funext (fun i => selectFresh_eq D k hcount i fallback)
  rw [hchoice]
  have h := designated_choices_envy_free D k hcount available.toFinset
    (fun i hi p hp => List.mem_toFinset.mpr ((hs.designated i hi).2.2 p (List.mem_toFinset.mp hp)))
    (fun i p => OrderedUnion.cachedValue (out.pieces p) (recipient i.val))
    (fun i => out.threshold i.val)
    (fun i p hp => hs.floor i.val i.isLt p (List.mem_toFinset.mp hp))
    (fun i p hp hn => hs.exact i.val i.isLt p (List.mem_toFinset.mp hp) hn)
  exact ⟨h.1,fun i => List.mem_toFinset.mp (h.2.1 i),h.2.2⟩

end EnvyFreeResearch.Full.Chores.Augment
