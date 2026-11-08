import EnvyFreeResearch.Full.ChoresAugmentReverseData

/-! The reverse-loop invariant links executed thresholds to the final
whole-piece choice. Later additions preserve every earlier floor; a
public bundle outside the later designated sets stays exactly unchanged. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Label : Type*} [LinearOrder Label]

structure ReverseOutput.Sound (out : ReverseOutput n Label)
    (recipient : ℕ → Fin n) (available : List Label) (k : ℕ) : Prop where
  designated : ∀ i < k, (out.designated i).length=2^i ∧ (out.designated i).Nodup ∧
    ∀ p ∈ out.designated i, p ∈ available
  floor : ∀ i < k, ∀ p ∈ available,
    out.threshold i ≤ OrderedUnion.cachedValue (out.pieces p) (recipient i)
  exact : ∀ i < k, ∀ p ∈ out.designated i,
    p ∉ earlier (fun j => (out.designated j).toFinset) i →
      OrderedUnion.cachedValue (out.pieces p) (recipient i)=out.threshold i

theorem install_sound (recipient : ℕ → Fin n) (available : List Label)
    (k : ℕ) (round : RoundOutput n Label) (out : ReverseOutput n Label)
    (hsound : out.Sound recipient available k)
    (hcount : round.designated.length=2^k) (hnd : round.designated.Nodup)
    (hinside : ∀ p ∈ round.designated, p ∈ available)
    (hfloor : ∀ p ∈ available, round.threshold ≤ OrderedUnion.cachedValue (round.pieces p) (recipient k))
    (hexact : ∀ p ∈ round.designated, OrderedUnion.cachedValue (round.pieces p) (recipient k)=round.threshold)
    (hmon : ∀ p ∈ available, ∀ i, OrderedUnion.cachedValue (round.pieces p) i ≤ OrderedUnion.cachedValue (out.pieces p) i)
    (hother : ∀ p ∈ available, p ∉ out.marked k → out.pieces p=round.pieces p) :
    (out.install k round).Sound recipient available (k+1) := by
  constructor
  · intro i hi
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | heq
    · have hne : i ≠ k := Nat.ne_of_lt hi
      simpa only [ReverseOutput.install,Function.update_of_ne hne] using hsound.designated i hi
    · subst i
      simpa only [ReverseOutput.install,Function.update_self] using And.intro hcount (And.intro hnd hinside)
  · intro i hi p hp
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | heq
    · have hne : i ≠ k := Nat.ne_of_lt hi
      simpa only [ReverseOutput.install,Function.update_of_ne hne] using hsound.floor i hi p hp
    · subst i
      simp only [ReverseOutput.install,Function.update_self]
      exact (hfloor p hp).trans (hmon p hp (recipient k))
  · intro i hi p hp hnot
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | heq
    · have hne : i ≠ k := Nat.ne_of_lt hi
      rw [earlier_install out k round i hi.le] at hnot
      have hp' : p ∈ out.designated i := by simpa only [ReverseOutput.install,Function.update_of_ne hne] using hp
      simpa only [ReverseOutput.install,Function.update_of_ne hne] using hsound.exact i hi p hp' hnot
    · subst i
      have hp' : p ∈ round.designated := by simpa only [ReverseOutput.install,Function.update_self] using hp
      rw [earlier_install out k round k le_rfl] at hnot
      change p ∉ out.marked k at hnot
      simp only [ReverseOutput.install,Function.update_self]
      rw [hother p (hinside p hp') hnot]
      exact hexact p hp'

end EnvyFreeResearch.Full.Chores.Augment
