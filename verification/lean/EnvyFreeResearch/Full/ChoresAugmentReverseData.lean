import EnvyFreeResearch.Full.ChoresAugmentRound
import EnvyFreeResearch.Full.ChoresAugmentDesignations

/-! The reverse augmentation program processes the recipients in descending
order, retaining the actual designated lists and thresholds at each step. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical BigOperators

variable {n : ℕ} {Label : Type*} [LinearOrder Label]

def totalQuota (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (2 : ℕ)^i

theorem totalQuota_zero : totalQuota 0=0 := by simp [totalQuota]
theorem totalQuota_succ (k : ℕ) : totalQuota (k+1)=totalQuota k+2^k := by
  simp [totalQuota,Finset.sum_range_succ]
theorem totalQuota_add_one (k : ℕ) : totalQuota k+1=2^k := sum_powers_two k

structure ReverseOutput (n : ℕ) (Label : Type*) where
  pieces : Label → List (Parent n)
  designated : ℕ → List Label
  threshold : ℕ → ℝ

def ReverseOutput.marked (out : ReverseOutput n Label) (k : ℕ) : Finset Label :=
  earlier (fun i => (out.designated i).toFinset) k

def ReverseOutput.install (out : ReverseOutput n Label) (k : ℕ) (round : RoundOutput n Label) :
    ReverseOutput n Label :=
  ⟨out.pieces,Function.update out.designated k round.designated,
    Function.update out.threshold k round.threshold⟩

theorem marked_install (out : ReverseOutput n Label) (k : ℕ) (round : RoundOutput n Label) :
    (out.install k round).marked (k+1)=out.marked k ∪ round.designated.toFinset := by
  ext p
  simp only [ReverseOutput.marked,earlier,Finset.mem_biUnion,Finset.mem_range,Finset.mem_union,
    List.mem_toFinset,ReverseOutput.install]
  constructor
  · rintro ⟨i,hi,hp⟩
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · exact Or.inl ⟨i,hi,by simpa [Function.update_of_ne (Nat.ne_of_lt hi)] using hp⟩
    · exact Or.inr (by simpa using hp)
  · rintro (⟨i,hi,hp⟩ | hp)
    · exact ⟨i,Nat.lt_succ_of_lt hi,by simpa [Function.update_of_ne (Nat.ne_of_lt hi)] using hp⟩
    · exact ⟨k,Nat.lt_succ_self k,by simpa using hp⟩

theorem earlier_install (out : ReverseOutput n Label) (k : ℕ) (round : RoundOutput n Label)
    (i : ℕ) (hi : i ≤ k) :
    earlier (fun j => ((out.install k round).designated j).toFinset) i=
      earlier (fun j => (out.designated j).toFinset) i := by
  apply Finset.biUnion_congr rfl
  intro j hj
  have hne : j ≠ k := Nat.ne_of_lt ((Finset.mem_range.mp hj).trans_le hi)
  simp only [ReverseOutput.install,Function.update_of_ne hne]

def reverseProgram (recipient : ℕ → Fin n) (available : List Label) (reserves : ℕ → List Label) :
    ℕ → (Label → List (Parent n)) → Program (Query (Fin n)) ℝ (ReverseOutput n Label)
  | 0, pieces => .returned ⟨pieces,fun _ => [],fun _ => 0⟩
  | k+1, pieces => (roundProgram (recipient k) (2^k) available (reserves k) pieces).bind
      (fun round => (reverseProgram recipient available reserves k round.pieces).bind
        (fun out => .returned (out.install k round)))

end EnvyFreeResearch.Full.Chores.Augment
