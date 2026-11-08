import EnvyFreeResearch.Full.UpperGlobalProtocolState
import Mathlib.Data.Fintype.Lattice

/-! Finite proper sink selection from actual directed non-reachability. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Sink
open scoped Classical
variable {n : ℕ}

def StrongOn (E : Fin n → Fin n → Prop) (A : Finset (Fin n)) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, Relation.ReflTransGen E i j

def Closed (E : Fin n → Fin n → Prop) (A S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ A, E i j → j ∈ S

def ProperSink (E : Fin n → Fin n → Prop) (A S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ S ⊆ A ∧ S ≠ A ∧ Closed E A S

def reachableSet (E : Fin n → Fin n → Prop) (A : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  A.filter (fun j => Relation.ReflTransGen E i j)

theorem exists_proper_sink (E : Fin n → Fin n → Prop) (A : Finset (Fin n))
    (hn : ¬ StrongOn E A) : ∃ S, ProperSink E A S := by
  unfold StrongOn at hn
  push_neg at hn
  obtain ⟨i,hi,j,hj,hnot⟩ := hn
  refine ⟨reachableSet E A i,?_,Finset.filter_subset _ _,?_,?_⟩
  · exact ⟨i,Finset.mem_filter.mpr ⟨hi,Relation.ReflTransGen.refl⟩⟩
  · intro heq
    have hm : j ∈ reachableSet E A i := heq.symm ▸ hj
    exact hnot (Finset.mem_filter.mp hm).2
  · intro a ha b hb hab
    exact Finset.mem_filter.mpr ⟨hb,(Finset.mem_filter.mp ha).2.tail hab⟩

def MinimalSink (E : Fin n → Fin n → Prop) (A S : Finset (Fin n)) : Prop :=
  ProperSink E A S ∧ ∀ T, ProperSink E A T → S.card ≤ T.card

theorem exists_minimal_sink (E : Fin n → Fin n → Prop) (A : Finset (Fin n))
    (hn : ¬ StrongOn E A) : ∃ S, MinimalSink E A S := by
  obtain ⟨S,hS⟩ := exists_proper_sink E A hn
  let candidates : Finset (Finset (Fin n)) := Finset.univ.filter (ProperSink E A)
  have hc : candidates.Nonempty := ⟨S,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS⟩⟩
  obtain ⟨M,hM,hmin⟩ := candidates.exists_min_image Finset.card hc
  exact ⟨M,(Finset.mem_filter.mp hM).2,
    fun T hT => hmin T (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT⟩)⟩

theorem minimal_sink_strong (E : Fin n → Fin n → Prop) (A M : Finset (Fin n))
    (hM : MinimalSink E A M) : StrongOn E M := by
  have hm := hM.1
  intro i hi j hj
  let T := reachableSet E M i
  have hTsub : T ⊆ M := Finset.filter_subset _ _
  have hT : ProperSink E A T := by
    refine ⟨⟨i,Finset.mem_filter.mpr ⟨hi,Relation.ReflTransGen.refl⟩⟩,
      hTsub.trans hm.2.1,?_,?_⟩
    · intro heq
      apply hm.2.2.1
      apply Finset.Subset.antisymm hm.2.1
      rw [← heq]
      exact hTsub
    · intro a ha b hb hab
      exact Finset.mem_filter.mpr ⟨hm.2.2.2 a (hTsub ha) b hb hab,
        (Finset.mem_filter.mp ha).2.tail hab⟩
  have heq : T=M := Finset.eq_of_subset_of_card_le hTsub (hM.2 T hT)
  have hjT : j ∈ T := heq.symm ▸ hj
  exact (Finset.mem_filter.mp hjT).2

theorem exists_sink_component (E : Fin n → Fin n → Prop) (A : Finset (Fin n))
    (hn : ¬ StrongOn E A) : ∃ S, ProperSink E A S ∧ StrongOn E S := by
  obtain ⟨S,hS⟩ := exists_minimal_sink E A hn
  exact ⟨S,hS.1,minimal_sink_strong E A S hS⟩
theorem closed_path_mem (E : Fin n → Fin n → Prop) (A S : Finset (Fin n))
    (hclosed : Closed E A S) (htarget : ∀ i j, E i j → j ∈ A)
    {i j : Fin n} (hi : i ∈ S) (hp : Relation.ReflTransGen E i j) : j ∈ S := by
  induction hp with
  | refl => exact hi
  | @tail b c hp hbc ih => exact hclosed b ih c (htarget b c hbc) hbc

theorem proper_sink_not_strong (E : Fin n → Fin n → Prop) (A S : Finset (Fin n))
    (hs : ProperSink E A S) (htarget : ∀ i j, E i j → j ∈ A) : ¬ StrongOn E A := by
  intro hstrong
  obtain ⟨i,hi⟩ := hs.1
  have hAS : A ⊆ S := by
    intro j hj
    exact closed_path_mem E A S hs.2.2.2 htarget hi (hstrong i (hs.2.1 hi) j hj)
  exact hs.2.2.1 (Finset.Subset.antisymm hs.2.1 hAS)
end EnvyFreeResearch.Full.UpperGlobal.Sink
