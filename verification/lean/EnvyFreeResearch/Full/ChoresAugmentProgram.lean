import EnvyFreeResearch.Full.ChoresAugmentReverse
import EnvyFreeResearch.Full.ChoresAugmentPowerReservations
import EnvyFreeResearch.Full.ChoresAugmentChoice
import EnvyFreeResearch.Full.ChoresAugmentComplement

/-! Complete whole-piece augmentation, as an input-independent ordinary
Eval/Cut program. Reservations, thresholds, physical supplements and final
choices are computed; the exact unallocated complement is returned. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n k : ℕ} {Label : Type*} [LinearOrder Label] [Fintype Label]

structure WholeOutput (n k : ℕ) (Label : Type*) where
  allocated : Fin k → List (Parent n)
  remainder : List (Parent n)
  originalLabel : Fin k → Label

def finish (out : ReverseOutput n Label) (k : ℕ) (fallback : Label) : WholeOutput n k Label :=
  let choice := out.choice k fallback
  ⟨fun i => out.pieces (choice i),complement out.pieces choice,choice⟩

def wholeProgram (recipient : ℕ → Fin n) (k : ℕ) (original : Label → List (Parent n))
    (initial : List Label) (fallback : Label) : Program (Query (Fin n)) ℝ (WholeOutput n k Label) :=
  let reserved := powerReservations recipient k original initial
  (reverseProgram recipient reserved.available reserved.reserved k original).bind
    (fun out => .returned (finish out k fallback))

theorem whole_program_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (recipient : ℕ → Fin n) (k : ℕ) (original : Label → List (Parent n))
    (hv : FamilyValid P original) (initial : List Label)
    (hnd : initial.Nodup) (hlen : initial.length=2^(k+1)) (fallback : Label)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (wholeProgram recipient k original initial fallback) prior out trace ∧
      trace.length ≤ (2^k-1)*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 2^k-1 ∧
      (∀ i, Valid P (out.allocated i) ∧ Ordered (out.allocated i)) ∧
      Valid P out.remainder ∧ Ordered out.remainder ∧
      Pairwise (fun i j => Disjoint (material (out.allocated i)) (material (out.allocated j))) ∧
      (∀ i, Disjoint (material (out.allocated i)) (material out.remainder)) ∧
      (⋃ i, material (out.allocated i)) ∪ material out.remainder=familyMaterial original ∧
      Function.Injective out.originalLabel ∧
      (∀ i, material (original (out.originalLabel i)) ⊆ material (out.allocated i)) ∧
      ∀ i j, OrderedUnion.cachedValue (out.allocated i) (recipient i.val) ≤
        OrderedUnion.cachedValue (out.allocated j) (recipient i.val) := by
  let reserved := powerReservations recipient k original initial
  obtain ⟨havail,hlength,hres,hcross,hsep,hdom⟩ := power_reservations_correct recipient k original initial hnd hlen
  have hbudget : (∅ : Finset Label).card+totalQuota k < reserved.available.length := by
    change reserved.available.length=2^k+1 at hlength
    rw [Finset.card_empty,zero_add,hlength]
    have h := totalQuota_add_one k
    omega
  obtain ⟨out,trace,hexec,hQ,hC,hv',hcover,hsound,hother,hsub,hmon⟩ :=
    reverse_program_correct P hmono oracle hpolicy recipient reserved.available reserved.reserved original
      havail k hres hcross hsep hdom original hv ∅ hbudget (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) prior
  obtain ⟨hinj,hchosen,hEF⟩ := sound_choice recipient reserved.available k out hsound fallback
  have hquota : totalQuota k=2^k-1 := by have h := totalQuota_add_one k; omega
  refine ⟨finish out k fallback,trace,?_,?_,?_,?_,?_,?_,?_,?_,?_,hinj,?_,hEF⟩
  · simpa only [wholeProgram,reserved,List.append_nil] using
      hexec.bind (fun out => Program.returned (finish out k fallback)) (Executes.returned _ _)
  · simpa only [hquota] using hQ
  · simpa only [hquota] using hC
  · exact fun i => hv'.1 (out.choice k fallback i)
  · exact (complement_valid P out.pieces hv' (out.choice k fallback)).1
  · exact (complement_valid P out.pieces hv' (out.choice k fallback)).2
  · exact chosen_disjoint P out.pieces hv' (out.choice k fallback) hinj
  · exact complement_disjoint P out.pieces hv' (out.choice k fallback)
  · exact (complement_cover out.pieces (out.choice k fallback)).trans hcover
  · exact fun i => hsub (out.choice k fallback i) (hchosen i)

end EnvyFreeResearch.Full.Chores.Augment
