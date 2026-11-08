import EnvyFreeResearch.Full.ChoresAugmentFamily

/-! One actual prefix transfer in whole-piece augmentation. Every original
observer's new values are recorded by the ordinary Cut implementation;
the complete physical family and every unchanged label are preserved. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n : ℕ} {Label : Type*} [DecidableEq Label]

def transferProgram (c : Fin n) (amount : ℝ) (pieces : Label → List (Parent n)) (s d : Label) :
    Program (Query (Fin n)) ℝ (Label → List (Parent n)) :=
  (splitProgram c amount (pieces s)).bind (fun out => .returned (transferState pieces s d out))

theorem transfer_program_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (amount : ℝ) (pieces : Label → List (Parent n))
    (hv : FamilyValid P pieces) (s d : Label) (hne : s ≠ d)
    (ha : 0 ≤ amount) (hfit : amount ≤ OrderedUnion.cachedValue (pieces s) c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ next trace, Executes oracle (transferProgram c amount pieces s d) prior next trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      FamilyValid P next ∧ familyMaterial next=familyMaterial pieces ∧
      (∀ j, j ≠ s → j ≠ d → next j=pieces j) ∧
      (∀ j, j ≠ s → material (pieces j) ⊆ material (next j)) ∧
      (∀ j, j ≠ s → ∀ i, OrderedUnion.cachedValue (pieces j) i ≤ OrderedUnion.cachedValue (next j) i) ∧
      OrderedUnion.cachedValue (next d) c=OrderedUnion.cachedValue (pieces d) c+amount := by
  obtain ⟨out,trace,hexec,hQ,hC,hcover,hdis,horder,hpre,hsuf,htarget,hvalues⟩ :=
    split_program_physical P hmono oracle hpolicy c (pieces s) (hv.1 s).1 (hv.1 s).2
      amount ha hfit prior
  let next := transferState pieces s d out
  refine ⟨next,trace,?_,hQ,hC,transfer_valid P pieces hv s d hne out hpre hsuf horder hcover hdis,
    transfer_material pieces s d hne out hcover,?_,?_,?_,?_⟩
  · simpa only [transferProgram,List.append_nil] using
      hexec.bind (fun out => Program.returned (transferState pieces s d out)) (Executes.returned _ _)
  · exact fun j hs hd => transfer_other pieces s d j hs hd out
  · intro j hs
    by_cases hd : j=d
    · subst j
      change material (pieces d) ⊆ material (transferState pieces s d out d)
      rw [transfer_destination,assemble_material,material_append]
      exact subset_union_left
    · rw [show next j=pieces j from transfer_other pieces s d j hs hd out]
  · intro j hs i
    by_cases hd : j=d
    · subst j
      change OrderedUnion.cachedValue (pieces d) i ≤ OrderedUnion.cachedValue (transferState pieces s d out d) i
      rw [transfer_value P pieces (fun j => (hv.1 j).1) s d out hpre i]
      exact le_add_of_nonneg_right (cachedValue_nonnegative P hmono hpre i)
    · rw [show next j=pieces j from transfer_other pieces s d j hs hd out]
  · change OrderedUnion.cachedValue (transferState pieces s d out d) c=_
    rw [transfer_value P pieces (fun j => (hv.1 j).1) s d out hpre c,htarget]

end EnvyFreeResearch.Full.Chores.Augment
