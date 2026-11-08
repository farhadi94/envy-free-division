import EnvyFreeResearch.Full.ChoresSubCoreDomains

/-! The actual affine target guard follows from whole-parent nonnegativity
at entry, or from nonnegative inherited own benchmarks in a recursive call.
The baseline-only entry case does not pretend that a virtual record is physical. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical
open Set Persistent SubCore
variable {n : ℕ} {GlobalParent Payload Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

def Input (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (inherited : Allocation Agent Parent (OrderedRecord n)) (store : Store GlobalParent Payload) : Prop :=
  ((∀ i p, benchmark i ≤ cachedValue agent i p (whole p)) ∧
    (∀ i p, 0 ≤ (ofLex (cachedValue agent i p (whole p))).1)) ∨
  (SubCore.InheritedAllocation (cachedValue agent) univ whole benchmark inherited ∧
    (∀ i, Stored view store (parent (inherited.assigned i)) (inherited.point (inherited.assigned i))) ∧
    (∀ i, 0 ≤ (ofLex (benchmark i)).1))

theorem primary_mono {a b : Lex (ℝ × ℚ)} (h : a ≤ b) : (ofLex a).1 ≤ (ofLex b).1 :=
  Prod.Lex.monotone_fst _ _ h

theorem Input.mono (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (inherited : Allocation Agent Parent (OrderedRecord n)) {before after : Store GlobalParent Payload}
    (h : Extends before after) (hi : Input view agent parent whole benchmark inherited before) :
    Input view agent parent whole benchmark inherited after := by
  rcases hi with hbase | ⟨hInherited,hrecords,hnonneg⟩
  · exact Or.inl hbase
  · exact Or.inr ⟨hInherited,fun i => Stored.mono view h (hrecords i),hnonneg⟩

theorem Input.restrict (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (inherited : Allocation Agent Parent (OrderedRecord n)) (store : Store GlobalParent Payload)
    (hi : Input view agent parent whole benchmark inherited store) (selected : Finset Agent) :
    Input view (fun i : selected => agent i.val) parent whole (fun i : selected => benchmark i.val)
      ⟨(⟨Subtype.val,Subtype.val_injective⟩ : selected ↪ Agent).trans inherited.assigned,inherited.point⟩ store := by
  rcases hi with ⟨hlow,hnonneg⟩ | ⟨hInherited,hrecords,hnonneg⟩
  · exact Or.inl ⟨fun i => hlow i.val,fun i => hnonneg i.val⟩
  · exact Or.inr ⟨⟨fun i => hInherited.1 i.val,fun i => hInherited.2.1 i.val,
      fun i j => hInherited.2.2 i.val j.val⟩,fun i => hrecords i.val,fun i => hnonneg i.val⟩

theorem Input.targets_nonnegative (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (inherited : Allocation Agent Parent (OrderedRecord n)) (store : Store GlobalParent Payload)
    (hi : Input view agent parent whole benchmark inherited store)
    (processed : Finset Agent) (assigned : processed ↪ Parent) (hc : processed.card < Fintype.card Parent) :
    ∀ i, 0 ≤ (ofLex (stageTarget processed assigned hc (fun i p => cachedValue agent i p (whole p)) benchmark i)).1 := by
  intro i
  rcases hi with ⟨_,hnonneg⟩ | ⟨_,_,hnonneg⟩
  · exact (hnonneg i _).trans (primary_mono (le_max_right _ _))
  · exact (hnonneg i).trans (primary_mono (stageTarget_benchmark processed assigned hc _ benchmark i))

theorem Input.output_nonnegative (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (inherited out : Allocation Agent Parent (OrderedRecord n)) (store : Store GlobalParent Payload)
    (hi : Input view agent parent whole benchmark inherited store) (hmany : Fintype.card Agent < Fintype.card Parent)
    (hout : SubCore.AllocationCorrect (cachedValue agent) univ whole benchmark out) :
    ∀ i, 0 ≤ (ofLex (cachedValue agent i (out.assigned i) (out.point (out.assigned i)))).1 := by
  intro i
  rcases hi with ⟨_,hnonneg⟩ | ⟨_,_,hnonneg⟩
  · have hnot : ¬ Function.Surjective out.assigned := by
      intro hsurj
      exact (not_le_of_gt hmany) (Fintype.card_le_of_surjective out.assigned hsurj)
    change ¬ (∀ p, ∃ j, out.assigned j = p) at hnot
    push_neg at hnot
    obtain ⟨p,hfree⟩ := hnot
    have hbest := hout.2.1 i p
    rw [hout.2.2.2.1 p hfree] at hbest
    exact (hnonneg i p).trans (primary_mono hbest)
  · exact (hnonneg i).trans (primary_mono (hout.2.2.1 i))

end EnvyFreeResearch.Full.Chores.SubCorePhysical
