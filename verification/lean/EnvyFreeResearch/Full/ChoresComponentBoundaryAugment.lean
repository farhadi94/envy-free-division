import EnvyFreeResearch.Full.ChoresComponentBoundaryNearEqual
import EnvyFreeResearch.Full.ChoresAugmentProgram

/-! Actual whole-piece augmentation creates boundaries only through its
ordinary prefix-transfer Cuts. Cached reservation, sorting, designation and
complement assembly preserve the physical coordinate ledger. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n k : ℕ} {Label : Type*}

def FamilyKnown (points : Set ℝ) (pieces : Label → List (Parent n)) : Prop :=
  ∀ j, CacheKnown points (pieces j)

theorem FamilyKnown.mono {old more : Set ℝ} {pieces : Label → List (Parent n)}
    (h : FamilyKnown old pieces) (hm : old ⊆ more) : FamilyKnown more pieces :=
  fun j => (h j).mono hm

theorem transfer_state_known [DecidableEq Label] (points : Set ℝ)
    (pieces : Label → List (Parent n)) (hpieces : FamilyKnown points pieces)
    (source destination : Label) (out : Split n)
    (hout : CacheKnown points (out.prefixParts++out.suffixParts)) :
    FamilyKnown points (Augment.transferState pieces source destination out) := by
  intro j
  by_cases hd : j = destination
  · subst j
    simp only [Augment.transferState, Function.update_self]
    exact assemble_known ((hpieces destination).append (fun p hp => hout p (List.mem_append_left _ hp)))
  · by_cases hs : j = source
    · subst j
      simp only [Augment.transferState, Function.update_of_ne hd, Function.update_self]
      exact fun p hp => hout p (List.mem_append_right _ hp)
    · simpa only [Augment.transferState, Function.update_of_ne hd, Function.update_of_ne hs] using hpieces j

theorem transfer_known [DecidableEq Label] (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (amount : ℝ) (pieces : Label → List (Parent n))
    (hpieces : FamilyKnown points pieces) (source destination : Label)
    (prior : History (Query (Fin n)) ℝ) (out : Label → List (Parent n))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Augment.transferProgram c amount pieces source destination) prior out trace) :
    FamilyKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨split, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  obtain ⟨hparts, hscope⟩ := split_known oracle points c amount (pieces source) (hpieces source) prior split first hf
  exact ⟨transfer_state_known _ pieces (hpieces.mono subset_union_left) source destination split hparts, hscope⟩

theorem transfer_batch_known [DecidableEq Label] (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (jobs : List (Augment.TransferJob Label))
    (pieces : Label → List (Parent n)) (hpieces : FamilyKnown points pieces)
    (prior : History (Query (Fin n)) ℝ) (out : Label → List (Parent n))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Augment.transferBatch c jobs pieces) prior out trace) :
    FamilyKnown (Known points trace) out ∧ Scoped points trace := by
  induction jobs generalizing points pieces prior out trace with
  | nil => cases h; exact ⟨by simpa only [known_nil] using hpieces, trivial⟩
  | cons job rest ih =>
    obtain ⟨middle, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
    subst trace
    obtain ⟨hm, hs₁⟩ := transfer_known oracle points c job.amount pieces hpieces job.source job.destination prior middle t₁ h₁
    obtain ⟨ho, hs₂⟩ := ih (Known points t₁) middle hm (prior++t₁) out t₂ h₂
    exact ⟨by simpa only [known_append] using ho, (scoped_append points t₁ t₂).mpr ⟨hs₁, hs₂⟩⟩

theorem augment_round_known [LinearOrder Label] (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (a : ℕ) (available reserves : List Label)
    (pieces : Label → List (Parent n)) (hpieces : FamilyKnown points pieces)
    (prior : History (Query (Fin n)) ℝ) (out : Augment.RoundOutput n Label)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Augment.roundProgram c a available reserves pieces) prior out trace) :
    FamilyKnown (Known points trace) out.pieces ∧ Scoped points trace := by
  obtain ⟨fresh, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  exact transfer_batch_known oracle points c _ pieces hpieces prior fresh first hf

theorem augment_reverse_known [LinearOrder Label] (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (recipient : ℕ → Fin n) (available : List Label) (reserves : ℕ → List Label)
    (k : ℕ) (pieces : Label → List (Parent n)) (hpieces : FamilyKnown points pieces)
    (prior : History (Query (Fin n)) ℝ) (out : Augment.ReverseOutput n Label)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Augment.reverseProgram recipient available reserves k pieces) prior out trace) :
    FamilyKnown (Known points trace) out.pieces ∧ Scoped points trace := by
  induction k generalizing points pieces prior out trace with
  | zero => cases h; exact ⟨by simpa only [known_nil] using hpieces, trivial⟩
  | succ k ih =>
    obtain ⟨round, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
    obtain ⟨result, t₃, t₄, h₃, h₄, ht₂⟩ := Executes.split_bind _ _ h₂
    cases h₄
    simp only [List.append_nil] at ht₂
    subst t₂
    subst trace
    obtain ⟨hr, hs₁⟩ := augment_round_known oracle points (recipient k) (2^k) available (reserves k)
      pieces hpieces prior round t₁ h₁
    obtain ⟨ho, hs₃⟩ := ih (Known points t₁) round.pieces hr (prior++t₁) result t₃ h₃
    exact ⟨by simpa only [known_append, Augment.ReverseOutput.install] using ho,
      (scoped_append points t₁ t₃).mpr ⟨hs₁, hs₃⟩⟩

theorem join_labels_known (points : Set ℝ) (pieces : Label → List (Parent n))
    (hpieces : FamilyKnown points pieces) (labels : List Label) :
    CacheKnown points (Augment.joinLabels pieces labels) := by
  apply assemble_known
  intro p hp
  obtain ⟨parts, hparts, hp⟩ := List.mem_flatMap.mp hp
  exact hpieces parts p hp

def WholeKnown (points : Set ℝ) (out : Augment.WholeOutput n k Label) : Prop :=
  (∀ i, CacheKnown points (out.allocated i)) ∧ CacheKnown points out.remainder

theorem WholeKnown.mono {old more : Set ℝ} {out : Augment.WholeOutput n k Label}
    (h : WholeKnown old out) (hm : old ⊆ more) : WholeKnown more out :=
  ⟨fun i => (h.1 i).mono hm, h.2.mono hm⟩

theorem augment_finish_known [LinearOrder Label] [Fintype Label] (points : Set ℝ)
    (out : Augment.ReverseOutput n Label) (hout : FamilyKnown points out.pieces) (k : ℕ) (fallback : Label) :
    WholeKnown points (Augment.finish out k fallback) :=
  ⟨fun i => hout _, join_labels_known points out.pieces hout _⟩

theorem augment_whole_known [LinearOrder Label] [Fintype Label]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (recipient : ℕ → Fin n) (k : ℕ)
    (original : Label → List (Parent n)) (horiginal : FamilyKnown points original)
    (initial : List Label) (fallback : Label) (prior : History (Query (Fin n)) ℝ)
    (out : Augment.WholeOutput n k Label) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Augment.wholeProgram recipient k original initial fallback) prior out trace) :
    WholeKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨result, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  obtain ⟨ho, hscope⟩ := augment_reverse_known oracle points recipient _ _ k original horiginal prior result first hf
  exact ⟨augment_finish_known _ result ho k fallback, hscope⟩

end EnvyFreeResearch.Full.Chores.Boundary
