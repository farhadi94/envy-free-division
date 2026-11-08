import EnvyFreeResearch.Full.ChoresComponentBoundaryTagged
import EnvyFreeResearch.Full.ChoresSubCorePhysicalProgram

/-! A compositional trace invariant for the real persistent SubCore store.
It retains all explored rows, including checked failures. The leaf contract
below concerns only query and coordinate provenance, not allocation success. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle QueryProgram Persistent Suffix SubCore SubCorePhysical
open scoped Classical

variable {n : ℕ} {GlobalParent Payload Q A B : Type*}

def SuffixStoreKnown (view : Payload → Record n) (points : Set ℝ)
    (store : SubCorePhysical.Store GlobalParent Payload) : Prop :=
  ∀ p r, r ∈ store p → 1-(view r).point ∈ points

theorem SuffixStoreKnown.mono {view : Payload → Record n} {old more : Set ℝ}
    {store : SubCorePhysical.Store GlobalParent Payload}
    (h : SuffixStoreKnown view old store) (hm : old ⊆ more) : SuffixStoreKnown view more store :=
  fun p r hr => hm (h p r hr)

def Tracks (project : Q → Query (Fin n)) (view : Payload → Record n)
    (oracle : AdaptiveOracle.Policy Q ℝ) (store : SubCorePhysical.Store GlobalParent Payload)
    (getStore : A → SubCorePhysical.Store GlobalParent Payload) (program : Program Q ℝ A) : Prop :=
  ∀ points, 1 ∈ points → SuffixStoreKnown view points store →
    ∀ prior out trace, Executes oracle program prior out trace →
      SuffixStoreKnown view (KnownBy project points trace) (getStore out) ∧ ScopedBy project points trace

theorem tracks_returned (project : Q → Query (Fin n)) (view : Payload → Record n)
    (oracle : AdaptiveOracle.Policy Q ℝ) (getStore : A → SubCorePhysical.Store GlobalParent Payload)
    (out : A) : Tracks project view oracle (getStore out) getStore (.returned out) := by
  intro points hone hold prior result trace h
  cases h
  exact ⟨by simpa only [knownBy_nil] using hold, trivial⟩

theorem tracks_pure (project : Q → Query (Fin n)) (view : Payload → Record n)
    (oracle : AdaptiveOracle.Policy Q ℝ) (store : SubCorePhysical.Store GlobalParent Payload)
    (getStore : A → SubCorePhysical.Store GlobalParent Payload)
    (out : A) (hstore : getStore out = store) :
    Tracks project view oracle store getStore (.returned out) := by
  rw [← hstore]
  exact tracks_returned project view oracle getStore out

theorem tracks_bind (project : Q → Query (Fin n)) (view : Payload → Record n)
    (oracle : AdaptiveOracle.Policy Q ℝ) (store : SubCorePhysical.Store GlobalParent Payload)
    (firstStore : A → SubCorePhysical.Store GlobalParent Payload)
    (lastStore : B → SubCorePhysical.Store GlobalParent Payload)
    (first : Program Q ℝ A) (next : A → Program Q ℝ B)
    (hfirst : Tracks project view oracle store firstStore first)
    (hnext : ∀ out, Tracks project view oracle (firstStore out) lastStore (next out)) :
    Tracks project view oracle store lastStore (first.bind next) := by
  intro points hone hold prior out trace h
  obtain ⟨middle, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
  subst trace
  have hf := hfirst points hone hold prior middle t₁ h₁
  have hs := hnext middle (KnownBy project points t₁) (Or.inl hone) hf.1 (prior++t₁) out t₂ h₂
  exact ⟨by simpa only [knownBy_append] using hs.1,
    (scopedBy_append project points t₁ t₂).mpr ⟨hf.2, hs.2⟩⟩

def LeafTracks (project : Q → Query (Fin n)) (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Q ℝ (Lookup.Result Payload))
    (oracle : AdaptiveOracle.Policy Q ℝ) : Prop :=
  ∀ points, 1 ∈ points → ∀ p records,
    (∀ r ∈ records, 1-(view r).point ∈ points) → ∀ i target prior out trace,
    Executes oracle (ensure p i target records) prior out trace →
      (∀ r ∈ out.records, 1-(view r).point ∈ KnownBy project points trace) ∧
        1-(view out.selected).point ∈ KnownBy project points trace ∧ ScopedBy project points trace

theorem clipped_leaf_tracks (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery GlobalParent n) ℝ) :
    LeafTracks Prod.snd ClippedRecord.record SubCoreLeaves.clippedEnsure oracle := by
  intro points _ p records hold i target prior out trace h
  exact clipped_leaf_known oracle points p records hold i target prior out trace h

theorem affine_leaf_tracks [Fintype GlobalParent] [Nonempty GlobalParent]
    (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery GlobalParent n) ℝ)
    (offset : GlobalParent → Fin n → ℝ) :
    LeafTracks Prod.snd id (SubCoreLeaves.affineEnsure offset) oracle := by
  intro points hone p records hold i target prior out trace h
  exact affine_leaf_known oracle points hone offset p records hold i target prior out trace h

variable [DecidableEq GlobalParent]
    (project : Q → Query (Fin n)) (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Q ℝ (Lookup.Result Payload))
    (oracle : AdaptiveOracle.Policy Q ℝ) (hleaf : LeafTracks project view ensure oracle)

include hleaf

theorem ensure_global_tracks (store : SubCorePhysical.Store GlobalParent Payload)
    (p : GlobalParent) (i : Fin n) (target : Lex (ℝ × ℚ)) :
    Tracks project view oracle store EnsureOutput.store
      (SubCorePhysical.ensureGlobalProgram view ensure store p i target) := by
  intro points hone hold prior out trace h
  obtain ⟨leaf, first, second, hl, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  have hh := hleaf points hone p (store p) (hold p) i (ofLex target) prior leaf first hl
  refine ⟨?_, hh.2.2⟩
  intro q r hr
  by_cases hq : q = p
  · subst q
    exact hh.1 r (by simpa only [Function.update_self] using hr)
  · exact Or.inl (hold q r (by simpa only [Function.update_of_ne hq] using hr))

variable {Agent Parent : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem one_trim_tracks (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (store : SubCorePhysical.Store GlobalParent Payload) (pair : Agent × Parent) :
    Tracks project view oracle store OneTrimOutput.store
      (oneTrimProgram view ensure agent parent whole target store pair) := by
  unfold oneTrimProgram
  split_ifs
  · apply tracks_pure project view oracle <;> rfl
  · apply tracks_bind project view oracle store EnsureOutput.store OneTrimOutput.store
    · exact ensure_global_tracks project view ensure oracle hleaf store _ _ _
    · intro out
      apply tracks_pure project view oracle <;> rfl

theorem trim_list_tracks (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (pairs : List (Agent × Parent)) (store : SubCorePhysical.Store GlobalParent Payload) :
    Tracks project view oracle store TrimRows.store
      (trimListProgram view ensure agent parent whole target pairs store) := by
  induction pairs generalizing store with
  | nil => apply tracks_pure project view oracle <;> rfl
  | cons pair rest ih =>
    rw [trimListProgram]
    apply tracks_bind project view oracle store OneTrimOutput.store TrimRows.store
    · exact one_trim_tracks project view ensure oracle hleaf agent parent whole target store pair
    · intro first
      apply tracks_bind project view oracle first.store TrimRows.store TrimRows.store
      · exact ih first.store
      · intro tail
        apply tracks_pure project view oracle <;> rfl

theorem trim_table_tracks (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (store : SubCorePhysical.Store GlobalParent Payload) :
    Tracks project view oracle store Prod.fst
      (trimTableProgram view ensure agent parent whole target store) := by
  unfold trimTableProgram
  split_ifs
  · apply tracks_bind project view oracle store TrimRows.store Prod.fst
    · exact trim_list_tracks project view ensure oracle hleaf agent parent whole target _ store
    · intro out
      split_ifs <;> apply tracks_pure project view oracle <;> rfl
  · apply tracks_pure project view oracle <;> rfl

end EnvyFreeResearch.Full.Chores.Boundary
