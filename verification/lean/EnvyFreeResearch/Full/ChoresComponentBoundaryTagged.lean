import EnvyFreeResearch.Full.ChoresComponentBoundarySuffix

/-! The coordinate ledger ignores routing tags while retaining the complete
actual tagged history. Tagging changes the queried parent, never a query
endpoint or a returned physical coordinate. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle QueryProgram Persistent Suffix SubCoreLeaves
open scoped Classical

variable {n : ℕ} {Q Root A : Type*}

def projectTrace (project : Q → Query (Fin n)) (trace : History Q ℝ) : History (Query (Fin n)) ℝ :=
  trace.map (fun qr => (project qr.1, qr.2))

@[simp] theorem projectTrace_append (project : Q → Query (Fin n)) (first second : History Q ℝ) :
    projectTrace project (first++second) = projectTrace project first++projectTrace project second :=
  List.map_append

def KnownBy (project : Q → Query (Fin n)) (points : Set ℝ) (trace : History Q ℝ) : Set ℝ :=
  Known points (projectTrace project trace)

def ScopedBy (project : Q → Query (Fin n)) (points : Set ℝ) (trace : History Q ℝ) : Prop :=
  Scoped points (projectTrace project trace)

@[simp] theorem knownBy_nil (project : Q → Query (Fin n)) (points : Set ℝ) :
    KnownBy project points [] = points := known_nil points

@[simp] theorem scopedBy_nil (project : Q → Query (Fin n)) (points : Set ℝ) :
    ScopedBy project points [] := trivial

theorem knownBy_append (project : Q → Query (Fin n)) (points : Set ℝ) (first second : History Q ℝ) :
    KnownBy project points (first++second) = KnownBy project (KnownBy project points first) second := by
  simp only [KnownBy, projectTrace_append, known_append]

theorem knownBy_old (project : Q → Query (Fin n)) (points : Set ℝ) (trace : History Q ℝ) :
    points ⊆ KnownBy project points trace := subset_union_left

theorem knownBy_mono (project : Q → Query (Fin n)) (points : Set ℝ) (first second : History Q ℝ) :
    KnownBy project points first ⊆ KnownBy project points (first++second) := by
  rw [knownBy_append]
  exact subset_union_left

theorem scopedBy_append (project : Q → Query (Fin n)) (points : Set ℝ) (first second : History Q ℝ) :
    ScopedBy project points (first++second) ↔
      ScopedBy project points first ∧ ScopedBy project (KnownBy project points first) second := by
  simp only [ScopedBy, projectTrace_append, scoped_append, KnownBy]

theorem project_tag (p : Root) (trace : History (Query (Fin n)) ℝ) :
    projectTrace Prod.snd (Masked.tagHistory p trace) = trace := by
  simp only [projectTrace, Masked.tagHistory, List.map_map, Function.comp_def]
  exact List.map_id trace

/-- Successful tagged execution has an actual ordinary source execution,
under the policy containing the exact preceding global history. -/
theorem untag_executes (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ)
    (prior : History (Masked.TaggedQuery Root n) ℝ) (p : Root)
    (program : Program (Query (Fin n)) ℝ A)
    (history : History (Query (Fin n)) ℝ) (out : A)
    (tagged : History (Masked.TaggedQuery Root n) ℝ)
    (h : Executes oracle (Masked.tagProgram p program) (prior++Masked.tagHistory p history) out tagged) :
    ∃ trace, tagged = Masked.tagHistory p trace ∧
      Executes (Masked.localPolicy oracle prior p) program history out trace := by
  induction program generalizing history out tagged with
  | returned a =>
    cases h
    exact ⟨[], rfl, Executes.returned _ _⟩
  | failed => cases h
  | ask q next ih =>
    cases h with
    | ask q' k prior' reply result tail hreply hnext =>
      have ht : Executes oracle (Masked.tagProgram p (next reply))
          (prior++Masked.tagHistory p (history++[(q,reply)])) out tail := by
        simpa only [Masked.tagHistory, List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hnext
      obtain ⟨trace, heq, he⟩ := ih reply (history++[(q,reply)]) out tail ht
      refine ⟨(q,reply)::trace, ?_, Executes.ask q next history reply out trace hreply he⟩
      simpa only [Masked.tagHistory, List.map_cons] using congrArg (List.cons ((p,q),reply)) heq

theorem clipped_leaf_known (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ)
    (points : Set ℝ) (p : Root) (records : List (ClippedRecord n))
    (hold : ∀ r ∈ records, 1-r.record.point ∈ points) (i : Fin n) (target : ℝ × ℚ)
    (prior : History (Masked.TaggedQuery Root n) ℝ) (out : Lookup.Result (ClippedRecord n))
    (trace : History (Masked.TaggedQuery Root n) ℝ)
    (h : Executes oracle (clippedEnsure p i target records) prior out trace) :
    (∀ r ∈ out.records, 1-r.record.point ∈ KnownBy Prod.snd points trace) ∧
      1-out.selected.record.point ∈ KnownBy Prod.snd points trace ∧ ScopedBy Prod.snd points trace := by
  obtain ⟨source, heq, he⟩ := untag_executes oracle prior p (clippedEnsureProgram records i target)
    [] out trace (by simpa only [clippedEnsure, Masked.tagHistory, List.map_nil, List.append_nil] using h)
  have hh := clipped_ensure_known (Masked.localPolicy oracle prior p) points records hold i target [] out source he
  simpa only [heq, KnownBy, ScopedBy, project_tag] using hh

theorem affine_leaf_known [Fintype Root] [Nonempty Root]
    (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ)
    (points : Set ℝ) (hone : 1 ∈ points) (offset : Root → Fin n → ℝ) (p : Root)
    (records : List (Record n)) (hold : ∀ r ∈ records, 1-r.point ∈ points)
    (i : Fin n) (target : ℝ × ℚ) (prior : History (Masked.TaggedQuery Root n) ℝ)
    (out : Lookup.Result (Record n)) (trace : History (Masked.TaggedQuery Root n) ℝ)
    (h : Executes oracle (affineEnsure offset p i target records) prior out trace) :
    (∀ r ∈ out.records, 1-r.point ∈ KnownBy Prod.snd points trace) ∧
      1-out.selected.point ∈ KnownBy Prod.snd points trace ∧ ScopedBy Prod.snd points trace := by
  obtain ⟨source, heq, he⟩ := untag_executes oracle prior p (affineLookupProgram offset records i target)
    [] out trace (by simpa only [affineEnsure, Masked.tagHistory, List.map_nil, List.append_nil] using h)
  rw [affineLookupProgram] at he
  obtain ⟨fresh, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ he
  cases hs
  simp only [List.append_nil] at ht
  subst source
  have hh := affine_virtual_known (Masked.localPolicy oracle prior p) points (virtualBottom offset)
    (by simpa only [virtualBottom, sub_zero] using hone) records hold i target [] fresh first hf
  simpa only [heq, KnownBy, ScopedBy, project_tag] using hh

end EnvyFreeResearch.Full.Chores.Boundary
