import EnvyFreeResearch.Full.ChoresUnionCoreCache

/-! Physical boundary accounting.  Only replies to actual Cut requests create
new points in this ledger; Eval replies are values, not coordinates. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ}

def cutReplies : History (Query (Fin n)) ℝ → List ℝ
  | [] => []
  | (.eval _ _ _, _) :: rest => cutReplies rest
  | (.cut _ _ _ _, x) :: rest => x :: cutReplies rest

@[simp] theorem cutReplies_nil : cutReplies (n := n) [] = [] := rfl

@[simp] theorem cutReplies_append (first second : History (Query (Fin n)) ℝ) :
    cutReplies (first ++ second) = cutReplies first ++ cutReplies second := by
  induction first with
  | nil => rfl
  | cons qr rest ih =>
    rcases qr with ⟨q, r⟩
    cases q <;> simp [cutReplies, ih]

@[simp] theorem cutReplies_length (trace : History (Query (Fin n)) ℝ) :
    (cutReplies trace).length = virtualCuts trace := by
  induction trace with
  | nil => rfl
  | cons qr rest ih =>
    rcases qr with ⟨q, r⟩
    cases q <;> simp [cutReplies, virtualCuts, isCutQuery, ih]

def Known (old : Set ℝ) (trace : History (Query (Fin n)) ℝ) : Set ℝ :=
  old ∪ {x | x ∈ cutReplies trace}

@[simp] theorem known_nil (old : Set ℝ) : Known (n := n) old [] = old := by
  ext x
  simp [Known]

theorem known_append (old : Set ℝ) (first second : History (Query (Fin n)) ℝ) :
    Known old (first ++ second) = Known (Known old first) second := by
  ext x
  simp only [Known, mem_union, mem_ofPred_eq, cutReplies_append, List.mem_append]
  tauto

theorem known_mono (old : Set ℝ) (first second : History (Query (Fin n)) ℝ) :
    Known old first ⊆ Known old (first ++ second) := by
  rw [known_append]
  exact subset_union_left

/-- A returned coordinate has either already been recorded in the inherited
cache, or is literally a response to a Cut in this execution. -/
def FromTrace (cache : List (Parent n)) (trace : History (Query (Fin n)) ℝ) (x : ℝ) : Prop :=
  Aligned cache x ∨ x ∈ cutReplies trace

/-- Spatial order makes every inherited component endpoint an already
recorded boundary, including endpoints of zero-length components. -/
theorem ordered_compare {cache : List (Parent n)} (h : Ordered cache)
    {p q : Parent n} (hp : p ∈ cache) (hq : q ∈ cache) :
    p.right ≤ q.left ∨ q.right ≤ p.left ∨ p = q := by
  let R : Parent n → Parent n → Prop := fun p q =>
    p.right ≤ q.left ∨ q.right ≤ p.left ∨ p = q
  have hf : cache.Pairwise R := h.imp (fun hab => Or.inl hab)
  have hr : cache.Pairwise (fun a b => R b a) := h.imp (fun hab => Or.inr (Or.inl hab))
  have hdiag : ∀ p ∈ cache, R p p := fun _ _ => Or.inr (Or.inr rfl)
  exact List.Pairwise.forall_of_forall_of_flip hdiag hf hr hp hq

theorem inherited_left_aligned (P : Profile (Fin n)) {cache : List (Parent n)}
    (hv : Valid P cache) (ho : Ordered cache) {p : Parent n} (hp : p ∈ cache) :
    Aligned cache p.left := by
  intro q hq
  have hb := ((valid_iff_forall P cache).mp hv p hp).1.2.1
  rcases ordered_compare ho hq hp with h | h | rfl
  · exact Or.inl h
  · exact Or.inr (hb.trans h)
  · exact Or.inr le_rfl

theorem inherited_right_aligned (P : Profile (Fin n)) {cache : List (Parent n)}
    (hv : Valid P cache) (ho : Ordered cache) {p : Parent n} (hp : p ∈ cache) :
    Aligned cache p.right := by
  intro q hq
  have hb := ((valid_iff_forall P cache).mp hv p hp).1.2.1
  rcases ordered_compare ho hq hp with h | h | rfl
  · exact Or.inl (h.trans hb)
  · exact Or.inr h
  · exact Or.inl le_rfl

/-- Deduplication is physical: a point already aligned in the inherited cache
requires no recording pass. -/
def freshPoints (cache : List (Parent n)) (points : List ℝ) : Finset ℝ :=
  points.toFinset.filter (fun x => ¬ Aligned cache x)

@[simp] theorem mem_freshPoints (cache : List (Parent n)) (points : List ℝ) (x : ℝ) :
    x ∈ freshPoints cache points ↔ x ∈ points ∧ ¬ Aligned cache x := by
  simp [freshPoints]

theorem freshPoints_card_le {cache : List (Parent n)} {points : List ℝ}
    {trace : History (Query (Fin n)) ℝ}
    (h : ∀ x ∈ points, FromTrace cache trace x) :
    (freshPoints cache points).card ≤ virtualCuts trace := by
  have hsub : freshPoints cache points ⊆ (cutReplies trace).toFinset := by
    intro x hx
    obtain ⟨hx, hnew⟩ := (mem_freshPoints cache points x).mp hx
    exact List.mem_toFinset.mpr ((h x hx).resolve_left hnew)
  exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans_eq (cutReplies_length trace))

def recordProgram (cache : List (Parent n)) (points : List ℝ) :
    Program (Query (Fin n)) ℝ (List (Parent n)) :=
  alignManyProgram (freshPoints cache points).toList cache

/-- Actual return recording costs at most n Evals per Cut-created endpoint,
not n times the preceding query count.  The source execution's provenance
is a separate, explicit hypothesis of this local compiler lemma. -/
theorem record_correct (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid P U cache)
    (points : List ℝ) (source : History (Query (Fin n)) ℝ)
    (hsource : ∀ x ∈ points, FromTrace cache source x)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordProgram cache points) prior fresh trace ∧
      trace.length ≤ n * virtualCuts source ∧ virtualCuts trace = 0 ∧
      CacheValid P U fresh ∧ (∀ x ∈ points, Aligned fresh x) ∧
      (∀ x, Aligned cache x → Aligned fresh x) ∧
      fresh.length ≤ cache.length + virtualCuts source := by
  obtain ⟨fresh, trace, hexec, hlen, hcuts, hcache, halign, hold, hcount⟩ :=
    align_many_correct P oracle hpolicy U (freshPoints cache points).toList cache hc prior
  have hcard := freshPoints_card_le hsource
  have hlength : (freshPoints cache points).toList.length ≤ virtualCuts source := by
    simpa using hcard
  refine ⟨fresh, trace, hexec, hlen.trans (Nat.mul_le_mul_left n hlength), hcuts,
    hcache, ?_, hold, hcount.trans (Nat.add_le_add_left hlength cache.length)⟩
  intro x hx
  by_cases holdx : Aligned cache x
  · exact hold x holdx
  · exact halign x (Finset.mem_toList.mpr ((mem_freshPoints cache points x).mpr ⟨hx, holdx⟩))

end EnvyFreeResearch.Full.Chores.Boundary
