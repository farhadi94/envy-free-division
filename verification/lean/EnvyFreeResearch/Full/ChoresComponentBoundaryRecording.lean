import EnvyFreeResearch.Full.ChoresComponentBoundarySubCorePhysical
import EnvyFreeResearch.Full.ChoresComponentRecordedSubCore

/-! The paid final retained-suffix recording pass queries only boundaries
already present in the compiled SubCore ledger. Its physical prefix/suffix
parts preserve that same ledger, including all zero-cost material. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent
open SubCorePhysical ComponentRecording
open scoped Classical

variable {n : ℕ} {Task Root Payload : Type*}

theorem retained_record_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (cache : List (Parent n)) (hcache : CacheKnown points cache)
    (point : ℝ) (hpoint : point ∈ points) (prior : History (Query (Fin n)) ℝ)
    (out : Split n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ComponentRecording.recordProgram cache point) prior out trace) :
    CacheKnown points (out.prefixParts++out.suffixParts) ∧ Scoped points trace := by
  obtain ⟨fresh, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  obtain ⟨hc, hscope⟩ := align_known oracle points point hpoint cache hcache prior fresh first hf
  exact ⟨(hc.filter _).append (hc.filter _), hscope⟩

theorem retained_list_known [DecidableEq Task]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (cache : Task → List (Parent n)) (hcache : ∀ task, CacheKnown points (cache task))
    (point : Task → ℝ) (hpoint : ∀ task, point task ∈ points)
    (tasks : List Task) (prior : History (Query (Fin n)) ℝ) (out : Task → Split n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ComponentRecording.recordList cache point tasks) prior out trace) :
    (∀ task, CacheKnown points ((out task).prefixParts++(out task).suffixParts)) ∧ Scoped points trace := by
  induction tasks generalizing prior out trace with
  | nil =>
    cases h
    exact ⟨by simp [CacheKnown], trivial⟩
  | cons task rest ih =>
    obtain ⟨first, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
    obtain ⟨tail, t₃, t₄, h₃, h₄, ht₂⟩ := Executes.split_bind _ _ h₂
    cases h₄
    simp only [List.append_nil] at ht₂
    subst t₂
    subst trace
    obtain ⟨hf, hs₁⟩ := retained_record_known oracle points (cache task) (hcache task) (point task)
      (hpoint task) prior first t₁ h₁
    obtain ⟨ht, hs₂⟩ := ih (prior++t₁) tail t₃ h₃
    refine ⟨?_, (scoped_append points t₁ t₃).mpr ⟨hs₁, hs₂.mono subset_union_left⟩⟩
    intro j
    by_cases hj : j = task
    · subst j
      simpa only [Function.update_self] using hf
    · simpa only [Function.update_of_ne hj] using ht j

def RecordedKnown (view : Payload → Record n) (points : Set ℝ) (out : Recorded Payload Task Root n) : Prop :=
  SuffixStoreKnown view points out.store ∧ MaskedCacheKnown points out.cache ∧
    (∀ p, 1-(out.allocation.point p).record.point ∈ points) ∧
    (∀ task, CacheKnown points ((out.parts task).prefixParts++(out.parts task).suffixParts))

theorem RecordedKnown.mono {view : Payload → Record n} {old more : Set ℝ}
    {out : Recorded Payload Task Root n} (h : RecordedKnown view old out) (hm : old ⊆ more) :
    RecordedKnown view more out :=
  ⟨h.1.mono hm, h.2.1.mono hm, fun p => hm (h.2.2.1 p), fun task => (h.2.2.2 task).mono hm⟩

theorem retained_finish_known [Fintype Task] [DecidableEq Task]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (view : Payload → Record n) (points : Set ℝ) (agent : Task → Fin n)
    (store : SubCorePhysical.Store Root Payload) (hstore : SuffixStoreKnown view points store)
    (out : SubCore.Allocation Task Root (OrderedRecord n))
    (hpoints : ∀ p, 1-(out.point p).record.point ∈ points)
    (cache : Masked.Cache Root n) (hcache : MaskedCacheKnown points cache)
    (prior : History (Query (Fin n)) ℝ) (result : Recorded Payload Task Root n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (finishProgram agent store out cache) prior result trace) :
    RecordedKnown view points result ∧ Scoped points trace := by
  obtain ⟨parts, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  have hh := retained_list_known oracle points (fun j => cache (out.assigned j) (agent j))
    (fun j => hcache (out.assigned j) (agent j)) (fun j => 1-(out.point (out.assigned j)).record.point)
    (fun j => hpoints (out.assigned j)) Finset.univ.toList prior parts first hf
  exact ⟨⟨hstore, hcache, hpoints, hh.1⟩, hh.2⟩

end EnvyFreeResearch.Full.Chores.Boundary
