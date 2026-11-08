import EnvyFreeResearch.Full.ChoresComponentActiveOutput
import EnvyFreeResearch.Full.ChoresComponentBoundary

/-! Native-population input projection and exact ambient cache restoration.
Projection reads existing cached observer rows and makes no query. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ActivePopulation
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n k : ℕ}

def projectPart (agent : Fin k → Fin n) (p : Parent n) : Parent k :=
  ⟨p.left, p.right, fun i => p.value (agent i)⟩

def projectCache (agent : Fin k → Fin n) (cache : List (Parent n)) : List (Parent k) :=
  cache.map (projectPart agent)

@[simp] theorem project_material (agent : Fin k → Fin n) (cache : List (Parent n)) :
    material (projectCache agent cache) = material cache := by
  induction cache with
  | nil => rfl
  | cons p rest ih =>
    exact congrArg (fun U => Ioc p.left p.right ∪ U) ih

theorem project_valid (P : Profile (Fin n)) (agent : Fin k → Fin n) (cache : List (Parent n))
    (h : Valid P cache) : Valid (ActiveCore.profile P agent) (projectCache agent cache) := by
  apply (valid_iff_forall _ _).mpr
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hv := (valid_iff_forall _ _).mp h q hq
  exact ⟨hv.1, fun i => hv.2 (agent i)⟩

theorem project_ordered (agent : Fin k → Fin n) (cache : List (Parent n)) (h : Ordered cache) :
    Ordered (projectCache agent cache) := by
  simpa only [Ordered, projectCache, List.pairwise_map, projectPart] using h

theorem project_cache_valid (P : Profile (Fin n)) (agent : Fin k → Fin n)
    (U : Set ℝ) (cache : List (Parent n)) (h : CacheValid P U cache) :
    CacheValid (ActiveCore.profile P agent) U (projectCache agent cache) :=
  ⟨project_valid P agent cache h.1, project_ordered agent cache h.2.1, (project_material agent cache).trans h.2.2⟩

@[simp] theorem project_aligned (agent : Fin k → Fin n) (cache : List (Parent n)) (x : ℝ) :
    Aligned (projectCache agent cache) x ↔ Aligned cache x := by
  constructor
  · intro h p hp
    exact h (projectPart agent p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact h q hq

def ranges (parts : List (Parent k)) : List (ℝ × ℝ) := parts.map (fun p => (p.left, p.right))

theorem ranges_material (parts : List (Parent k)) : rangeMaterial (ranges parts) = material parts := by
  ext x
  simp only [rangeMaterial, ranges, mem_ofPred_eq, List.mem_map, mem_material_iff]
  constructor
  · rintro ⟨r, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨_, ⟨p, hp, rfl⟩, hx⟩

def restore (cache : List (Parent n)) (out : Completion.Allocation k (Fin k)) :
    Completion.Allocation n (Fin k) :=
  ⟨fun i => selectWindows (ranges (out.pieces i)) cache⟩

def endpoints (out : Completion.Allocation n (Fin k)) : List ℝ :=
  (List.ofFn out.pieces).flatMap (fun parts => parts.flatMap (fun p => [p.left, p.right]))

theorem mem_endpoints (out : Completion.Allocation n (Fin k)) (i : Fin k)
    (p : Parent n) (hp : p ∈ out.pieces i) : p.left ∈ endpoints out ∧ p.right ∈ endpoints out := by
  constructor <;> apply List.mem_flatMap.mpr <;>
    refine ⟨out.pieces i, List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_flatMap.mpr ⟨p, hp, ?_⟩⟩ <;> simp

theorem restore_cache (P : Profile (Fin n)) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid P U cache) (out : Completion.Allocation k (Fin k))
    (halign : ∀ x ∈ endpoints out, Aligned cache x)
    (hsub : ∀ i, material (out.pieces i) ⊆ U) (i : Fin k) :
    CacheValid P (material (out.pieces i)) ((restore cache out).pieces i) := by
  have hbound : ∀ r ∈ ranges (out.pieces i), Aligned cache r.1 ∧ Aligned cache r.2 := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have he := mem_endpoints out i p hp
    exact ⟨halign p.left he.1, halign p.right he.2⟩
  have h := selected_cache P U cache hc (ranges (out.pieces i)) hbound
  simpa only [restore, ranges_material, inter_eq_right.mpr (hsub i)] using h

theorem restore_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k → Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (out : Completion.Allocation k (Fin k))
    (hs : out.Sound (fun i => cost (agent i)) id U)
    (halign : ∀ x ∈ endpoints out, Aligned cache x) :
    (restore cache out).Sound cost agent U := by
  have hcaches := restore_cache (measureProfile cost) U cache hc out halign
    (fun i => hs.subset _ id U out i)
  have hm (i : Fin k) : material ((restore cache out).pieces i) = material (out.pieces i) :=
    (hcaches i).2.2
  constructor
  · intro i
    exact ⟨(hcaches i).1, (hcaches i).2.1, rfl⟩
  · intro i j hij
    rw [hm i, hm j]
    exact hs.disjoint hij
  · simpa only [hm] using hs.cover
  · intro i j
    rw [hm i, hm j]
    exact hs.envy_free i j

theorem cutReplies_lift (agent : Fin k → Fin n) (trace : History (Query (Fin k)) ℝ) :
    Boundary.cutReplies (ActiveCore.liftHistory agent trace) = Boundary.cutReplies trace := by
  induction trace with
  | nil => rfl
  | cons qr rest ih =>
    rcases qr with ⟨q, r⟩
    cases q with
    | eval i a b => exact ih
    | cut i a b t => exact congrArg (List.cons r) ih

end EnvyFreeResearch.Full.Chores.ActivePopulation
