import EnvyFreeResearch.Full.ChoresComponentBoundaryAugment
import EnvyFreeResearch.Full.ChoresCompletionProgram

/-! Concrete two-group preparation preserves parametric physical boundary
provenance through both near-equal refinements and both augmentations. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

variable {n b c k : ℕ}

def SplitKnown (points : Set ℝ) (out : SplitOutput n k) : Prop :=
  FamilyKnown points out.original ∧ WholeKnown points out.allocation

theorem SplitKnown.mono {old more : Set ℝ} {out : SplitOutput n k}
    (h : SplitKnown old out) (hm : old ⊆ more) : SplitKnown more out :=
  ⟨h.1.mono hm, h.2.mono hm⟩

theorem split_augment_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (observers : Finset (Fin n)) (recipient : ℕ → Fin n) (k : ℕ)
    (cache : List (Parent n)) (hcache : CacheKnown points cache)
    (prior : History (Query (Fin n)) ℝ) (out : SplitOutput n k)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (splitAugment observers recipient k cache) prior out trace) :
    SplitKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨split, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
  obtain ⟨allocation, t₃, t₄, h₃, h₄, ht₂⟩ := Executes.split_bind _ _ h₂
  cases h₄
  simp only [List.append_nil] at ht₂
  subst t₂
  subst trace
  obtain ⟨hgrid, hs₁⟩ := near_equal_known oracle points observers _ (countPieces_pos k) cache hcache prior split t₁ h₁
  have hparts : FamilyKnown (Known points t₁) split.parts := near_equal_parts_known _ split hgrid
  obtain ⟨hwhole, hs₃⟩ := augment_whole_known oracle (Known points t₁) recipient k split.parts hparts
    _ _ (prior++t₁) allocation t₃ h₃
  refine ⟨⟨hparts.mono (known_mono points t₁ t₃), ?_⟩,
    (scoped_append points t₁ t₃).mpr ⟨hs₁, hs₃⟩⟩
  simpa only [known_append] using hwhole

def PreparedKnown (points : Set ℝ) (out : Prepared n b c) : Prop :=
  SplitKnown points out.forB ∧ SplitKnown points out.forD

theorem PreparedKnown.mono {old more : Set ℝ} {out : Prepared n b c}
    (h : PreparedKnown old out) (hm : old ⊆ more) : PreparedKnown more out :=
  ⟨h.1.mono hm, h.2.mono hm⟩

theorem prepare_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (cacheX cacheR : List (Parent n)) (hX : CacheKnown points cacheX) (hR : CacheKnown points cacheR)
    (prior : History (Query (Fin n)) ℝ) (out : Prepared n b c)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (prepare agentB agentD hb hc cacheX cacheR) prior out trace) :
    PreparedKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨forD, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
  obtain ⟨forB, t₃, t₄, h₃, h₄, ht₂⟩ := Executes.split_bind _ _ h₂
  cases h₄
  simp only [List.append_nil] at ht₂
  subst t₂
  subst trace
  obtain ⟨hD, hs₁⟩ := split_augment_known oracle points _ _ c cacheX hX prior forD t₁ h₁
  obtain ⟨hB, hs₃⟩ := split_augment_known oracle (Known points t₁) _ _ b cacheR
    (hR.mono subset_union_left) (prior++t₁) forB t₃ h₃
  exact ⟨⟨by simpa only [known_append] using hB, hD.mono (known_mono points t₁ t₃)⟩,
    (scoped_append points t₁ t₃).mpr ⟨hs₁, hs₃⟩⟩

theorem attach_known {Label : Type*} (points : Set ℝ) (base : Augment.WholeOutput n k Label)
    (hbase : WholeKnown points base) (child : Allocation n (Fin k))
    (hchild : AllocationKnown points child) : AllocationKnown points (attach base child) :=
  fun i => assemble_known ((hbase.1 i).append (hchild i))

theorem sum_allocation_known (points : Set ℝ) (first : Allocation n (Fin b)) (second : Allocation n (Fin c))
    (hf : AllocationKnown points first) (hs : AllocationKnown points second) :
    AllocationKnown points (sumAllocation first second) := by
  intro i
  cases i with
  | inl a => exact hf a
  | inr a => exact hs a

theorem finish_prepared_known (points : Set ℝ) (prepared : Prepared n b c)
    (hp : PreparedKnown points prepared) (childB : Allocation n (Fin b)) (childD : Allocation n (Fin c))
    (hB : AllocationKnown points childB) (hD : AllocationKnown points childD) :
    AllocationKnown points (finishPrepared prepared childB childD) :=
  sum_allocation_known points _ _ (attach_known points _ hp.1.2 childB hB)
    (attach_known points _ hp.2.2 childD hD)

end EnvyFreeResearch.Full.Chores.Boundary
