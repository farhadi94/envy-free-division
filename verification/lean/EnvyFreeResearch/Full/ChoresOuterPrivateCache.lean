import EnvyFreeResearch.Full.ChoresOuterInitial
import EnvyFreeResearch.Full.ChoresComponentResidueCache

/-! Actual cached private complements, maintained from recorded suffixes. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical
variable {n : ℕ} {RootId : Type*}

def PrivateCorrect (P : Profile (Fin n)) (parent : RootId → Fin n → Set ℝ)
    (retained privateCache : RootId → Fin n → List (Parent n)) : Prop :=
  ∀ r p, CacheValid P (parent r p \ material (retained r p)) (privateCache r p)

theorem private_initial (P : Profile (Fin n)) (original : RootId → Snapshot.Output n) :
    PrivateCorrect P (fun r => (original r).piece) (fun r => (original r).parents)
      (fun _ _ => []) := by
  intro r p
  change CacheValid P (material ((original r).parents p) \ material ((original r).parents p)) []
  simp [CacheValid, Valid, Ordered, material]

theorem private_filter (data : Data n RootId) (P : Profile (Fin n))
    (parent : RootId → Fin n → Set ℝ) (privateCache : RootId → Fin n → List (Parent n))
    (h : PrivateCorrect P parent data.cache privateCache) (kept : List (Fin data.size)) :
    PrivateCorrect P parent (data.filter kept).cache privateCache := h

theorem private_reveal (data : Data n RootId) (P : Profile (Fin n))
    (parent : RootId → Fin n → Set ℝ) (privateCache : RootId → Fin n → List (Parent n))
    (h : PrivateCorrect P parent data.cache privateCache)
    (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (proposed : Scheduler.Proposal (Fin data.size) (Fin n))
    (hv : proposed.Valid data.pending.partition p) :
    PrivateCorrect P parent (data.reveal p hp proposed hv).cache privateCache := h

/-- Both caches use exactly the same selected old root, including batch slots. -/
theorem private_patch {Slot : Type*} [Fintype Slot] (frames : Slot → ChoreComposition.Frame (Fin n) RootId)
    (P : Profile (Fin n)) (parent : RootId → Fin n → Set ℝ)
    (old oldPrivate : RootId → Fin n → List (Parent n))
    (next nextPrivate : Slot → Fin n → List (Parent n))
    (hold : PrivateCorrect P parent old oldPrivate)
    (hnext : ∀ s p, CacheValid P (parent (frames s).root p \ material (next s p)) (nextPrivate s p)) :
    PrivateCorrect P parent (ComponentPhysical.patchCache frames old next)
      (ComponentPhysical.patchCache frames oldPrivate nextPrivate) := by
  intro r p
  unfold ComponentPhysical.patchCache
  split
  next h =>
    have hh := hnext h.choose p
    simpa only [h.choose_spec] using hh
  next _ => exact hold r p

theorem private_equalizer (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (original : Snapshot.Output n) (c : Fin n) (U : Set ℝ)
    (hs : Snapshot.Sound cost U c original) (p j : Fin n) :
    CacheValid (measureProfile cost)
      (original.piece p \ material (original.equalizers (p,j)).parts.prefixParts)
      (original.equalizers (p,j)).parts.suffixParts := by
  have hc := snapshot_equalizers hs p j
  rw [hc.2.1.2.2]
  have heq : original.piece p \ (original.piece p ∩ Iic (original.equalizers (p,j)).point)=
      original.piece p ∩ Ioi (original.equalizers (p,j)).point := by
    ext x
    simp only [mem_sdiff, mem_inter_iff, mem_Iic, mem_Ioi]
    constructor
    · rintro ⟨hx,hn⟩
      exact ⟨hx,lt_of_not_ge (fun hh => hn ⟨hx,hh⟩)⟩
    · rintro ⟨hx,hh⟩
      exact ⟨hx,fun h => (not_le_of_gt hh) h.2⟩
  rw [heq]
  exact hc.2.2.1
end EnvyFreeResearch.Full.Chores.Outer
