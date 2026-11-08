import EnvyFreeResearch.Full.ChoresComponentDonors
import EnvyFreeResearch.Full.ChoresAugmentCache

/-! All-observer finite-union caches for the actual complementary donor
pieces.  Assembly is free computation on already recorded intervals;
positive-length zero-cost components remain material. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentPieces
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ComponentRecording
open ChoreComposition
open scoped Classical

variable {n : ℕ}

def complementCache (frontier : List (Parent n)) (parts : Split n) : List (Parent n) :=
  Augment.assemble (frontier ++ parts.prefixParts)

theorem complement_cache_correct (P : Profile (Fin n)) (parent front : Set ℝ)
    (frontier : List (Parent n)) (parts : Split n) (point : ℝ)
    (hprefix : front ⊆ parent) (hparent : parent ⊆ Ioc (0 : ℝ) 1)
    (hfrontier : CacheValid P front frontier)
    (hparts : Correct P (parent \ front) point parts) :
    CacheValid P (parent \ material parts.suffixParts) (complementCache frontier parts) := by
  have hd : Disjoint (material frontier) (material parts.prefixParts) := by
    rw [hfrontier.2.2, hparts.1.2.2]
    exact disjoint_left.mpr (fun x hx hy => hy.1.2 hx)
  obtain ⟨hv, ho, hm⟩ := Augment.assemble_join P frontier parts.prefixParts
    hfrontier.1 hparts.1.1 hfrontier.2.1 hparts.1.2.1 hd
  refine ⟨hv, ho, ?_⟩
  rw [complementCache, hm, hfrontier.2.2, hparts.1.2.2, hparts.2.2.2]
  ext x
  constructor
  · rintro (hx | hx)
    · exact ⟨hprefix hx, fun h => h.1.2 hx⟩
    · exact ⟨hx.1.1, fun h => (not_lt_of_ge hx.2) h.2.1⟩
  · rintro ⟨hx, hnot⟩
    by_cases hp : x ∈ front
    · exact Or.inl hp
    · right
      refine ⟨⟨hx, hp⟩, ?_⟩
      by_contra hgt
      exact hnot ⟨⟨hx, hp⟩, lt_of_not_ge hgt, (hparent hx).2⟩

def proposalCache {RootId : Type*}
    (equalizer : Fin n → Fin n → List (Parent n)) (frontier : List (Parent n))
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (parts : Split n)
    (p : Fin n) : List (Parent n) :=
  if proposal.execute then
    if p = proposal.label then complementCache frontier parts else equalizer p (proposal.owner p)
  else equalizer p (proposal.before.owner p)

theorem proposal_cache_correct {RootId : Type*} (P : Profile (Fin n))
    (parent : Fin n → Set ℝ) (equalizer : Fin n → Fin n → List (Parent n))
    (frontier : List (Parent n)) (proposal : ChoreComposition.Proposal (Fin n) RootId)
    (parts : Split n) (point : ℝ)
    (hfrontier : CacheValid P (material frontier) frontier)
    (hequalizer : ∀ p j, CacheValid P (material (equalizer p j)) (equalizer p j))
    (hprefix : material frontier ⊆ parent proposal.label)
    (hparent : parent proposal.label ⊆ Ioc (0 : ℝ) 1)
    (hparts : Correct P (parent proposal.label \ material frontier) point parts)
    (p : Fin n) :
    CacheValid P
      (PackageGeometry.proposalPiece parent (fun p j => material (equalizer p j)) proposal
        (material parts.suffixParts) p)
      (proposalCache equalizer frontier proposal parts p) := by
  cases he : proposal.execute with
  | false => simpa only [proposalCache, PackageGeometry.proposalPiece, he,
      Bool.false_eq_true, ite_false] using hequalizer p (proposal.before.owner p)
  | true =>
    by_cases hp : p = proposal.label
    · subst p
      simpa only [proposalCache, PackageGeometry.proposalPiece, he, ite_true] using
        complement_cache_correct P (parent proposal.label) (material frontier) frontier parts
          point hprefix hparent hfrontier hparts
    · simpa only [proposalCache, PackageGeometry.proposalPiece, he, ite_true,
        ite_eq_right hp] using hequalizer p (proposal.owner p)

theorem proposal_cache_values {RootId : Type*} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (parent : Fin n → Set ℝ) (equalizer : Fin n → Fin n → List (Parent n))
    (frontier : List (Parent n)) (proposal : ChoreComposition.Proposal (Fin n) RootId)
    (parts : Split n) (point : ℝ)
    (hfrontier : CacheValid (measureProfile cost) (material frontier) frontier)
    (hequalizer : ∀ p j, CacheValid (measureProfile cost) (material (equalizer p j)) (equalizer p j))
    (hprefix : material frontier ⊆ parent proposal.label)
    (hparent : parent proposal.label ⊆ Ioc (0 : ℝ) 1)
    (hparts : Correct (measureProfile cost) (parent proposal.label \ material frontier) point parts)
    (i p : Fin n) :
    cachedValue (proposalCache equalizer frontier proposal parts p) i =
      (cost i).real (PackageGeometry.proposalPiece parent
        (fun p j => material (equalizer p j)) proposal (material parts.suffixParts) p) := by
  have h := proposal_cache_correct (measureProfile cost) parent equalizer frontier proposal
    parts point hfrontier hequalizer hprefix hparent hparts p
  rw [← h.2.2, material_value cost _ h.1 h.2.1]

end EnvyFreeResearch.Full.Chores.ComponentPieces
