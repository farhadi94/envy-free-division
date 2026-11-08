import EnvyFreeResearch.Full.ChoresComponentPieceCache

/-! Literal complementary residue caches for executed and unchanged
donors. An affine-zero assignment retains its complete removed suffix;
an unexecuted ordinary assignment retains its old private complement. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentPieces
open Set IntervalOracle InitialPartition OrderedUnion ComponentRecording ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*}

def proposalResidueCache (equalizerSuffix : Fin n → Fin n → List (Parent n))
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (parts : Split n)
    (p : Fin n) : List (Parent n) :=
  if proposal.execute then
    if p = proposal.label then parts.suffixParts else equalizerSuffix p (proposal.owner p)
  else equalizerSuffix p (proposal.before.owner p)

theorem proposal_residue_cache_correct (P : Profile (Fin n))
    (parent : Fin n → Set ℝ) (equalizer : Fin n → Fin n → List (Parent n))
    (equalizerSuffix : Fin n → Fin n → List (Parent n))
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (parts : Split n)
    (hsuffix : ∀ p j, CacheValid P (parent p \ material (equalizer p j)) (equalizerSuffix p j))
    (hparts : CacheValid P (material parts.suffixParts) parts.suffixParts)
    (hsub : material parts.suffixParts ⊆ parent proposal.label) (p : Fin n) :
    CacheValid P
      (parent p \ PackageGeometry.proposalPiece parent
        (fun p j => material (equalizer p j)) proposal (material parts.suffixParts) p)
      (proposalResidueCache equalizerSuffix proposal parts p) := by
  cases he : proposal.execute with
  | false => simpa only [proposalResidueCache, PackageGeometry.proposalPiece, he,
      Bool.false_eq_true, ite_false] using hsuffix p (proposal.before.owner p)
  | true =>
    by_cases hp : p = proposal.label
    · subst p
      have heq : parent proposal.label \ (parent proposal.label \ material parts.suffixParts) =
          material parts.suffixParts := by
        ext x
        constructor
        · rintro ⟨hx, hn⟩
          by_contra hs
          exact hn ⟨hx, hs⟩
        · intro hx
          exact ⟨hsub hx, fun hn => hn.2 hx⟩
      simpa only [proposalResidueCache, PackageGeometry.proposalPiece, he, ite_true, heq] using hparts
    · simpa only [proposalResidueCache, PackageGeometry.proposalPiece, he, ite_true,
        ite_eq_right hp] using hsuffix p (proposal.owner p)

theorem proposal_piece_residue_partition
    (parent : Fin n → Set ℝ) (equalizer : Fin n → Fin n → Set ℝ)
    (hsub : ∀ p j, equalizer p j ⊆ parent p)
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (removed : Set ℝ) (p : Fin n) :
    Disjoint (PackageGeometry.proposalPiece parent equalizer proposal removed p)
      (parent p \ PackageGeometry.proposalPiece parent equalizer proposal removed p) ∧
    PackageGeometry.proposalPiece parent equalizer proposal removed p ∪
      (parent p \ PackageGeometry.proposalPiece parent equalizer proposal removed p) = parent p := by
  constructor
  · exact disjoint_left.mpr (fun x hx hy => hy.2 hx)
  · have hs := PackageGeometry.proposal_piece_subset parent equalizer hsub proposal removed p
    ext x
    constructor
    · rintro (hx | hx)
      · exact hs hx
      · exact hx.1
    · intro hx
      by_cases hy : x ∈ PackageGeometry.proposalPiece parent equalizer proposal removed p
      · exact Or.inl hy
      · exact Or.inr ⟨hx, hy⟩

end EnvyFreeResearch.Full.Chores.ComponentPieces
