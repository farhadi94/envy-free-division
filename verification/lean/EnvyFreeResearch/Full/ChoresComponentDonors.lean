import EnvyFreeResearch.Full.ChoresComponentPayments
import EnvyFreeResearch.Full.ChoresSchedulerGraphRound

/-! Concrete donor permutations and physical proposal tables for component payments. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentDonors
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Persistent SubCorePhysical SubCoreLeaves Suffix SubCoreEntry ComponentRecording
open ComponentPayments Components Scheduler ChoreComposition
open scoped Classical

variable {n : ℕ} {Task Root RootId : Type*} [Fintype Task] [DecidableEq Task]
  [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (frames : Root → Frame (Fin n) RootId) (agent : Task → Fin n)
  (gap : Root → Fin n → Fin n → ℝ)

def owner {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task) :
    Equiv.Perm (Fin n) :=
  donorMatching (visited.graph (out.allocation.assigned j))
    (state.partition.representative (agent j)) (agent j)
    ((visited.exact _ _ _).mpr (state.partition.fixed (agent j)).symm)

theorem owner_recipient {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task) :
    owner state visited agent out j (state.partition.representative (agent j)) = agent j :=
  donorMatching_recipient _ _ _ _

theorem owner_other {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task)
    (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
    (p : Fin n) (hp : p ≠ state.partition.representative (agent j)) :
    owner state visited agent out j p ∈ (frames (out.allocation.assigned j)).allowed p := by
  apply (hallowed _ _ _).mpr
  rcases donorMatching_other (visited.graph (out.allocation.assigned j))
      (state.partition.representative (agent j)) (agent j) _ hp with heq | he
  · exact ⟨1, visited.identity _, by simpa only [owner, Equiv.Perm.one_apply] using heq.symm⟩
  · exact he

def ordinary {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task) :
    ChoreComposition.Proposal (Fin n) RootId :=
  ordinaryProposal (frames (out.allocation.assigned j))
    (state.partition.representative (agent j)) (agent j)
    (owner state visited agent out j)
    (fun i => utility agent state.partition.representative gap out i j)

def affine {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task) :
    ChoreComposition.Proposal (Fin n) RootId :=
  affineProposal (frames (out.allocation.assigned j))
    (state.partition.representative (agent j)) (agent j)
    (owner state visited agent out j)
    (fun i => utility agent state.partition.representative gap out i j)

theorem ordinary_good {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task)
    (hframes : ∀ s, (frames s).Good)
    (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i) :
    (ordinary state visited frames agent gap out j).Good :=
  ordinary_proposal_good _ (hframes _) _ _ _ _
    (owner_recipient state visited agent out j)
    (owner_other state visited frames agent out j hallowed)

theorem affine_good {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task)
    (hframes : ∀ s, (frames s).Good)
    (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
    (hnonnegative : 0 ≤ utility agent state.partition.representative gap out (agent j) j) :
    (affine state visited frames agent gap out j).Good :=
  affine_proposal_good _ (hframes _) _ _ _ _
    (owner_recipient state visited agent out j)
    (owner_other state visited frames agent out j hallowed) hnonnegative

theorem ordinary_nonpositive {Payload : Type*} (out : Recorded Payload Task Root n) (j : Task)
    (hzero : utility agent state.partition.representative gap out (agent j) j ≤ 0) :
    (ordinary state visited frames agent gap out j).output =
      (frames (out.allocation.assigned j)).allocation :=
  ordinary_nonpositive_is_unchanged _ _ _ _ _ hzero

private theorem output_decidable (proposal : ChoreComposition.Proposal (Fin n) RootId) :
    @ChoreComposition.Proposal.output (Fin n) RootId (instDecidableEqFin n) proposal =
      @ChoreComposition.Proposal.output (Fin n) RootId
        (fun a b => Classical.propDecidable (a = b)) proposal := by
  have h : (instDecidableEqFin n) = (fun a b : Fin n => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [h]

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks parent : Root → Fin n → Set ℝ)
  (equalizer : Root → Fin n → Fin n → Set ℝ)
  (hblock : ∀ s p, blocks s p ⊆ parent s p)
  (hequalizer : ∀ s i p j, (frames s).equalizerCost i p j = (cost i).real (equalizer s p j))
  (hgap : ∀ s p i, gap s p i = (cost i).real (parent s p) - (frames s).baseline i)
  {Payload : Type*} (out : Recorded Payload Task Root n)
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) agent out)
include hblock hequalizer hgap hparts


theorem ordinary_piece_value (j : Task) (i p : Fin n) :
    (ordinary state visited frames agent gap out j).output.cost i p =
      (cost i).real (PackageGeometry.proposalPiece (parent (out.allocation.assigned j))
        (equalizer (out.allocation.assigned j))
        (ordinary state visited frames agent gap out j)
        (material (out.parts j).suffixParts) p) := by
  rw [output_decidable]
  apply PackageGeometry.proposal_piece_value
  · exact (suffix_subset cost blocks agent state.partition.representative out hparts j).trans (hblock _ _)
  · exact material_measurable _
  · exact hequalizer _
  · intro a
    change utility agent state.partition.representative gap out a j = _
    rw [suffix_values cost blocks agent state.partition.representative gap out hparts, hgap]
    rfl

theorem affine_piece_value (j : Task) (i p : Fin n) :
    (affine state visited frames agent gap out j).output.cost i p =
      (cost i).real (PackageGeometry.proposalPiece (parent (out.allocation.assigned j))
        (equalizer (out.allocation.assigned j))
        (affine state visited frames agent gap out j)
        (material (out.parts j).suffixParts) p) := by
  rw [output_decidable]
  apply PackageGeometry.proposal_piece_value
  · exact (suffix_subset cost blocks agent state.partition.representative out hparts j).trans (hblock _ _)
  · exact material_measurable _
  · exact hequalizer _
  · intro a
    change utility agent state.partition.representative gap out a j = _
    rw [suffix_values cost blocks agent state.partition.representative gap out hparts, hgap]
    rfl

end EnvyFreeResearch.Full.Chores.ComponentDonors
