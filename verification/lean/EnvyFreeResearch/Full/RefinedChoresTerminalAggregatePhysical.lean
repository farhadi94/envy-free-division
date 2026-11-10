import EnvyFreeResearch.Full.RefinedChoresTerminalAggregateDonor
import EnvyFreeResearch.Full.ChoresComponentExtraction

/-! Root-local affine donor deviations are actual complementary-piece
values. They can be transported into the complete valid package pool. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
open Set MeasureTheory IntervalOracle OracleProtocol
open ChoreComposition Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentExtraction
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (A : Finset (Fin n)) (p : Fin n)
    (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ A → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) A)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (parent blocks : Root → Fin n → Set ℝ)
    (hparts : PartsCorrect cost (domains blocks (fun _ => p)) Subtype.val out)
    (hblock : ∀ s, blocks s p ⊆ parent s p)
    (hgap : ∀ s i, gap s p i = (cost i).real (parent s p)-(frames s).baseline i)
include hparts hblock hgap

theorem actual_donor_physical_value (j : A) (i : Fin n) :
    (actualDonor A p frames hpath gap out j).cost i p =
      (cost i).real (parent (out.allocation.assigned j) p \ material (out.parts j).suffixParts) := by
  have hsub := (suffix_subset cost blocks (Subtype.val : A → Fin n) (fun _ => p) out hparts j).trans
    (hblock _)
  rw [measureReal_sdiff hsub (material_measurable _)]
  simp only [actualDonor,donorProposal,affineProposal,Proposal.output,ite_true,utilities,
    dite_eq_left j.property]
  rw [suffix_values cost blocks (Subtype.val : A → Fin n) (fun _ => p) gap out hparts, hgap]
  ring

theorem actual_donor_deviation (j : A) (i : Fin n) :
    (actualDonor A p frames hpath gap out j).cost i p-
      (actualDonor A p frames hpath gap out j).baseline i =
      (cost i).real (parent (out.allocation.assigned j) p \ material (out.parts j).suffixParts)-
        (frames (out.allocation.assigned j)).baseline i := by
  rw [actual_donor_physical_value A p frames hpath gap out cost parent blocks hparts hblock hgap,
    actual_donor_baseline]

/-- A concrete complementary donor deviation survives all frozen ancestors
and every other valid package, with no synchronized-component assumption. -/
theorem full_pool_margin
    (pool : List (Package (Fin n) RootId)) (hp : PoolValid pool) (hd : PoolDistinct pool)
    (G : PackageGeometry.Pieces RootId (Fin n)) (cache : RootId → Fin n → List (Parent n))
    (hsub : ∀ root a, material (cache root a) ⊆ G.piece root a)
    (hcost : ∀ a ∈ pool.flatMap Package.allocations, ∀ i q,
      a.cost i q=(cost i).real (material (cache a.root q)))
    (j : A) (hmem : actualDonor A p frames hpath gap out j ∈ pool.flatMap Package.allocations)
    (i : Fin n) (hij : i ≠ (j:Fin n)) (D : ℝ)
    (hwitness : D ≤ (cost i).real
      (parent (out.allocation.assigned j) p \ material (out.parts j).suffixParts)-
        (frames (out.allocation.assigned j)).baseline i) :
    D ≤ (cost i).real (Chores.ComponentPhysical.bundle (Chores.Outer.closePool pool) cache j)-
      (cost i).real (Chores.ComponentPhysical.bundle (Chores.Outer.closePool pool) cache i) := by
  apply Chores.Terminal.pool_recipient_witness_margin pool hp hd G cache hsub cost hcost
    i j p hij (actualDonor A p frames hpath gap out j) hmem
    (actual_donor_owner A p frames hpath gap out j) D
  rw [← hcost _ hmem i p]
  rw [actual_donor_deviation A p frames hpath gap out cost parent blocks hparts hblock hgap]
  exact hwitness

end EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
