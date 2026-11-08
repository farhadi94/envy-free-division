import EnvyFreeResearch.Full.ChoresComponentPhysicalJoin
import EnvyFreeResearch.Full.ChoresComponentPhysicalEF

/-! An open compensation group as an actual original-oracle program with
truthful physical output caches and envy-freeness. Every frozen ancestor
is retained in the output bundle; the new payment is derived internally. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentBatch
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCore SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle InitialPartition OrderedUnion
open OracleProtocol QueryProgram
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ)
  (hmany : Fintype.card (Task state hall cycle) < Fintype.card Root)
  (old : RootId → Fin n → List (Parent n))
  (equalizer : Root → Fin n → Fin n → List (Parent n))
  (frontier : Root → Fin n → List (Parent n))

def physicalProgram (cache : Masked.Cache Root n) :
    Program (Query (Fin n)) ℝ
      (Option (Result state hall cycle × (RootId → Fin n → List (Parent n)))) :=
  (program state hall cycle visited packages frames gap hmany cache).bind
    (fun result => match result with
      | none => .returned none
      | some (out, _) => .returned
          (some (out, patchedCache state hall cycle visited frames gap out old equalizer frontier)))

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (parent blocks : Root → Fin n → Set ℝ)
  (cache : Masked.Cache Root n)
  (hc : Masked.CacheCorrect (measureProfile cost) (domains blocks state.partition.representative) cache)
  (hnonnegative : ∀ s p i, 0 ≤ gap s p i)
  (hlive : ∀ s, (packages s).live = some (frames s))
  (hvalid : ∀ s, (packages s).Valid)
  (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
  (hequalized : ∀ s p i, (frames s).equalizerCost i p i = (frames s).baseline i)
  (hforbidden : ∀ s p, p ∈ state.selected hall cycle →
    (frames s).forbidden p ⊆ state.partition.component p)
  (hfrontierValue : ∀ s p, p ∈ state.selected hall cycle → ∀ i,
    (frames s).gap i (ComponentFrames.nextAgent state s p) p =
      (cost i).real (blocks s p) - gap s p i)
  (hprotect : ∀ p ∈ state.selected hall cycle, ∀ s i,
    i ∉ state.partition.component p → (cost i).real (blocks s p) ≤ gap s p i)
  (hcontain : ∀ s p, p ∈ state.selected hall cycle → ∀ i j, j ∈ (frames s).allowed p →
    (frames s).gap i j p ≤ (frames s).gap i (ComponentFrames.nextAgent state s p) p)
  (hp : ∀ s p, parent s p ⊆ Ioc (0 : ℝ) 1)
  (hf : ∀ s p, CacheValid (measureProfile cost) (material (frontier s p)) (frontier s p))
  (he : ∀ s p j, CacheValid (measureProfile cost) (material (equalizer s p j)) (equalizer s p j))
  (hfrontier : ∀ s p, material (frontier s p) ⊆ parent s p)
  (hblocks : ∀ s p, blocks s p = parent s p \ material (frontier s p))
  (hvalues : ∀ s i p j, (frames s).equalizerCost i p j = (cost i).real (material (equalizer s p j)))
  (hgap : ∀ s p i, gap s p i = (cost i).real (parent s p) - (frames s).baseline i)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hparent : ∀ s p, parent s p = G.piece (frames s).root p)
  (hesub : ∀ s p j, material (equalizer s p j) ⊆ parent s p)
  (holdsub : ∀ r p, material (old r p) ⊆ G.piece r p)
  (holdvalid : ∀ r p, Valid (measureProfile cost) (old r p) ∧ Ordered (old r p))
  (holdcost : ∀ s a, a ∈ (packages s).frozen → ∀ i p,
    a.cost i p = (cost i).real (material (old a.root p)))
  (hdistinct : (Finset.univ.toList.flatMap (fun s => (packages s).ids)).Nodup)
  (hcard : Fintype.card Root = Fintype.card (Task state hall cycle) + 1)

include hc hnonnegative hlive hvalid hallowed hequalized hforbidden hfrontierValue hprotect hcontain
  hp hf he hfrontier hblocks hvalues hgap hparent hesub holdsub holdvalid holdcost hdistinct hcard

theorem physical_program_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Result state hall cycle, ∃ updated : RootId → Fin n → List (Parent n),
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle
        (physicalProgram state hall cycle visited packages frames gap hmany old equalizer frontier cache)
        prior (some (out, updated)) trace ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card (Task state hall cycle)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card (Task state hall cycle)) ∧
      (outputPackage state hall cycle visited packages frames gap hmany out).Valid ∧
      (outputPackage state hall cycle visited packages frames gap hmany out).ids.Perm
        (Finset.univ.toList.flatMap (fun s => (packages s).ids)) ∧
      (∀ r p, Valid (measureProfile cost) (updated r p) ∧ Ordered (updated r p)) ∧
      (∀ r p, material (updated r p) ⊆ G.piece r p) ∧
      (∀ a ∈ (outputPackage state hall cycle visited packages frames gap hmany out).allocations,
        ∀ i p, a.cost i p = (cost i).real (material (updated a.root p))) ∧
      (∀ i, CacheValid (measureProfile cost)
        (ComponentPhysical.bundle (outputPackage state hall cycle visited packages frames gap hmany out) updated i)
        (ComponentPhysical.bundleCache (outputPackage state hall cycle visited packages frames gap hmany out) updated i)) ∧
      Pairwise (fun i j => Disjoint
        (ComponentPhysical.bundle (outputPackage state hall cycle visited packages frames gap hmany out) updated i)
        (ComponentPhysical.bundle (outputPackage state hall cycle visited packages frames gap hmany out) updated j)) ∧
      (∀ i j, (cost i).real
        (ComponentPhysical.bundle (outputPackage state hall cycle visited packages frames gap hmany out) updated i) ≤
        (cost i).real
        (ComponentPhysical.bundle (outputPackage state hall cycle visited packages frames gap hmany out) updated j)) := by
  obtain ⟨out, trace, hexec, hnewvalid, hcorrect, hparts, hlen, hcuts, hcache⟩ :=
    program_correct state hall cycle visited packages frames gap hmany cost blocks cache hc
      hnonnegative hlive hvalid hallowed hequalized hforbidden hfrontierValue hprotect hcontain
      oracle hpolicy prior
  let updated := patchedCache state hall cycle visited frames gap out old equalizer frontier
  have hids := output_ids state hall cycle visited packages frames gap hmany out cost blocks
    hparts hcorrect hcache hlive hvalid hallowed hequalized hforbidden hfrontierValue hprotect hcontain hcard
  have hnd := hids.nodup_iff.mpr hdistinct
  have hv := patched_cache_valid state hall cycle visited frames gap out old equalizer frontier
    cost parent blocks hp hf he hfrontier hblocks hparts holdvalid
  have hsub := patched_cache_subset state hall cycle visited frames gap out old equalizer frontier
    cost parent blocks hp hf he hfrontier hblocks hparts G hparent hesub holdsub
  have hcost := output_cost_realized state hall cycle visited packages frames gap out old equalizer frontier
    cost parent blocks hp hf he hfrontier hblocks hparts hvalues hgap hmany hlive hdistinct holdcost
  refine ⟨out, updated, trace, ?_, hlen, hcuts, hnewvalid, hids, hv, hsub, hcost, ?_, ?_, ?_⟩
  · simpa only [physicalProgram, List.append_nil] using hexec.bind
      (fun result => match result with
        | none => Program.returned none
        | some (out, _) => Program.returned
            (some (out, patchedCache state hall cycle visited frames gap out old equalizer frontier)))
      (Executes.returned _ (prior ++ trace))
  · exact ComponentPhysical.bundle_cache_correct _ hnd G updated hsub (measureProfile cost) hv
  · exact ComponentPhysical.bundle_disjoint _ hnd G updated hsub
  · exact ComponentPhysical.bundle_envy_free _ hnewvalid hnd G updated hsub cost hcost

end EnvyFreeResearch.Full.Chores.ComponentBatch
