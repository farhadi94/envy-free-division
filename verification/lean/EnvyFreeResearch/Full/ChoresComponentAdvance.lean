import EnvyFreeResearch.Full.ChoresComponentPaymentCertificate
import EnvyFreeResearch.Full.ChoresComponentFrontierValues

/-!
# An actual paid component-cycle group operation

The ordinary oracle program executes masked clipped SubCore, records all final
retained pieces, builds the concrete donor modifications, and updates the live
survivor's frame.  Its package reserve invariant is proved from the actual
recorded comparisons and local frontier facts, not assumed as an interface.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentBatch
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical SubCore ChoreComposition IntervalOracle QueryProgram
open OracleProtocol
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ)
  (hmany : Fintype.card (Task state hall cycle) < Fintype.card Root)

def outputPackage (out : Result state hall cycle) : Package (Fin n) RootId :=
  let survivor := ComponentAssignment.unused out.allocation hmany
  mergeOpen (packages survivor) (donations state hall cycle visited packages frames gap out)
    (ComponentFrames.advance state hall cycle visited frames survivor)

def program (cache : Masked.Cache Root n) :
    Program (Query (Fin n)) ℝ (Option (Result state hall cycle × Package (Fin n) RootId)) :=
  (ComponentRecording.clippedProgram Subtype.val (offsets gap state.partition.representative)
    cache hmany.le).bind (fun result => match result with
      | none => .returned none
      | some out => .returned (some (out, outputPackage state hall cycle visited packages frames gap hmany out)))

theorem task_positive : 0 < Fintype.card (Task state hall cycle) := by
  have hs : (state.selected hall cycle).Nonempty :=
    Finset.card_pos.mp (by have := state.selected_two hall cycle; omega)
  have ht := state.partition.tasks_nonempty (state.selected hall cycle)
    (state.selected_subset hall cycle) hs
  simpa only [Fintype.card_coe] using Finset.card_pos.mpr ht

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ)
  (cache : Masked.Cache Root n)
  (hc : Masked.CacheCorrect (measureProfile cost) (domains blocks state.partition.representative) cache)
  (hgap : ∀ s p i, 0 ≤ gap s p i)
  (hlive : ∀ s, (packages s).live = some (frames s))
  (hvalid : ∀ s, (packages s).Valid)
  (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
  (hequalized : ∀ s p i, (frames s).equalizerCost i p i = (frames s).baseline i)
  (hforbidden : ∀ s p, p ∈ state.selected hall cycle →
    (frames s).forbidden p ⊆ state.partition.component p)
  (hfrontier : ∀ s p, p ∈ state.selected hall cycle → ∀ i,
    (frames s).gap i (ComponentFrames.nextAgent state s p) p =
      (cost i).real (blocks s p) - gap s p i)
  (hprotect : ∀ p ∈ state.selected hall cycle, ∀ s i,
    i ∉ state.partition.component p → (cost i).real (blocks s p) ≤ gap s p i)
  (hcontain : ∀ s p, p ∈ state.selected hall cycle → ∀ i j, j ∈ (frames s).allowed p →
    (frames s).gap i j p ≤ (frames s).gap i (ComponentFrames.nextAgent state s p) p)

include hlive hvalid hallowed hequalized hforbidden hfrontier hprotect hcontain

theorem output_valid (out : Result state hall cycle)
    (hparts : PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out)
    (hcorrect : PhysicalCorrect
      (clippedUtility cost (domains blocks state.partition.representative)
        (offsets gap state.partition.representative)) Subtype.val out.allocation)
    (hcache : Masked.CacheCorrect (measureProfile cost)
      (domains blocks state.partition.representative) out.cache) :
    (outputPackage state hall cycle visited packages frames gap hmany out).Valid := by
  let survivor := ComponentAssignment.unused out.allocation hmany
  have hframes : ∀ s, (frames s).Good := fun s => (hvalid s).live_good _ (hlive s)
  have hd := donations_wellFormed state hall cycle visited packages frames gap out hlive hframes hallowed
  have hv := donations_packages_valid state hall cycle visited packages frames gap out hvalid
  have hn := ComponentFrames.advance_good state hall cycle visited frames survivor
    (hallowed survivor) (hequalized survivor)
  have hpay := exclusive_payment state hall cycle visited packages frames gap out cost blocks
    hparts hcorrect hcache survivor (ComponentAssignment.unused_spec out.allocation hmany)
    (hlive survivor) (hallowed survivor) (hforbidden survivor) (hfrontier survivor)
    hprotect (hcontain survivor)
  exact merge_open_valid (packages survivor) (hvalid survivor) _ hd hv _ hn hpay

include hc hgap

/-- All physical calls use the original oracle at the actual prior history. -/
theorem program_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Result state hall cycle, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (program state hall cycle visited packages frames gap hmany cache) prior
        (some (out, outputPackage state hall cycle visited packages frames gap hmany out)) trace ∧
      (outputPackage state hall cycle visited packages frames gap hmany out).Valid ∧
      PhysicalCorrect
        (clippedUtility cost (domains blocks state.partition.representative)
          (offsets gap state.partition.representative)) Subtype.val out.allocation ∧
      PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card (Task state hall cycle)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card (Task state hall cycle)) ∧
      Masked.CacheCorrect (measureProfile cost) (domains blocks state.partition.representative) out.cache := by
  obtain ⟨out, trace, hexec, hcorrect, hparts, hlen, hcuts, hcache⟩ :=
    ComponentRecording.clipped_correct cost (domains blocks state.partition.representative) cache hc
      Subtype.val (offsets gap state.partition.representative) (fun s i => hgap s _ i)
      (task_positive state hall cycle) hmany oracle hpolicy prior
  refine ⟨out, trace, ?_, ?_, hcorrect, hparts, hlen, hcuts, hcache⟩
  · simpa only [program, List.append_nil] using hexec.bind
      (fun result => match result with
        | none => Program.returned none
        | some out => Program.returned
            (some (out, outputPackage state hall cycle visited packages frames gap hmany out)))
      (Executes.returned _ (prior ++ trace))
  · exact output_valid state hall cycle visited packages frames gap hmany cost blocks
      hlive hvalid hallowed hequalized hforbidden hfrontier hprotect hcontain out hparts hcorrect hcache

end EnvyFreeResearch.Full.Chores.ComponentBatch
