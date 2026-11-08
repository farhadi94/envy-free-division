import EnvyFreeResearch.Full.ChoresComponentClosed

/-! Actual original-oracle execution of a closed affine compensation group. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentClosed
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCore SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle OrderedUnion
open QueryProgram OracleProtocol
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (participants : Finset (Fin n)) (label : Fin n)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ)
  (hmany : Fintype.card participants < Fintype.card Root)

def program (cache : Masked.Cache Root n) :
    Program (Query (Fin n)) ℝ
      (Option (Result (Root := Root) participants × Package (Fin n) RootId)) :=
  (ComponentRecording.affineProgram Subtype.val (offsets gap state.partition.representative)
    cache hmany.le).bind (fun result => match result with
      | none => .returned none
      | some out => .returned
          (some (out, outputPackage state visited participants label packages frames gap out hmany)))

variable (hlabel : ∀ j ∈ participants, state.partition.representative j = label)
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ)
  (cache : Masked.Cache Root n)
  (hc : Masked.CacheCorrect (measureProfile cost) (domains blocks state.partition.representative) cache)
  (hgap : ∀ s p i, 0 ≤ gap s p i)
  (hpositive : participants.Nonempty)
  (hwhole : ∀ s i, i ∈ participants → 0 ≤ (cost i).real (blocks s label) - gap s label i)
  (hlive : ∀ s, (packages s).live = some (frames s))
  (hvalid : ∀ s, (packages s).Valid)
  (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
  (hprotect : ∀ i ∉ participants, ∀ s, (cost i).real (blocks s label) ≤ gap s label i)

include hlabel hc hgap hpositive hwhole hlive hvalid hallowed hprotect

theorem program_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Result (Root := Root) participants, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (program state visited participants label packages frames gap hmany cache) prior
        (some (out, outputPackage state visited participants label packages frames gap out hmany)) trace ∧
      (outputPackage state visited participants label packages frames gap out hmany).Valid ∧
      (outputPackage state visited participants label packages frames gap out hmany).live = none ∧
      PhysicalCorrect
        (affineUtility cost (domains blocks state.partition.representative)
          (offsets gap state.partition.representative)) Subtype.val out.allocation ∧
      PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card participants) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card participants) ∧
      Masked.CacheCorrect (measureProfile cost) (domains blocks state.partition.representative) out.cache ∧
      ∃ j : participants, material (out.parts j).suffixParts = blocks (out.allocation.assigned j) label := by
  have hpos : 0 < Fintype.card participants := by simpa using Finset.card_pos.mpr hpositive
  obtain ⟨out, trace, hexec, hcorrect, hparts, hlen, hcuts, hcache⟩ :=
    ComponentRecording.affine_correct cost (domains blocks state.partition.representative) cache hc
      Subtype.val (offsets gap state.partition.representative) (fun s i => hgap s _ i)
      hpos hmany oracle hpolicy prior (fun s i => by
        simpa only [ComponentPayments.domains, offsets, hlabel i i.property] using hwhole s i i.property)
  refine ⟨out, trace, ?_, ?_, rfl, hcorrect, hparts, hlen, hcuts, hcache, ?_⟩
  · simpa only [program, List.append_nil] using hexec.bind
      (fun result => match result with
        | none => Program.returned none
        | some out => Program.returned
            (some (out, outputPackage state visited participants label packages frames gap out hmany)))
      (Executes.returned _ (prior ++ trace))
  · exact output_valid state visited participants label packages frames gap out hlabel cost
      blocks hparts hcorrect hmany hlive hvalid hallowed hprotect
  · obtain ⟨j, hj, _⟩ := whole_suffix_retained state visited participants label frames gap out
      hlabel cost blocks hparts hcorrect hcache
    exact ⟨j, hj⟩

end EnvyFreeResearch.Full.Chores.ComponentClosed
