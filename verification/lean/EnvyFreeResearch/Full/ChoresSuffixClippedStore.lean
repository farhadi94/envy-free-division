import EnvyFreeResearch.Full.ChoresSuffixLookup

/-! The clipped suffix table uses the proved concrete insertion operation.
It preserves the unclipped values as well as the public formal records. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix
open Set OracleProtocol IntervalOracle QueryProgram Persistent

variable {n : ℕ}

def clippedEnsureProgram (records : List (ClippedRecord n)) (i : Fin n) (target : ℝ × ℚ) :
    Program (Query (Fin n)) ℝ (Lookup.Result (ClippedRecord n)) :=
  Lookup.ensureProgram ClippedRecord.record clippedInsertProgram records i target

/-- Exact record reuse or one immutable physical insertion, with no
assumed insertion interface remaining in this concrete theorem. -/
theorem clipped_ensure_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (offset : Fin n → ℝ) (first : ClippedRecord n) (rest : List (ClippedRecord n))
    (i : Fin n) (target : ℝ × ℚ)
    (horder : List.Pairwise (fun r s => Before r.record s.record) (first::rest))
    (hsound : ∀ r ∈ first::rest, ClippedSound P offset r)
    (hbound : ∀ r ∈ first::rest, r.record.point ∈ Icc (0 : ℝ) 1)
    (hlower : recordLT (first.record.formal i) target ∨ first.record.formal i = target)
    (hupper : ∃ last ∈ first::rest, recordLT target (last.record.formal i) ∨ last.record.formal i = target)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : Lookup.Result (ClippedRecord n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (clippedEnsureProgram (first::rest) i target) prior result trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      List.Pairwise (fun r s => Before r.record s.record) result.records ∧
      (∀ r ∈ result.records, ClippedSound P offset r ∧ r.record.point ∈ Icc (0 : ℝ) 1) ∧
      (first::rest).Sublist result.records ∧ result.records.length ≤ (first::rest).length+1 ∧
      result.records.head? = (first::rest).head? ∧ result.records.getLast? = (first::rest).getLast? ∧
      result.selected ∈ result.records ∧ result.selected.record.formal i = target :=
  Lookup.ensure_correct ClippedRecord.record clippedInsertProgram (ClippedSound P offset) oracle
    (fun left right i target => clipped_insert_correct P hmono oracle hpolicy offset left right i target)
    first rest i target horder hsound hbound hlower hupper prior

end EnvyFreeResearch.Full.Chores.Suffix
