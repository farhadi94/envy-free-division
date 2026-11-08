import EnvyFreeResearch.Full.ChoresTrackedTable

/-! Original snapshots and clearance are composed into one ordinary-query
program. All tracked entries refer to the first, immutable batch. The
returned cache is the actual final residue and every clearance allocation
is retained in the physical accounting. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Preprocessing
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Snapshot
open scoped Classical

structure Output (n : ℕ) where
  originals : List (Snapshot.Output n)
  clearance : List (Snapshot.Output n)
  middle : List (Parent n)
  residue : List (Parent n)

def program {n : ℕ} (c : Fin n) (J : ℕ) (H : ℝ) (L : ℕ) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (Output n) :=
  (generate c J cache).bind (fun original =>
    (Clearance.allProgram original.snapshots H L original.residue).bind (fun cleared =>
      .returned ⟨original.snapshots,cleared.snapshots,original.residue,cleared.residue⟩))

theorem program_correct {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (J : ℕ) (H : ℝ) (hH : 0 < H) (L : ℕ)
    (hscale : H*contraction n^L ≤ 1/H)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (program c J H L cache) prior out trace ∧
      out.originals.length = J ∧ out.clearance.length ≤ J*(n^2+n^3)*L ∧
      trace.length ≤ (J+J*(n^2+n^3)*L)*queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ (J+J*(n^2+n^3)*L)*cutBudget n ∧
      Chain cost c U out.originals out.middle ∧
      AnyChain cost (material out.middle) out.clearance out.residue ∧
      Clearance.Separated (Clearance.entries out.originals) cost H (material out.residue) := by
  obtain ⟨first,t₁,hexec₁,hJ,hQ₁,hC₁,hchain₁⟩ := generate_correct hn cost oracle hpolicy U cache hc c J prior
  obtain ⟨second,t₂,hexec₂,hcount₂,hQ₂,hC₂,hchain₂,hsep⟩ :=
    Clearance.all_program_correct hn oracle hpolicy first.snapshots H hH L hscale
      (material first.residue) first.residue hchain₁.final_cache (prior++t₁)
  rw [hJ] at hcount₂ hQ₂ hC₂
  refine ⟨⟨first.snapshots,second.snapshots,first.residue,second.residue⟩,t₁++t₂,?_,
    hJ,hcount₂,?_,?_,hchain₁,hchain₂,hsep⟩
  · have hsecond := hexec₂.bind (fun second => Program.returned
      (⟨first.snapshots,second.snapshots,first.residue,second.residue⟩ : Output n))
      (Executes.returned _ ((prior++t₁)++t₂))
    exact hexec₁.bind (fun first => (Clearance.allProgram first.snapshots H L first.residue).bind
      (fun second => Program.returned
        (⟨first.snapshots,second.snapshots,first.residue,second.residue⟩ : Output n)))
      (by simpa only [List.append_nil] using hsecond)
  · simp only [List.length_append]
    simpa only [add_mul] using Nat.add_le_add hQ₁ hQ₂
  · simp only [List.countP_append]
    simpa only [add_mul] using Nat.add_le_add hC₁ hC₂

end EnvyFreeResearch.Full.Chores.Preprocessing
