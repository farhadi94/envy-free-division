import EnvyFreeResearch.Full.ChoresOuterPreprocessingGeometry

/-! The actual preprocessing program returns either a complete zero-residue
allocation or a protected entrance, retaining the fixed clearance allocation. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion Snapshot Completion QueryProgram
open scoped Classical
variable {n : ℕ}

inductive Prepared (n : ℕ) where
  | complete (allocation : Completion.Allocation n (Fin n))
  | continuing (out : Preprocessing.Output n) (choice : EntranceChoice n out.originals.length)
  | failed

def prepareFinish (c : Fin n) (H : ℝ) (S : ℕ) (out : Preprocessing.Output n) : Prepared n :=
  if hz : ∃ z : Fin n, cachedValue out.residue z=0 then
    .complete ((batchAllocation (out.originals++out.clearance)).join (zeroAllocation hz.choose out.residue))
  else match entranceChoice out.originals.get c (cachedValue out.residue) H S with
    | none => .failed
    | some a => .continuing out a

def prepareProgram (c : Fin n) (J : ℕ) (H : ℝ) (L S : ℕ) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (Prepared n) :=
  (Preprocessing.program c J H L cache).bind (fun out => .returned (prepareFinish c H S out))

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

def Prepared.Sound (U : Set ℝ) (c : Fin n) (H : ℝ) (J S : ℕ) : Prepared n → Prop
  | .complete allocation => allocation.Sound cost id U
  | .failed => False
  | .continuing out a =>
      out.originals.length=J ∧ Chain cost c U out.originals out.middle ∧
      AnyChain cost (material out.middle) out.clearance out.residue ∧
      Clearance.Separated (Clearance.entries out.originals) cost H (material out.residue) ∧
      (∀ i, 0 < (cost i).real (material out.residue)) ∧
      a.Admissible out.originals.get c (fun i => (cost i).real (material out.residue)) H S ∧
      (a.data out.originals.get).Good out.originals.get cost
        (fun i => (cost i).real (material out.residue)) H

theorem prepare_finish_sound (hn : 2 ≤ n) (U : Set ℝ) (c : Fin n) (H : ℝ)
    (hH : (n-1 : ℕ) < H) (J S : ℕ) (hcount : (S-1)*(n-1)<J)
    (out : Preprocessing.Output n) (hJ : out.originals.length=J)
    (horiginal : Chain cost c U out.originals out.middle)
    (hclear : AnyChain cost (material out.middle) out.clearance out.residue)
    (hsep : Clearance.Separated (Clearance.entries out.originals) cost H (material out.residue)) :
    (prepareFinish c H S out).Sound cost U c H J S := by
  have hc (i : Fin n) : cachedValue out.residue i=(cost i).real (material out.residue) :=
    Clearance.cached_total cost _ _ hclear.final_cache i
  have hcf : cachedValue out.residue=(fun i => (cost i).real (material out.residue)) := funext hc
  by_cases hz : ∃ z : Fin n, cachedValue out.residue z=0
  · rw [prepareFinish,dif_pos hz]
    apply preprocessing_zero_sound cost out horiginal hclear hz.choose
    rw [← hc]
    exact hz.choose_spec
  · have hpos (i : Fin n) : 0 < (cost i).real (material out.residue) := by
      have hne : (cost i).real (material out.residue) ≠ 0 := fun hh => hz ⟨i,(hc i).trans hh⟩
      exact lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    obtain ⟨a,ha,had⟩ := entrance_selection cost c out.originals out.middle horiginal hn
      hclear.subsets.2 (hpos c) H hH S (by rw [hJ]; exact hcount)
    rw [prepareFinish,dif_neg hz,hcf,ha]
    refine ⟨hJ,horiginal,hclear,hsep,hpos,had,?_⟩
    exact entrance_good cost c out.originals out.middle horiginal a H
      (lt_of_le_of_lt (Nat.cast_nonneg _) hH)

theorem prepare_program_correct (hn : 2 ≤ n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (J : ℕ) (H : ℝ) (hH : (n-1 : ℕ) < H) (L S : ℕ)
    (hscale : H*contraction n^L ≤ 1/H) (hcount : (S-1)*(n-1)<J)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (prepareProgram c J H L S cache) prior out trace ∧
      trace.length ≤ (J+J*(n^2+n^3)*L)*queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ (J+J*(n^2+n^3)*L)*cutBudget n ∧
      out.Sound cost U c H J S := by
  obtain ⟨out,trace,he,hJ,hnum,hQ,hC,horiginal,hclear,hsep⟩ :=
    Preprocessing.program_correct hn cost oracle hpolicy c J H
      (lt_of_le_of_lt (Nat.cast_nonneg _) hH) L hscale U cache hc prior
  refine ⟨prepareFinish c H S out,trace,?_,hQ,hC,?_⟩
  · simpa only [prepareProgram,List.append_nil] using he.bind
      (fun out => Program.returned (prepareFinish c H S out))
      (Executes.returned _ (prior++trace))
  · exact prepare_finish_sound cost hn U c H hH J S hcount out hJ horiginal hclear hsep
end EnvyFreeResearch.Full.Chores.Outer
