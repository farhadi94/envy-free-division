import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryPrepared
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryPreprocessing
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryProgram

/-! Endpoints and scoped queries through the full continuing preprocessing
branch, including the fixed clearance allocation and all rejected outer roots. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Completion Boundary Parameters
variable {n : ℕ} [NeZero n]

theorem continue_prepared_known (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : EntranceChoice n out.originals.length)
    (hs : (Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n), CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hknown : PreprocessingKnown points out)
    (hdata : DataKnown points out.originals.get (a.data out.originals.get))
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (hex : Executes oracle (continuePrepared c children out a) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  obtain ⟨mid,first,rest,hfirst,hrest,rfl⟩ := Executes.split_bind _ _ hex
  obtain ⟨entry,tr,he,hinv,_⟩ := prepared_driver_executes cost hn oracle hpolicy U c out a hs prior
  obtain ⟨rfl,rfl⟩ := hfirst.deterministic he
  obtain ⟨hentry,hpriv,hscope⟩ := driver_known cost.measure out.originals id c
    (fun s => hs.2.1.member_sound _ (List.get_mem _ s)) a.pivot (cachedValue out.residue) (scale n)
    (exponent n) (a.data out.originals.get) (fun _ _ => []) oracle hpolicy points hdata
    (fun _ _ => by simp [CacheKnown]) hzero hone prior first entry he
  obtain ⟨inner,second,empty,hsecond,hreturn,htrace⟩ := Executes.split_bind _ _ hrest
  cases hreturn
  simp only [List.append_nil] at htrace
  subst rest
  obtain ⟨hinner,hscope₂⟩ := prepared_finish_known cost hn U c out a hs entry hinv children hchildren
    (Known points first) hentry hpriv (hknown.residue.mono (by intro x hx; exact Or.inl hx))
    (Or.inl hzero) (Or.inl hone) oracle hpolicy (prior++first) second inner hsecond
  refine ⟨?_,(scoped_append points first second).mpr ⟨hscope,hscope₂⟩⟩
  apply join_known
  · exact (batch_allocation_known points out.clearance hknown.clearance).mono
      (by intro x hx; exact Or.inl hx)
  · simpa only [known_append] using hinner
end EnvyFreeResearch.Full.Chores.Outer
