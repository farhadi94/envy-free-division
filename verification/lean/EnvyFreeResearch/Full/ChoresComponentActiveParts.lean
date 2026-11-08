import EnvyFreeResearch.Full.ChoresComponentActiveCache
import EnvyFreeResearch.Full.ChoresCompletionAllocation

/-! Active-agent output pieces with all ambient original-observer values. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ActiveCore
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical
variable {n k : ℕ}

def allocationCache (cache : List (Parent n)) : IntervalCore.Outcome k → Fin k → List (Parent n)
  | .zero z, i => if i = z then cache else []
  | .prefixes parent s, i => window (parent (s.matching i)).left (s.endpoint (s.matching i)).point cache

def residueCache (cache : List (Parent n)) : IntervalCore.Outcome k → List (Parent n)
  | .zero _ => []
  | .prefixes parent s => selectWindows
      (List.ofFn (fun p => ((s.endpoint p).point,(parent p).right))) cache

theorem allocation_cache_correct (P : Profile (Fin n)) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid P U cache) (c : Fin k) (out : IntervalCore.Outcome k)
    (halign : AlignedOutcome cache out) (i : Fin k) :
    CacheValid P (domainAllocation U c out i) (allocationCache cache out i) := by
  have hU : U ⊆ Icc 0 1 := fun x hx =>
    ⟨le_of_lt ((cache_domain_subset _ _ _ hc hx).1),(cache_domain_subset _ _ _ hc hx).2⟩
  have hzero : 0 ∉ U := fun h => lt_irrefl 0 ((cache_domain_subset _ _ _ hc h).1)
  cases out with
  | zero z =>
    by_cases hi : i = z
    · simpa only [allocationCache,domainAllocation,IntervalCore.outputAllocation,
        ite_eq_left hi,inter_eq_right.mpr hU] using hc
    · simpa only [allocationCache,domainAllocation,IntervalCore.outputAllocation,
        ite_eq_right hi,empty_inter] using empty_cache_valid P
  | prefixes parent s =>
    rw [domain_prefix_allocation U hzero c parent s i]
    refine ⟨window_valid P hc.1,window_ordered hc.2.1,?_⟩
    change material (window _ _ cache) = _
    rw [window_material (halign (s.matching i)).1 (halign (s.matching i)).2.1,hc.2.2]

theorem residue_cache_correct (P : Profile (Fin n)) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid P U cache) (out : IntervalCore.Outcome k) (halign : AlignedOutcome cache out) :
    CacheValid P (domainResidue U out) (residueCache cache out) := by
  cases out with
  | zero z =>
    simpa only [residueCache,domainResidue,IntervalCore.outputResidue,empty_inter] using empty_cache_valid P
  | prefixes parent s =>
    have hparts : rangeMaterial (List.ofFn (fun p => ((s.endpoint p).point,(parent p).right))) =
        IntervalCore.residue parent s := by
      ext x
      simp only [rangeMaterial,mem_ofPred_eq,List.mem_ofFn,IntervalCore.residue,
        IntervalCore.suffixPiece,mem_iUnion]
      constructor
      · rintro ⟨r,⟨p,rfl⟩,hp⟩
        exact ⟨p,hp⟩
      · rintro ⟨p,hp⟩
        exact ⟨_,⟨p,rfl⟩,hp⟩
    have hbound : ∀ r ∈ List.ofFn (fun p => ((s.endpoint p).point,(parent p).right)),
        Aligned cache r.1 ∧ Aligned cache r.2 := by
      intro r hr
      obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hr
      exact (halign p).2
    have hs := selected_cache P U cache hc _ hbound
    simpa only [hparts,domainResidue,residueCache,IntervalCore.outputResidue,inter_comm] using hs

/-- Every observer's cached share and residue values equal the original
physical measures of the returned sets. These are exact cache sums, without
additional Eval calls and without passing to equivalence modulo null sets. -/
theorem core_cache_values (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin k) (out : IntervalCore.Outcome k) (halign : AlignedOutcome cache out) :
    (∀ (i : Fin n) (j : Fin k), cachedValue (allocationCache cache out j) i = (cost i).real (domainAllocation U c out j)) ∧
    (∀ i : Fin n, cachedValue (residueCache cache out) i = (cost i).real (domainResidue U out)) := by
  constructor
  · intro i j
    have hs := allocation_cache_correct _ U cache hc c out halign j
    rw [← hs.2.2,material_value cost _ hs.1 hs.2.1]
  · intro i
    have hs := residue_cache_correct _ U cache hc out halign
    rw [← hs.2.2,material_value cost _ hs.1 hs.2.1]


end EnvyFreeResearch.Full.Chores.ActiveCore
