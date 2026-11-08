import EnvyFreeResearch.Full.ChoresUnionCoreCache

/-! Actual cached component lists for every returned Core share and for its
residue. Filtering preserves physical order and the original all-observer
values; the component extraction itself makes no oracle calls. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram
open scoped Classical

variable {n : ℕ}

def rangeMaterial (ranges : List (ℝ × ℝ)) : Set ℝ :=
  {x | ∃ r ∈ ranges, x ∈ Ioc r.1 r.2}

def selectWindows (ranges : List (ℝ × ℝ)) (cache : List (Parent n)) : List (Parent n) :=
  cache.filter (fun p => decide (∃ r ∈ ranges, r.1 ≤ p.left ∧ p.right ≤ r.2))

theorem selected_material (ranges : List (ℝ × ℝ)) (cache : List (Parent n))
    (halign : ∀ r ∈ ranges, Aligned cache r.1 ∧ Aligned cache r.2) :
    material (selectWindows ranges cache) = material cache ∩ rangeMaterial ranges := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hx
    have hp' : p ∈ cache ∧ ∃ r ∈ ranges, r.1 ≤ p.left ∧ p.right ≤ r.2 := by
      simpa only [selectWindows,List.mem_filter,decide_eq_true_eq] using hp
    obtain ⟨r,hr,hl,hu⟩ := hp'.2
    exact ⟨(mem_material_iff _ _).mpr ⟨p,hp'.1,hpx⟩,
      r,hr,hl.trans_lt hpx.1,hpx.2.trans hu⟩
  · rintro ⟨hx,r,hr,hrx⟩
    have hw : x ∈ material (window r.1 r.2 cache) := by
      rw [window_material (halign r hr).1 (halign r hr).2]
      exact ⟨hx,hrx⟩
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hw
    obtain ⟨hp,hl,hu⟩ := mem_window.mp hp
    apply (mem_material_iff _ _).mpr
    refine ⟨p,?_,hpx⟩
    simpa only [selectWindows,List.mem_filter,decide_eq_true_eq] using
      And.intro hp ⟨r,hr,hl,hu⟩

theorem selected_cache (P : Profile (Fin n)) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid P U cache) (ranges : List (ℝ × ℝ))
    (halign : ∀ r ∈ ranges, Aligned cache r.1 ∧ Aligned cache r.2) :
    CacheValid P (U ∩ rangeMaterial ranges) (selectWindows ranges cache) := by
  refine ⟨valid_filter P hc.1 _,hc.2.1.filter _,?_⟩
  rw [selected_material ranges cache halign,hc.2.2]

def allocationCache (cache : List (Parent n)) : IntervalCore.Outcome n → Fin n → List (Parent n)
  | .zero z, i => if i = z then cache else []
  | .prefixes parent s, i => window (parent (s.matching i)).left (s.endpoint (s.matching i)).point cache

def residueCache (cache : List (Parent n)) : IntervalCore.Outcome n → List (Parent n)
  | .zero _ => []
  | .prefixes parent s => selectWindows
      (List.ofFn (fun p => ((s.endpoint p).point,(parent p).right))) cache

theorem empty_cache_valid (P : Profile (Fin n)) : CacheValid P ∅ ([] : List (Parent n)) :=
  ⟨trivial,by simp [Ordered],rfl⟩

theorem domain_prefix_allocation (U : Set ℝ) (hzero : 0 ∉ U) (c : Fin n)
    (parent : Fin n → Parent n) (s : PhysicalCore.State n n) (i : Fin n) :
    domainAllocation U c (.prefixes parent s) i =
      U ∩ Ioc (parent (s.matching i)).left (s.endpoint (s.matching i)).point := by
  change (Ioc _ _ ∪ if i = c then {0} else ∅) ∩ U = _
  by_cases hi : i = c
  · rw [ite_eq_left hi,union_inter_distrib_right,singleton_inter_of_notMem hzero,union_empty]
    exact inter_comm _ _
  · simp only [ite_eq_right hi,union_empty,inter_comm]

theorem allocation_cache_correct (P : Profile (Fin n)) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid P U cache) (c : Fin n) (out : IntervalCore.Outcome n)
    (halign : CoreAligned cache out) (i : Fin n) :
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
    (hc : CacheValid P U cache) (out : IntervalCore.Outcome n) (halign : CoreAligned cache out) :
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
    (c : Fin n) (out : IntervalCore.Outcome n) (halign : CoreAligned cache out) :
    (∀ i j, cachedValue (allocationCache cache out j) i = (cost i).real (domainAllocation U c out j)) ∧
    (∀ i, cachedValue (residueCache cache out) i = (cost i).real (domainResidue U out)) := by
  constructor
  · intro i j
    have hs := allocation_cache_correct _ U cache hc c out halign j
    rw [← hs.2.2,material_value cost _ hs.1 hs.2.1]
  · intro i
    have hs := residue_cache_correct _ U cache hc out halign
    rw [← hs.2.2,material_value cost _ hs.1 hs.2.1]

/-- Physical Core with reusable, correctly valued component lists for every
returned share and for the residual domain. All of the caches are computed
from the actual returned records, not additional oracle interfaces. -/
theorem recorded_core_correct (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : IntervalCore.Outcome n, ∃ fresh : List (Parent n),
    ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (cachedDomainCoreProgram c cache) prior (out,fresh) trace ∧
      trace.length ≤ cachedDomainCoreBudget n ∧
      virtualCuts trace ≤ n-1+IntervalCore.trimBudget n ∧
      DomainCorrect cost U c out ∧
      (∀ i, CacheValid (measureProfile cost) (domainAllocation U c out i) (allocationCache fresh out i)) ∧
      CacheValid (measureProfile cost) (domainResidue U out) (residueCache fresh out) := by
  obtain ⟨out,fresh,trace,hexec,hlen,hcuts,hcorrect,hcached,hfresh,halign⟩ :=
    cached_domain_core_correct hn cost oracle hpolicy U cache hc c prior
  exact ⟨out,fresh,trace,hexec,hlen,hcuts,hcorrect,
    allocation_cache_correct _ U fresh hfresh c out halign,
    residue_cache_correct _ U fresh hfresh out halign⟩

end EnvyFreeResearch.Full.Chores.OrderedUnion
