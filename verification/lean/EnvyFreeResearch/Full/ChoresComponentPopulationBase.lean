import EnvyFreeResearch.Full.ChoresComponentPopulationProgram

/-! Complete native-population base programs on arbitrary recorded finite
unions. One agent needs no query; two agents use one union half-cut with
all-observer recording, then choose from the actual cached replies. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

def singletonProgram (cache : List (Parent 1)) : Program (Query (Fin 1)) ℝ (Allocation 1 (Fin 1)) :=
  .returned (ActiveCore.singletonAllocation cache)

theorem singleton_specification (cost : Costs 1) : Specification cost id singletonProgram 0 0 := by
  intro cache hc oracle hpolicy prior
  refine ⟨ActiveCore.singletonAllocation cache, [], Executes.returned _ _, le_rfl, le_rfl,
    ActiveCore.singleton_sound cost.measure id (material cache) cache hc, trivial, ?_⟩
  intro i
  simpa only [ActiveCore.singletonAllocation, Boundary.known_nil] using
    Boundary.inherited_cache_known (measureProfile cost.measure) cache hc.1 hc.2.1

def pairAllocation (first second : List (Parent 2)) : Allocation 2 (Fin 2) :=
  ⟨fun i => if i = 0 then first else second⟩

theorem pair_sound (cost : Costs 2) (U : Set ℝ) (first second : List (Parent 2))
    (hf : CacheValid (measureProfile cost.measure) (material first) first)
    (hs : CacheValid (measureProfile cost.measure) (material second) second)
    (hd : Disjoint (material first) (material second)) (hcover : material first ∪ material second = U)
    (h0 : (cost.measure 0).real (material first) ≤ (cost.measure 0).real (material second))
    (h1 : (cost.measure 1).real (material second) ≤ (cost.measure 1).real (material first)) :
    (pairAllocation first second).Sound cost.measure id U := by
  constructor
  · intro i
    fin_cases i
    · simpa [pairAllocation] using hf
    · simpa [pairAllocation] using hs
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [pairAllocation] using hd
    · simpa [pairAllocation] using hd.symm
    · exact (hij rfl).elim
  · rw [← hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl (by simpa [pairAllocation] using hi)
      · exact Or.inr (by simpa [pairAllocation] using hi)
    · intro hx
      rcases hx with hx | hx
      · exact mem_iUnion.mpr ⟨0, by simpa [pairAllocation] using hx⟩
      · exact mem_iUnion.mpr ⟨1, by simpa [pairAllocation] using hx⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact le_rfl
    · simpa [pairAllocation] using h0
    · simpa [pairAllocation] using h1
    · exact le_rfl

def chooseTwo (out : Split 2) : Allocation 2 (Fin 2) :=
  if cachedValue out.prefixParts 1 ≤ cachedValue out.suffixParts 1 then
    pairAllocation out.suffixParts out.prefixParts
  else pairAllocation out.prefixParts out.suffixParts

def twoProgram (cache : List (Parent 2)) : Program (Query (Fin 2)) ℝ (Allocation 2 (Fin 2)) :=
  (splitProgram (0 : Fin 2) (cachedValue cache 0 / 2) cache).bind
    (fun out => .returned (chooseTwo out))

theorem two_specification (cost : Costs 2) : Specification cost id twoProgram 2 1 := by
  intro cache hc oracle hpolicy prior
  have hmono : ∀ i, Monotone ((measureProfile cost.measure).cumulative i) :=
    fun i => prefixCost_monotone (cost.measure i) 0
  have hnonneg : 0 ≤ cachedValue cache (0 : Fin 2) :=
    cachedValue_nonnegative (measureProfile cost.measure) hmono hc.1 0
  obtain ⟨parts, trace, hexec, hQ, hC, hcover, hd, horder, hpre, hsuf, hhalf, hadd⟩ :=
    split_program_physical (measureProfile cost.measure) hmono oracle hpolicy (0 : Fin 2) cache hc.1 hc.2.1
      (cachedValue cache 0 / 2) (by positivity) (by linarith) prior
  have hpord := (List.pairwise_append.mp horder).1
  have hsord := (List.pairwise_append.mp horder).2.1
  have hpreCache : CacheValid (measureProfile cost.measure) (material parts.prefixParts) parts.prefixParts :=
    ⟨hpre, hpord, rfl⟩
  have hsufCache : CacheValid (measureProfile cost.measure) (material parts.suffixParts) parts.suffixParts :=
    ⟨hsuf, hsord, rfl⟩
  have hvaluePre (i : Fin 2) : cachedValue parts.prefixParts i = (cost.measure i).real (material parts.prefixParts) :=
    (material_value cost.measure _ hpre hpord i).symm
  have hvalueSuf (i : Fin 2) : cachedValue parts.suffixParts i = (cost.measure i).real (material parts.suffixParts) :=
    (material_value cost.measure _ hsuf hsord i).symm
  have hsame : (cost.measure 0).real (material parts.prefixParts) =
      (cost.measure 0).real (material parts.suffixParts) := by
    have htotal := hadd (0 : Fin 2)
    rw [hvaluePre, hvalueSuf] at htotal
    rw [hvaluePre] at hhalf
    linarith
  have hsound : (chooseTwo parts).Sound cost.measure id (material cache) := by
    by_cases hchoose : cachedValue parts.prefixParts 1 ≤ cachedValue parts.suffixParts 1
    · rw [chooseTwo, ite_eq_left hchoose]
      exact pair_sound cost (material cache) _ _ hsufCache hpreCache hd.symm
        (by simpa only [union_comm] using hcover) hsame.ge
        (by simpa only [hvaluePre, hvalueSuf] using hchoose)
    · rw [chooseTwo, ite_eq_right hchoose]
      exact pair_sound cost (material cache) _ _ hpreCache hsufCache hd hcover hsame.le
        (by simpa only [hvaluePre, hvalueSuf] using (le_of_not_ge hchoose))
  obtain ⟨hknown, hscope⟩ := Boundary.split_known oracle {x | Aligned cache x} (0 : Fin 2)
    (cachedValue cache 0 / 2) cache (Boundary.inherited_cache_known _ cache hc.1 hc.2.1)
    prior parts trace hexec
  refine ⟨chooseTwo parts, trace, ?_, hQ, hC, hsound, hscope, ?_⟩
  · simpa only [twoProgram, List.append_nil] using hexec.bind
      (fun out => Program.returned (chooseTwo out)) (Executes.returned _ _)
  · intro i p hp
    have hpreKnown : Boundary.CacheKnown (Boundary.Known {x | Aligned cache x} trace) parts.prefixParts :=
      fun p hp => hknown p (List.mem_append_left _ hp)
    have hsufKnown : Boundary.CacheKnown (Boundary.Known {x | Aligned cache x} trace) parts.suffixParts :=
      fun p hp => hknown p (List.mem_append_right _ hp)
    unfold chooseTwo at hp
    split_ifs at hp
    all_goals
      by_cases hi : i = 0
      · simp only [pairAllocation, ite_eq_left hi] at hp
        first | exact hpreKnown p hp | exact hsufKnown p hp
      · simp only [pairAllocation, ite_eq_right hi] at hp
        first | exact hpreKnown p hp | exact hsufKnown p hp

end EnvyFreeResearch.Full.Chores.Population
