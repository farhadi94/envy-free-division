import EnvyFreeResearch.Full.ChoresUnionCut

/-! The ordered-union programs act on actual finite nonatomic measures.
Cached sums equal the measures of their literal finite-union materials. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

theorem material_measurable {n : ℕ} (ps : List (Parent n)) : MeasurableSet (material ps) := by
  induction ps with
  | nil => exact MeasurableSet.empty
  | cons p ps ih => exact measurableSet_Ioc.union ih

theorem material_value {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (ps : List (Parent n)) (hp : Valid (measureProfile cost) ps) (ho : Ordered ps) (i : Fin n) :
    (cost i).real (material ps) = cachedValue ps i := by
  induction ps with
  | nil => simp [material,cachedValue]
  | cons p ps ih =>
    obtain ⟨hp,hps⟩ := hp
    obtain ⟨hbefore,horder⟩ := List.pairwise_cons.mp ho
    rw [material,measureReal_union (disjoint_material_of_before p ps hbefore) (material_measurable ps),
      ih hps horder]
    change (cost i).real (Ioc p.left p.right)+cachedValue ps i = p.value i+cachedValue ps i
    rw [hp.2 i]
    exact congrArg (fun x => x+cachedValue ps i)
      (prefix_difference_eq_interval (cost i) hp.1.1 hp.1.2.1).symm

/-- One input-independent ordinary-query program cuts the requested physical
prefix from any cached ordered union, for every legal adaptive reply policy.
All observers' component caches remain exact on both returned materials. -/
theorem split_union_measures {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (ps : List (Parent n)) (hp : Valid (measureProfile cost) ps) (ho : Ordered ps)
    (t : ℝ) (ht : 0 ≤ t) (htop : t ≤ (cost c).real (material ps)) :
    ∃ out : Split n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (splitProgram c t ps).protocol oracle () n [] = ⟨trace,.returned out⟩ ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      material out.prefixParts ∪ material out.suffixParts = material ps ∧
      Disjoint (material out.prefixParts) (material out.suffixParts) ∧
      Ordered (out.prefixParts ++ out.suffixParts) ∧
      Valid (measureProfile cost) out.prefixParts ∧ Valid (measureProfile cost) out.suffixParts ∧
      (cost c).real (material out.prefixParts) = t ∧
      out.prefixParts.length+out.suffixParts.length ≤ ps.length+1 ∧
      ∀ i, (cost i).real (material out.prefixParts) = cachedValue out.prefixParts i ∧
        (cost i).real (material out.suffixParts) = cachedValue out.suffixParts i := by
  have hmono : ∀ i, Monotone ((measureProfile cost).cumulative i) :=
    fun i => prefixCost_monotone (cost i) 0
  have htarget : t ≤ cachedValue ps c := by rwa [material_value cost ps hp ho] at htop
  obtain ⟨out,trace,hexec,hlen,hcuts,hsplit,hvalidpre,hvalidsuf,hvalue⟩ :=
    split_program_correct (measureProfile cost) hmono oracle hpolicy c ps hp t ht htarget []
  have horder := hsplit.ordered ho
  have hopre : Ordered out.prefixParts := (List.pairwise_append.mp horder).1
  have hosuf : Ordered out.suffixParts := (List.pairwise_append.mp horder).2.1
  refine ⟨out,trace,hexec.run n hlen,hlen,hcuts,hsplit.cover,hsplit.disjoint ho,horder,
    hvalidpre,hvalidsuf,?_,hsplit.length_bound,?_⟩
  · rw [material_value cost out.prefixParts hvalidpre hopre,hvalue]
  · intro i
    exact ⟨material_value cost out.prefixParts hvalidpre hopre i,
      material_value cost out.suffixParts hvalidsuf hosuf i⟩

theorem suffix_union_measures {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (ps : List (Parent n)) (hp : Valid (measureProfile cost) ps) (ho : Ordered ps)
    (t : ℝ) (ht : 0 ≤ t) (htop : t ≤ (cost c).real (material ps)) :
    ∃ out : SuffixSplit n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (suffixProgram c t ps).protocol oracle () n [] = ⟨trace,.returned out⟩ ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      material out.prefixParts ∪ material out.suffixParts = material ps ∧
      Disjoint (material out.prefixParts) (material out.suffixParts) ∧
      Ordered (out.prefixParts ++ out.suffixParts) ∧
      Valid (measureProfile cost) out.prefixParts ∧ Valid (measureProfile cost) out.suffixParts ∧
      (cost c).real (material out.suffixParts) = t ∧
      out.prefixParts.length+out.suffixParts.length ≤ ps.length+1 ∧
      ∀ i, (cost i).real (material out.prefixParts) = cachedValue out.prefixParts i ∧
        (cost i).real (material out.suffixParts) = cachedValue out.suffixParts i := by
  have hmono : ∀ i, Monotone ((measureProfile cost).cumulative i) :=
    fun i => prefixCost_monotone (cost i) 0
  have htarget : t ≤ cachedValue ps c := by rwa [material_value cost ps hp ho] at htop
  obtain ⟨out,trace,hexec,hlen,hcuts,hsplit,hvalidsuf,hvalidpre,hvalue⟩ :=
    suffix_program_correct (measureProfile cost) hmono oracle hpolicy c ps hp t ht htarget []
  have horder := hsplit.ordered ho
  have hopre : Ordered out.prefixParts := (List.pairwise_append.mp horder).1
  have hosuf : Ordered out.suffixParts := (List.pairwise_append.mp horder).2.1
  refine ⟨out,trace,hexec.run n hlen,hlen,hcuts,hsplit.cover,hsplit.disjoint ho,horder,
    hvalidpre,hvalidsuf,?_,hsplit.length_bound,?_⟩
  · rw [material_value cost out.suffixParts hvalidsuf hosuf,hvalue]
  · intro i
    exact ⟨material_value cost out.prefixParts hvalidpre hopre i,
      material_value cost out.suffixParts hvalidsuf hosuf i⟩

end EnvyFreeResearch.Full.Chores.OrderedUnion
