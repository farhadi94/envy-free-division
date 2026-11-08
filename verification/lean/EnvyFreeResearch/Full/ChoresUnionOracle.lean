import EnvyFreeResearch.Full.ChoresUnionEndpoint

/-! The physical union-cut macro supplies exact replies for the continuous
CDF of a restricted domain. This is the local oracle bridge; it does not
assume a free query oracle for disconnected domains. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

def restrictedProfile {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) : Profile (Fin n) := measureProfile (fun i => (cost i).restrict U)

theorem restricted_interval_value {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (i : Fin n) :
    (restrictedProfile cost U).cumulative i b-(restrictedProfile cost U).cumulative i a =
      (cost i).real (U ∩ Ioc a b) := by
  change prefixCost ((cost i).restrict U) 0 b-prefixCost ((cost i).restrict U) 0 a = _
  rw [prefix_difference_eq_interval ((cost i).restrict U) ha hab,
    measureReal_restrict_apply measurableSet_Ioc,inter_comm]

theorem cached_restricted_interval {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (ps : List (Parent n)) (hp : Valid (measureProfile cost) ps) (ho : Ordered ps)
    (hmaterial : material ps = U ∩ Ioc a b) (i : Fin n) :
    (restrictedProfile cost U).cumulative i b-(restrictedProfile cost U).cumulative i a =
      cachedValue ps i := by
  rw [restricted_interval_value cost U ha hab,← hmaterial,material_value cost ps hp ho]

structure RestrictedCutResult (n : ℕ) where
  point : ℝ
  parts : Split n
  values : Fin n → ℝ

/-- The returned endpoint and every value are computed from the physical
split's cached output; only the split itself makes ordinary oracle calls. -/
def restrictedCutProgram {n : ℕ} (c : Fin n) (a t : ℝ) (ps : List (Parent n)) :
    Program (Query (Fin n)) ℝ (RestrictedCutResult n) :=
  (splitProgram c t ps).bind (fun out =>
    .returned ⟨endpoint a out.prefixParts,out,cachedValue out.prefixParts⟩)

theorem restricted_cut_program_correct {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (c : Fin n) (a b t : ℝ) (hb : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1)
    (ps : List (Parent n)) (hp : Valid (measureProfile cost) ps) (ho : Ordered ps)
    (hw : Within a b ps) (hmaterial : material ps = U ∩ Ioc a b)
    (ht : 0 ≤ t) (htop : t ≤ cachedValue ps c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : RestrictedCutResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (restrictedCutProgram c a t ps) prior out trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      ValidReply (restrictedProfile cost U) (.cut c a b t) out.point ∧
      (∀ i, out.values i = (restrictedProfile cost U).cumulative i out.point-
        (restrictedProfile cost U).cumulative i a) ∧
      out.values c = t ∧
      PrefixSplit ps out.parts.prefixParts out.parts.suffixParts ∧
      Valid (measureProfile cost) out.parts.prefixParts ∧
      Valid (measureProfile cost) out.parts.suffixParts ∧
      Ordered (out.parts.prefixParts ++ out.parts.suffixParts) ∧
      out.point = endpoint a out.parts.prefixParts := by
  have hmono : ∀ i, Monotone ((measureProfile cost).cumulative i) :=
    fun i => prefixCost_monotone (cost i) 0
  obtain ⟨parts,trace,hexec,hlen,hcuts,hsplit,hvalidpre,hvalidsuf,hvalue⟩ :=
    split_program_correct (measureProfile cost) hmono oracle hpolicy c ps hp t ht htop prior
  have he := hsplit.endpoint_spec hb.2.1 hw ho
  have horder := hsplit.ordered ho
  have hpreorder : Ordered parts.prefixParts := (List.pairwise_append.mp horder).1
  have hvalues (i : Fin n) : cachedValue parts.prefixParts i =
      (restrictedProfile cost U).cumulative i (endpoint a parts.prefixParts)-
        (restrictedProfile cost U).cumulative i a := by
    rw [restricted_interval_value cost U hb.1 he.1,
      ← hsplit.restricted_prefix hb.2.1 hw ho U hmaterial,
      material_value cost parts.prefixParts hvalidpre hpreorder]
  let out : RestrictedCutResult n := ⟨endpoint a parts.prefixParts,parts,cachedValue parts.prefixParts⟩
  refine ⟨out,trace,?_,hlen,hcuts,?_,hvalues,hvalue,hsplit,hvalidpre,hvalidsuf,horder,rfl⟩
  · simpa only [restrictedCutProgram,List.append_nil] using hexec.bind
      (fun parts => Program.returned (⟨endpoint a parts.prefixParts,parts,cachedValue parts.prefixParts⟩ : RestrictedCutResult n))
      (Executes.returned _ _)
  · refine ⟨⟨he.1,he.2.1⟩,?_⟩
    change (restrictedProfile cost U).cumulative c (endpoint a parts.prefixParts) =
      (restrictedProfile cost U).cumulative c a+t
    have hdiff := (hvalues c).symm.trans hvalue
    linarith

end EnvyFreeResearch.Full.Chores.OrderedUnion
