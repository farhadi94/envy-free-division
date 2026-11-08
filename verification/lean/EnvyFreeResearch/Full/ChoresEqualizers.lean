import EnvyFreeResearch.Full.ChoresUnionCoreParts

/-! Actual recorded equalizers of a Core snapshot. Every own equalizer is
the entire original share, including its zero-cost material. Other equalizers
are cut from the recorded original share and retain exact all-observer costs.
The program uses only cached values and ordinary interval oracle requests. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Equalizers
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ}

theorem full_prefix_split (ps : List (Parent n)) : PrefixSplit ps ps [] := by
  induction ps with
  | nil => exact PrefixSplit.zero []
  | cons p ps ih => exact PrefixSplit.cons p ih

def recordProgram (owner observer : Fin n) (baseline : Fin n → ℝ) (ps : List (Parent n)) :
    Program (Query (Fin n)) ℝ (RestrictedCutResult n) :=
  if observer = owner then .returned ⟨endpoint 0 ps,⟨ps,[]⟩,cachedValue ps⟩
  else restrictedCutProgram observer 0 (baseline observer) ps

def Correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (baseline : Fin n → ℝ) (observer : Fin n) (out : RestrictedCutResult n) : Prop :=
  out.point ∈ Icc 0 1 ∧
  CacheValid (measureProfile cost) (U ∩ Iic out.point) out.parts.prefixParts ∧
  CacheValid (measureProfile cost) (U ∩ Ioi out.point) out.parts.suffixParts ∧
  (cost observer).real (U ∩ Iic out.point) = baseline observer ∧
  (∀ i, out.values i = (cost i).real (U ∩ Iic out.point))

theorem record_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (ps : List (Parent n)) (hc : CacheValid (measureProfile cost) U ps)
    (owner observer : Fin n) (baseline : Fin n → ℝ)
    (hbase : 0 ≤ baseline observer) (hfeasible : baseline observer ≤ cachedValue ps observer)
    (hown : baseline owner = cachedValue ps owner) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : RestrictedCutResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordProgram owner observer baseline ps) prior out trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      Correct cost U baseline observer out ∧
      (observer = owner → out.parts.prefixParts = ps ∧ out.parts.suffixParts = [] ∧ trace = []) := by
  have hw : Within 0 1 ps := fun p hp => ((valid_iff_forall _ _).mp hc.1 p hp).1
  have hsource : ∃ out : RestrictedCutResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordProgram owner observer baseline ps) prior out trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      PrefixSplit ps out.parts.prefixParts out.parts.suffixParts ∧
      Valid (measureProfile cost) out.parts.prefixParts ∧
      Valid (measureProfile cost) out.parts.suffixParts ∧
      cachedValue out.parts.prefixParts observer = baseline observer ∧
      out.point = endpoint 0 out.parts.prefixParts ∧ out.values = cachedValue out.parts.prefixParts ∧
      (observer = owner → out.parts.prefixParts = ps ∧ out.parts.suffixParts = [] ∧ trace = []) := by
    by_cases heq : observer = owner
    · subst observer
      refine ⟨⟨endpoint 0 ps,⟨ps,[]⟩,cachedValue ps⟩,[],?_,Nat.zero_le _,by simp,
        full_prefix_split ps,hc.1,trivial,hown.symm,rfl,rfl,by simp⟩
      simpa only [recordProgram,ite_true] using
        (Executes.returned (oracle := oracle) (⟨endpoint 0 ps,⟨ps,[]⟩,cachedValue ps⟩ : RestrictedCutResult n) prior)
    · obtain ⟨parts,trace,hexec,hlen,hcuts,hsplit,hvp,hvs,hvalue⟩ :=
        split_program_correct (measureProfile cost) (fun i => prefixCost_monotone (cost i) 0)
          oracle hpolicy observer ps hc.1 (baseline observer) hbase hfeasible prior
      refine ⟨⟨endpoint 0 parts.prefixParts,parts,cachedValue parts.prefixParts⟩,trace,
        ?_,hlen,hcuts,hsplit,hvp,hvs,hvalue,rfl,rfl,fun h => (heq h).elim⟩
      have h := hexec.bind (fun parts => Program.returned
        (⟨endpoint 0 parts.prefixParts,parts,cachedValue parts.prefixParts⟩ : RestrictedCutResult n))
        (Executes.returned _ (prior++trace))
      simpa only [recordProgram,ite_eq_right heq,restrictedCutProgram,List.append_nil] using h
  obtain ⟨out,trace,hexec,hlen,hcuts,hsplit,hvp,hvs,hvalue,hpoint,hvalues,hownResult⟩ := hsource
  have horder := List.pairwise_append.mp (hsplit.ordered hc.2.1)
  have hpre : material out.parts.prefixParts = U ∩ Iic out.point := by
    rw [hpoint,hsplit.prefix_eq zero_le_one hw hc.2.1,hc.2.2]
  have hsuf : material out.parts.suffixParts = U ∩ Ioi out.point := by
    rw [hpoint,hsplit.suffix_eq zero_le_one hw hc.2.1,hc.2.2]
  have hbound := hsplit.endpoint_spec zero_le_one hw hc.2.1
  refine ⟨out,trace,hexec,hlen,hcuts,?_,hownResult⟩
  refine ⟨by simpa only [hpoint,Set.mem_Icc] using And.intro hbound.1 hbound.2.1,
    ⟨hvp,horder.1,hpre⟩,⟨hvs,horder.2.1,hsuf⟩,?_,?_⟩
  · rw [← hpre,material_value cost _ hvp horder.1,hvalue]
  · intro i
    rw [hvalues,← hpre,material_value cost _ hvp horder.1]

end EnvyFreeResearch.Full.Chores.Equalizers
