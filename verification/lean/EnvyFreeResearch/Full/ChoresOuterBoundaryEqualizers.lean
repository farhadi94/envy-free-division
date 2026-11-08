import EnvyFreeResearch.Full.ChoresComponentBoundaryUnion
import EnvyFreeResearch.Full.ChoresEqualizerTable

/-! Parametric coordinate provenance for every recorded original equalizer.
Inherited endpoints and literal earlier Cut replies suffice for every
query and every returned coordinate, even with null components and ties. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Equalizers
open scoped Classical

variable {n : ℕ}

def EqualizerKnown (points : Set ℝ) (record : RestrictedCutResult n) : Prop :=
  record.point ∈ points ∧ CacheKnown points (record.parts.prefixParts ++ record.parts.suffixParts)

def TableKnown (points : Set ℝ) (table : Table n) : Prop := ∀ pair, EqualizerKnown points (table pair)

theorem EqualizerKnown.mono {old more : Set ℝ} {record : RestrictedCutResult n}
    (h : EqualizerKnown old record) (hm : old ⊆ more) : EqualizerKnown more record :=
  ⟨hm h.1,h.2.mono hm⟩

theorem TableKnown.mono {old more : Set ℝ} {table : Table n}
    (h : TableKnown old table) (hm : old ⊆ more) : TableKnown more table :=
  fun pair => (h pair).mono hm

theorem equalizer_record_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (hzero : (0 : ℝ) ∈ points) (owner observer : Fin n)
    (baseline : Fin n → ℝ) (cache : List (Parent n)) (hc : CacheKnown points cache)
    (prior : History (Query (Fin n)) ℝ) (out : RestrictedCutResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Equalizers.recordProgram owner observer baseline cache) prior out trace) :
    EqualizerKnown (Known points trace) out ∧ Scoped points trace := by
  by_cases heq : observer=owner
  · simp only [Equalizers.recordProgram,ite_eq_left heq] at h
    cases h
    simp only [EqualizerKnown,known_nil,List.append_nil]
    exact ⟨⟨endpoint_known points 0 hzero cache hc,hc⟩,trivial⟩
  · simp only [Equalizers.recordProgram,ite_eq_right heq] at h
    obtain ⟨hcache,hscope,hpoint⟩ := restricted_cut_known oracle points observer 0 (baseline observer)
      hzero cache hc prior out trace h
    exact ⟨⟨hpoint,hcache⟩,hscope⟩

theorem equalizer_list_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (hzero : (0 : ℝ) ∈ points)
    (baseline : Fin n → ℝ) (parents : Fin n → List (Parent n))
    (hc : ∀ p, CacheKnown points (parents p))
    (pairs : List (Fin n × Fin n)) (prior : History (Query (Fin n)) ℝ)
    (out : Table n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (recordList baseline parents pairs) prior out trace) :
    TableKnown (Known points trace) out ∧ Scoped points trace := by
  induction pairs generalizing points prior out trace with
  | nil =>
    cases h
    refine ⟨fun pair => ?_,trivial⟩
    exact ⟨by simpa only [known_nil] using hzero,by simp [CacheKnown]⟩
  | cons pair rest ih =>
    obtain ⟨first,t₁,tail,hfirst,htail,htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨second,t₂,empty,hsecond,hreturn,htailtrace⟩ := Executes.split_bind _ _ htail
    cases hreturn
    simp only [List.append_nil] at htailtrace
    subst tail
    subst trace
    obtain ⟨hknown₁,hscope₁⟩ := equalizer_record_known oracle points hzero pair.1 pair.2 baseline
      (parents pair.1) (hc pair.1) prior first t₁ hfirst
    obtain ⟨hknown₂,hscope₂⟩ := ih (Known points t₁) (Or.inl hzero)
      (fun p => (hc p).mono subset_union_left) (prior++t₁) second t₂ hsecond
    refine ⟨?_,(scoped_append points t₁ t₂).mpr ⟨hscope₁,hscope₂⟩⟩
    intro q
    by_cases hq : q=pair
    · subst q
      rw [Function.update_self]
      exact hknown₁.mono (known_mono points t₁ t₂)
    · rw [Function.update_of_ne hq]
      simpa only [known_append] using hknown₂ q

theorem equalizer_table_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (hzero : (0 : ℝ) ∈ points) (parents : Fin n → List (Parent n))
    (hc : ∀ p, CacheKnown points (parents p))
    (prior : History (Query (Fin n)) ℝ) (out : Table n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (recordTable parents) prior out trace) :
    TableKnown (Known points trace) out ∧ Scoped points trace :=
  equalizer_list_known oracle points hzero (baselines parents) parents hc Finset.univ.toList prior out trace h

end EnvyFreeResearch.Full.Chores.Boundary
