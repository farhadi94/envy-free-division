import EnvyFreeResearch.Full.ChoresQuantileGeometry

/-! Successive equal-cost prefix extractions form an actual physical
quantile refinement. Every strict target is cut inside one cached component
and recorded for all enclosing observers. Null components are retained. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Quantile
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion

variable {n : ℕ}

def equalGrid (c : Fin n) (t : ℝ) : ℕ → List (Parent n) → Program (Query (Fin n)) ℝ (List (Parent n))
  | 0, cache => .returned cache
  | k+1, cache => (splitProgram c t cache).bind (fun first =>
      (equalGrid c t k first.suffixParts).bind (fun rest => .returned (first.prefixParts++rest)))

theorem equal_grid_correct (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (t : ℝ) (ht : 0 ≤ t) (k : ℕ)
    (cache : List (Parent n)) (hv : Valid P cache) (ho : Ordered cache)
    (htotal : cachedValue cache c = (k+1 : ℕ)*t)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh trace, Executes oracle (equalGrid c t k cache) prior fresh trace ∧
      trace.length ≤ k*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ k ∧
      Valid P fresh ∧ Ordered fresh ∧ material fresh=material cache ∧ Refines cache fresh ∧
      (∀ i, cachedValue fresh i=cachedValue cache i) ∧
      (∀ p ∈ fresh, p.value c ≤ t) ∧ fresh.length ≤ cache.length+k := by
  induction k generalizing cache prior with
  | zero =>
    refine ⟨cache,[],Executes.returned _ _,by simp,by simp,hv,ho,rfl,Refines.refl _,fun _ => rfl,?_,by simp⟩
    intro p hp
    have h := value_le_total P hmono cache hv p hp c
    simpa only [Nat.zero_add,Nat.cast_one,one_mul] using h.trans_eq htotal
  | succ k ih =>
    have htarget : t ≤ cachedValue cache c := by
      rw [htotal]
      push_cast
      nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    obtain ⟨first,t₁,hexec₁,hQ₁,hC₁,hsplit,hpre,hsuf,hvalue⟩ :=
      split_program_correct P hmono oracle hpolicy c cache hv t ht htarget prior
    have horder := hsplit.ordered ho
    have hsuforder := (List.pairwise_append.mp horder).2.1
    have hsufvalue : cachedValue first.suffixParts c = (k+1 : ℕ)*t := by
      have h := hsplit.cached_add c
      rw [hvalue,htotal] at h
      push_cast at h ⊢
      linarith
    obtain ⟨tail,t₂,hexec₂,hQ₂,hC₂,hvalid₂,horder₂,hmaterial₂,href₂,htotal₂,hsmall₂,hlen₂⟩ :=
      ih first.suffixParts hsuf hsuforder hsufvalue (prior++t₁)
    refine ⟨first.prefixParts++tail,t₁++t₂,?_,?_,?_,(valid_append _ _ _).mpr ⟨hpre,hvalid₂⟩,
      append_ordered horder horder₂ href₂,?_,append_refines hsplit href₂,?_,?_,?_⟩
    · have htail := hexec₂.bind (fun rest => Program.returned (first.prefixParts++rest))
        (Executes.returned _ ((prior++t₁)++t₂))
      exact hexec₁.bind (fun first => (equalGrid c t k first.suffixParts).bind
        (fun rest => Program.returned (first.prefixParts++rest)))
        (by simpa only [List.append_nil] using htail)
    · simp only [List.length_append]
      calc
        t₁.length+t₂.length ≤ n+k*n := Nat.add_le_add hQ₁ hQ₂
        _ = (k+1)*n := by ring
    · simp only [List.countP_append]
      omega
    · rw [material_append,hmaterial₂,hsplit.cover]
    · intro i
      rw [cachedValue_append,htotal₂]
      exact hsplit.cached_add i
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (value_le_total P hmono first.prefixParts hpre p hp c).trans_eq hvalue
      · exact hsmall₂ p hp
    · have hlen₁ := hsplit.length_bound
      simp only [List.length_append]
      omega

end EnvyFreeResearch.Full.Chores.Quantile
