import EnvyFreeResearch.Full.ChoresQuantileGrid

/-! Common physical quantile refinement for a fixed list of observers.
All input totals are cached. Each observer contributes at most K-1 new
cuts, and every later refinement preserves earlier small-cell bounds. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Quantile
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion

variable {n : ℕ}

def singleGrid (c : Fin n) (K : ℕ) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (List (Parent n)) :=
  equalGrid c (cachedValue cache c/K) (K-1) cache

theorem single_grid_correct (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (K : ℕ) (hK : 0 < K) (cache : List (Parent n))
    (hv : Valid P cache) (ho : Ordered cache) (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh trace, Executes oracle (singleGrid c K cache) prior fresh trace ∧
      trace.length ≤ (K-1)*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ K-1 ∧
      Valid P fresh ∧ Ordered fresh ∧ material fresh=material cache ∧ Refines cache fresh ∧
      (∀ i, cachedValue fresh i=cachedValue cache i) ∧
      (∀ p ∈ fresh, p.value c ≤ cachedValue cache c/K) ∧ fresh.length ≤ cache.length+(K-1) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have ht : 0 ≤ cachedValue cache c/(K : ℝ) :=
    div_nonneg (cachedValue_nonnegative P hmono hv c) hKreal.le
  have htotal : cachedValue cache c = (K-1+1 : ℕ)*(cachedValue cache c/(K : ℝ)) := by
    rw [Nat.sub_add_cancel hK]
    field_simp
  exact equal_grid_correct P hmono oracle hpolicy c _ ht (K-1) cache hv ho htotal prior

def commonGrid (K : ℕ) : List (Fin n) → List (Parent n) → Program (Query (Fin n)) ℝ (List (Parent n))
  | [], cache => .returned cache
  | c::rest, cache => (singleGrid c K cache).bind (fun fresh => commonGrid K rest fresh)

theorem common_grid_correct (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (K : ℕ) (hK : 0 < K) (observers : List (Fin n)) (cache : List (Parent n))
    (hv : Valid P cache) (ho : Ordered cache) (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh trace, Executes oracle (commonGrid K observers cache) prior fresh trace ∧
      trace.length ≤ observers.length*(K-1)*n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ observers.length*(K-1) ∧
      Valid P fresh ∧ Ordered fresh ∧ material fresh=material cache ∧ Refines cache fresh ∧
      (∀ i, cachedValue fresh i=cachedValue cache i) ∧
      (∀ i ∈ observers, ∀ p ∈ fresh, p.value i ≤ cachedValue cache i/K) ∧
      fresh.length ≤ cache.length+observers.length*(K-1) := by
  induction observers generalizing cache prior with
  | nil =>
    exact ⟨cache,[],Executes.returned _ _,by simp,by simp,hv,ho,rfl,Refines.refl _,fun _ => rfl,by simp,by simp⟩
  | cons c rest ih =>
    obtain ⟨middle,t₁,hexec₁,hQ₁,hC₁,hv₁,ho₁,hmat₁,href₁,htotal₁,hsmall₁,hlen₁⟩ :=
      single_grid_correct P hmono oracle hpolicy c K hK cache hv ho prior
    obtain ⟨fresh,t₂,hexec₂,hQ₂,hC₂,hv₂,ho₂,hmat₂,href₂,htotal₂,hsmall₂,hlen₂⟩ :=
      ih middle hv₁ ho₁ (prior++t₁)
    refine ⟨fresh,t₁++t₂,hexec₁.bind (fun fresh => commonGrid K rest fresh) hexec₂,?_,?_,
      hv₂,ho₂,hmat₂.trans hmat₁,href₁.trans href₂,fun i => (htotal₂ i).trans (htotal₁ i),?_,?_⟩
    · simp only [List.length_append,List.length_cons]
      calc
        t₁.length+t₂.length ≤ (K-1)*n+rest.length*(K-1)*n := Nat.add_le_add hQ₁ hQ₂
        _ = (rest.length+1)*(K-1)*n := by ring
    · simp only [List.countP_append,List.length_cons]
      calc
        t₁.countP (fun qr => isCutQuery qr.1)+t₂.countP (fun qr => isCutQuery qr.1) ≤
            (K-1)+rest.length*(K-1) := Nat.add_le_add hC₁ hC₂
        _ = (rest.length+1)*(K-1) := by ring
    · intro i hi p hp
      rcases List.mem_cons.mp hi with rfl | hi
      · exact href₂.cost_bound P hmono hv₁ hv₂ i _ hsmall₁ p hp
      · simpa only [htotal₁] using hsmall₂ i hi p hp
    · simp only [List.length_cons]
      calc
        fresh.length ≤ middle.length+rest.length*(K-1) := hlen₂
        _ ≤ (cache.length+(K-1))+rest.length*(K-1) := Nat.add_le_add_right hlen₁ _
        _ = cache.length+(rest.length+1)*(K-1) := by ring

end EnvyFreeResearch.Full.Chores.Quantile
