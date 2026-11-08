import EnvyFreeResearch.Full.ChoresClearanceGeometry

/-! The actual finite clearance program. The immutable tracked table is
read only. A successful trigger is removed from the pending list; all of
its later values remain large because the physical residue only decreases.
The program uses ordinary Core snapshots and records every clearance
allocation and every query, including the equalizer overhead of snapshots. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Clearance
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Snapshot
open scoped Classical

structure Entry (n : ℕ) where
  observer : Fin n
  value : ℝ

variable {n : ℕ} {Index : Type*} [DecidableEq Index]

def middle (H : ℝ) (entry : Entry n) (cache : List (Parent n)) : Prop :=
  cachedValue cache entry.observer/H < entry.value ∧
    entry.value < H*cachedValue cache entry.observer

def program (entries : Index → Entry n) (H : ℝ) (L : ℕ) :
    ℕ → List Index → List (Parent n) → Program (Query (Fin n)) ℝ (Batch n)
  | 0, _, cache => .returned ⟨[],cache⟩
  | fuel+1, pending, cache =>
      match pending.find? (fun t => decide (middle H (entries t) cache)) with
      | none => .returned ⟨[],cache⟩
      | some t => (generate (entries t).observer L cache).bind (fun first =>
          (program entries H L fuel (pending.erase t) first.residue).bind (fun rest =>
            .returned ⟨first.snapshots++rest.snapshots,rest.residue⟩))

def Large (entries : Index → Entry n) (cost : Fin n → Measure ℝ) (H : ℝ)
    (U : Set ℝ) (t : Index) : Prop := H*(cost (entries t).observer).real U ≤ (entries t).value

def Separated (entries : Index → Entry n) (cost : Fin n → Measure ℝ) (H : ℝ)
    (U : Set ℝ) : Prop := ∀ t, (entries t).value ≤ (cost (entries t).observer).real U/H ∨
      Large entries cost H U t

theorem cached_total (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (i : Fin n) : cachedValue cache i = (cost i).real U := by
  rw [← material_value cost cache hc.1 hc.2.1,hc.2.2]

theorem large_after_block (H α r r' v : ℝ) (hH : 0 < H) (hr : 0 ≤ r)
    (hscale : H*α ≤ 1/H) (hsmall : r/H < v) (hshrink : r' ≤ α*r) : H*r' ≤ v := by
  calc
    H*r' ≤ H*(α*r) := mul_le_mul_of_nonneg_left hshrink hH.le
    _ = (H*α)*r := (mul_assoc _ _ _).symm
    _ ≤ (1/H)*r := mul_le_mul_of_nonneg_right hscale hr
    _ = r/H := by ring
    _ ≤ v := hsmall.le

theorem separated_of_no_middle (entries : Index → Entry n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (H : ℝ) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (pending : List Index)
    (hinv : ∀ t, t ∉ pending → Large entries cost H U t)
    (hstop : pending.find? (fun t => decide (middle H (entries t) cache)) = none) :
    Separated entries cost H U := by
  intro t
  by_cases ht : t ∈ pending
  · have hnot := List.find?_eq_none.mp hstop t ht
    have hm : ¬ middle H (entries t) cache := by simpa only [decide_eq_true_eq] using hnot
    simp only [middle,cached_total cost U cache hc] at hm
    by_cases hsmall : (entries t).value ≤ (cost (entries t).observer).real U/H
    · exact Or.inl hsmall
    · exact Or.inr (le_of_not_gt (fun hlarge => hm ⟨lt_of_not_ge hsmall,hlarge⟩))
  · exact Or.inr (hinv t ht)

theorem program_correct (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (entries : Index → Entry n) (H : ℝ) (hH : 0 < H) (L : ℕ)
    (hscale : H*contraction n^L ≤ 1/H)
    (fuel : ℕ) (pending : List Index) (hlen : pending.length ≤ fuel)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (hinv : ∀ t, t ∉ pending → Large entries cost H U t)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ batch trace, Executes oracle (program entries H L fuel pending cache) prior batch trace ∧
      batch.snapshots.length ≤ fuel*L ∧ trace.length ≤ fuel*L*queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ fuel*L*cutBudget n ∧
      AnyChain cost U batch.snapshots batch.residue ∧
      Separated entries cost H (material batch.residue) := by
  induction fuel generalizing pending U cache prior with
  | zero =>
    have hp : pending = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    refine ⟨⟨[],cache⟩,[],Executes.returned _ _,by simp,by simp,by simp,AnyChain.nil U cache hc,?_⟩
    rw [hc.2.2]
    intro t
    exact Or.inr (hinv t (by simp [hp]))
  | succ fuel ih =>
    cases hfind : pending.find? (fun t => decide (middle H (entries t) cache)) with
    | none =>
      refine ⟨⟨[],cache⟩,[],?_,by simp,by simp,by simp,AnyChain.nil U cache hc,?_⟩
      · simp only [program,hfind]
        exact Executes.returned _ _
      · rw [hc.2.2]
        exact separated_of_no_middle entries cost H U cache hc pending hinv hfind
    | some t =>
      have ht : t ∈ pending := List.mem_of_find?_eq_some hfind
      have hm : middle H (entries t) cache := by
        simpa only [decide_eq_true_eq] using List.find?_some hfind
      have hsmall : (cost (entries t).observer).real U/H < (entries t).value := by
        simpa only [middle,cached_total cost U cache hc] using hm.1
      obtain ⟨first,t₁,hexec₁,hcount₁,hQ₁,hC₁,hchain₁⟩ :=
        generate_correct hn cost oracle hpolicy U cache hc (entries t).observer L prior
      have hcache₁ := hchain₁.final_cache
      have hcontract := hchain₁.contracts
      rw [hcount₁] at hcontract
      have htlarge : Large entries cost H (material first.residue) t :=
        large_after_block H (contraction n^L) _ _ _ hH measureReal_nonneg hscale hsmall hcontract
      have hinv₁ : ∀ u, u ∉ pending.erase t → Large entries cost H (material first.residue) u := by
        intro u hu
        by_cases hut : u = t
        · simpa only [hut] using htlarge
        · have hout : u ∉ pending := fun h => hu ((List.mem_erase_of_ne hut).mpr h)
          exact (mul_le_mul_of_nonneg_left (hchain₁.any.residue_value_le (entries u).observer) hH.le).trans
            (hinv u hout)
      have hlen₁ : (pending.erase t).length ≤ fuel := by
        have := List.length_erase_add_one ht
        omega
      obtain ⟨rest,t₂,hexec₂,hcount₂,hQ₂,hC₂,hchain₂,hsep₂⟩ :=
        ih (pending.erase t) hlen₁ (material first.residue) first.residue hcache₁ hinv₁ (prior++t₁)
      refine ⟨⟨first.snapshots++rest.snapshots,rest.residue⟩,t₁++t₂,?_,?_,?_,?_,
        hchain₁.any.append hchain₂,hsep₂⟩
      · simp only [program,hfind]
        have he₂ := hexec₂.bind (fun rest => Program.returned
          (⟨first.snapshots++rest.snapshots,rest.residue⟩ : Batch n))
          (Executes.returned _ ((prior++t₁)++t₂))
        exact hexec₁.bind (fun first => (program entries H L fuel (pending.erase t) first.residue).bind
          (fun rest => Program.returned (⟨first.snapshots++rest.snapshots,rest.residue⟩ : Batch n)))
          (by simpa only [List.append_nil] using he₂)
      · simp only [List.length_append,hcount₁]
        calc
          L+rest.snapshots.length ≤ L+fuel*L := Nat.add_le_add_left hcount₂ L
          _ = (fuel+1)*L := by ring
      · simp only [List.length_append]
        calc
          t₁.length+t₂.length ≤ L*queryBudget n+fuel*L*queryBudget n := Nat.add_le_add hQ₁ hQ₂
          _ = (fuel+1)*L*queryBudget n := by ring
      · simp only [List.countP_append]
        calc
          t₁.countP (fun qr => isCutQuery qr.1)+t₂.countP (fun qr => isCutQuery qr.1) ≤
              L*cutBudget n+fuel*L*cutBudget n := Nat.add_le_add hC₁ hC₂
          _ = (fuel+1)*L*cutBudget n := by ring

end EnvyFreeResearch.Full.Chores.Clearance
