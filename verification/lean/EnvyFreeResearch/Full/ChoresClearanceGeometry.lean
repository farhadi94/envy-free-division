import EnvyFreeResearch.Full.ChoresSnapshotGeometry

/-! Clearance snapshots may use different cutters. Their allocations remain
fixed, and their literal residual domains decrease for every observer. A
same-cutter block has the multiplicative contraction supplied by Core. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Snapshot
open Set MeasureTheory OrderedUnion InitialPartition PackageGeometry

variable {n : ℕ} {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

def contraction (n : ℕ) : ℝ := ((n-1 : ℕ) : ℝ)/n

theorem contraction_nonneg (n : ℕ) : 0 ≤ contraction n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem Chain.final_cache {U : Set ℝ} {c : Fin n} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : Chain cost c U xs cache) :
    CacheValid (measureProfile cost) (material cache) cache := by
  induction chain with
  | nil U cache hc => exact ⟨hc.1,hc.2.1,rfl⟩
  | cons _ _ ih => exact ih

theorem Chain.contracts {U : Set ℝ} {c : Fin n} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : Chain cost c U xs cache) :
    (cost c).real (material cache) ≤ contraction n ^ xs.length * (cost c).real U := by
  induction chain with
  | nil U cache hc => simpa only [List.length_nil,pow_zero,one_mul,hc.2.2] using le_rfl
  | @cons U first rest cache hfirst hrest ih =>
    calc
      (cost c).real (material cache) ≤ contraction n ^ rest.length *
          (cost c).real (domainResidue U first.outcome) := ih
      _ ≤ contraction n ^ rest.length * (contraction n * (cost c).real U) :=
        mul_le_mul_of_nonneg_left hfirst.core.2.2.2.2.1
          (pow_nonneg (contraction_nonneg n) _)
      _ = contraction n ^ (first::rest).length * (cost c).real U := by
        rw [List.length_cons,pow_succ,mul_assoc]

inductive AnyChain (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)] :
    Set ℝ → List (Output n) → List (Parent n) → Prop
  | nil (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache) :
      AnyChain cost U [] cache
  | cons {U : Set ℝ} {first : Output n} {rest : List (Output n)} {cache : List (Parent n)}
      (c : Fin n) (hfirst : Sound cost U c first)
      (hrest : AnyChain cost (domainResidue U first.outcome) rest cache) :
      AnyChain cost U (first::rest) cache

theorem Chain.any {U : Set ℝ} {c : Fin n} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : Chain cost c U xs cache) : AnyChain cost U xs cache := by
  induction chain with
  | nil U cache hc => exact AnyChain.nil U cache hc
  | cons hfirst _ ih => exact AnyChain.cons c hfirst ih

theorem AnyChain.final_cache {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache) :
    CacheValid (measureProfile cost) (material cache) cache := by
  induction chain with
  | nil U cache hc => exact ⟨hc.1,hc.2.1,rfl⟩
  | cons _ _ _ ih => exact ih

theorem AnyChain.append {U : Set ℝ} {xs ys : List (Output n)}
    {middle cache : List (Parent n)} (first : AnyChain cost U xs middle)
    (rest : AnyChain cost (material middle) ys cache) : AnyChain cost U (xs++ys) cache := by
  induction first with
  | nil U middle hc => simpa only [List.nil_append,hc.2.2] using rest
  | cons c hfirst _ ih => exact AnyChain.cons c hfirst (ih rest)

theorem AnyChain.subsets {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache) :
    (∀ out ∈ xs, out.carrier ⊆ U) ∧ material cache ⊆ U := by
  induction chain with
  | nil U cache hc => exact ⟨by simp,hc.2.2 ▸ Subset.rfl⟩
  | @cons U first rest cache c hfirst hrest ih =>
    have hr : domainResidue U first.outcome ⊆ U := by
      rw [← hfirst.residue_eq]
      exact hfirst.residue_subset
    refine ⟨?_,ih.2.trans hr⟩
    intro out hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hfirst.carrier_subset
    · exact (ih.1 out hm).trans hr

theorem AnyChain.residue_value_le {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache) (i : Fin n) :
    (cost i).real (material cache) ≤ (cost i).real U := measureReal_mono chain.subsets.2

theorem AnyChain.cover {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache) :
    batchMaterial xs ∪ material cache = U := by
  induction chain with
  | nil U cache hc => simpa only [batchMaterial,empty_union] using hc.2.2
  | @cons U first rest cache c hfirst hrest ih =>
    rw [batchMaterial,union_assoc,ih,← hfirst.residue_eq]
    exact hfirst.cover

theorem AnyChain.final_residue_disjoint {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache) :
    Disjoint (batchMaterial xs) (material cache) := by
  induction chain with
  | nil _ _ _ => simp [batchMaterial]
  | @cons U first rest cache c hfirst hrest ih =>
    apply disjoint_union_left.mpr
    refine ⟨?_,ih⟩
    have hsub := hrest.subsets.2
    rw [← hfirst.residue_eq] at hsub
    exact hfirst.carrier_residue_disjoint.mono_right hsub

theorem AnyChain.roots_disjoint {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache) :
    xs.Pairwise (fun a b => Disjoint a.carrier b.carrier) := by
  induction chain with
  | nil _ _ _ => exact List.Pairwise.nil
  | @cons U first rest cache c hfirst hrest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro other hm
    have hsub := hrest.subsets.1 other hm
    rw [← hfirst.residue_eq] at hsub
    exact hfirst.carrier_residue_disjoint.mono_right hsub

theorem AnyChain.member_sound {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache)
    (out : Output n) (hm : out ∈ xs) : ∃ c domain, Sound cost domain c out := by
  induction chain with
  | nil _ _ _ => cases hm
  | @cons U first rest cache c hfirst hrest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨c,U,hfirst⟩
    · exact ih hm

end EnvyFreeResearch.Full.Chores.Snapshot
