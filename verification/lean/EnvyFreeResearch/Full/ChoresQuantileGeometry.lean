import EnvyFreeResearch.Full.ChoresUnionRefinement

/-! Refinement preserves all existing physical component boundaries and
every previously established component-cost bound. These facts are used
when quantile grids for successive observers are combined. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Quantile
open Set IntervalOracle InitialPartition OrderedUnion

variable {n : ℕ}

def Refines (old fresh : List (Parent n)) : Prop :=
  ∀ q ∈ fresh, ∃ p ∈ old, p.left ≤ q.left ∧ q.right ≤ p.right

theorem Refines.refl (old : List (Parent n)) : Refines old old :=
  fun q hq => ⟨q,hq,le_rfl,le_rfl⟩

theorem Refines.trans {a b c : List (Parent n)} (hab : Refines a b) (hbc : Refines b c) :
    Refines a c := by
  intro r hr
  obtain ⟨q,hq,hql,hqr⟩ := hbc r hr
  obtain ⟨p,hp,hpl,hpr⟩ := hab q hq
  exact ⟨p,hp,hpl.trans hql,hqr.trans hpr⟩

theorem split_refines {old pre suf : List (Parent n)} (h : PrefixSplit old pre suf) :
    Refines old (pre++suf) := fun _ hq => h.component_contained hq

theorem append_refines {old pre suf fresh : List (Parent n)} (h : PrefixSplit old pre suf)
    (hf : Refines suf fresh) : Refines old (pre++fresh) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h.component_contained (List.mem_append_left _ hq)
  · obtain ⟨r,hr,hl,hu⟩ := hf q hq
    obtain ⟨p,hp,hpl,hpr⟩ := h.component_contained (List.mem_append_right _ hr)
    exact ⟨p,hp,hpl.trans hl,hu.trans hpr⟩

theorem append_ordered {pre suf fresh : List (Parent n)} (h : Ordered (pre++suf))
    (hf : Ordered fresh) (href : Refines suf fresh) : Ordered (pre++fresh) := by
  obtain ⟨hp,_,hcross⟩ := List.pairwise_append.mp h
  apply List.pairwise_append.mpr
  refine ⟨hp,hf,?_⟩
  intro p hp q hq
  obtain ⟨r,hr,hl,_⟩ := href q hq
  exact (hcross p hp r hr).trans hl

theorem cachedValue_append (a b : List (Parent n)) (i : Fin n) :
    cachedValue (a++b) i=cachedValue a i+cachedValue b i := by
  induction a with
  | nil => simp [cachedValue]
  | cons p a ih => simp only [List.cons_append,cachedValue,ih,add_assoc]

theorem value_le_total (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (cache : List (Parent n)) (hv : Valid P cache) (p : Parent n) (hp : p ∈ cache) (i : Fin n) :
    p.value i ≤ cachedValue cache i := by
  induction cache with
  | nil => cases hp
  | cons q rest ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_add_of_nonneg_right (cachedValue_nonnegative P hmono hv.2 i)
    · have hle := ih hv.2 hp
      exact hle.trans (le_add_of_nonneg_left (validPart_nonnegative P hmono hv.1 i))

theorem contained_value_le (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    {p q : Parent n} (hp : ValidPart P p) (hq : ValidPart P q)
    (hl : p.left ≤ q.left) (hr : q.right ≤ p.right) (i : Fin n) : q.value i ≤ p.value i := by
  rw [hq.2 i,hp.2 i]
  exact sub_le_sub (hmono i hr) (hmono i hl)

theorem Refines.cost_bound (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    {old fresh : List (Parent n)} (href : Refines old fresh) (hold : Valid P old) (hf : Valid P fresh)
    (i : Fin n) (bound : ℝ) (hbound : ∀ p ∈ old, p.value i ≤ bound) :
    ∀ q ∈ fresh, q.value i ≤ bound := by
  intro q hq
  obtain ⟨p,hp,hl,hr⟩ := href q hq
  exact (contained_value_le P hmono ((valid_iff_forall _ _).mp hold p hp)
    ((valid_iff_forall _ _).mp hf q hq) hl hr i).trans (hbound p hp)

end EnvyFreeResearch.Full.Chores.Quantile
