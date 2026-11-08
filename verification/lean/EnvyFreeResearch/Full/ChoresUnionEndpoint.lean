import EnvyFreeResearch.Full.ChoresUnionMeasures

/-! Recover the physical endpoint of the compiled finite-union prefix.
Cached boundary cases and positive-length zero-cost components are included. -/

namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set InitialPartition

variable {n : ℕ}

def endpoint (a : ℝ) : List (Parent n) → ℝ
  | [] => a
  | p :: ps => endpoint p.right ps

def Within (a b : ℝ) (ps : List (Parent n)) : Prop :=
  ∀ p ∈ ps, a ≤ p.left ∧ p.left ≤ p.right ∧ p.right ≤ b

theorem material_within {a b : ℝ} {ps : List (Parent n)} (h : Within a b ps) :
    material ps ⊆ Ioc a b := by
  induction ps with
  | nil => exact empty_subset _
  | cons p ps ih =>
    apply union_subset
    · intro x hx
      exact ⟨(h p List.mem_cons_self).1.trans_lt hx.1,
        hx.2.trans (h p List.mem_cons_self).2.2⟩
    · exact ih (fun q hq => h q (List.mem_cons_of_mem p hq))

/-- The returned endpoint separates the complete input material into the
two literal lists, even when an entire zero-cost component is traversed. -/
theorem PrefixSplit.endpoint_spec {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) {a b : ℝ} (hab : a ≤ b)
    (hw : Within a b ps) (ho : Ordered ps) :
    a ≤ endpoint a pre ∧ endpoint a pre ≤ b ∧
      material pre ⊆ Iic (endpoint a pre) ∧ material suf ⊆ Ioi (endpoint a pre) := by
  induction h generalizing a b with
  | zero ps =>
    refine ⟨le_rfl,hab,empty_subset _,?_⟩
    intro x hx
    exact (material_within hw hx).1
  | @cons p ps pre suf h ih =>
    have hp := hw p List.mem_cons_self
    obtain ⟨hbefore,horder⟩ := List.pairwise_cons.mp ho
    have hrest : Within p.right b ps := by
      intro q hq
      exact ⟨hbefore q hq,(hw q (List.mem_cons_of_mem p hq)).2⟩
    obtain ⟨hl,hu,hpre,hsuf⟩ := ih hp.2.2 hrest horder
    refine ⟨(hp.1.trans hp.2.1).trans hl,hu,?_,hsuf⟩
    apply union_subset
    · intro x hx
      exact hx.2.trans hl
    · exact hpre
  | cut p ps x values hx =>
    have hp := hw p List.mem_cons_self
    obtain ⟨hbefore,horder⟩ := List.pairwise_cons.mp ho
    refine ⟨hp.1.trans hx.1,hx.2.trans hp.2.2,?_,?_⟩
    · intro y hy
      have hy' : y ∈ Ioc p.left x := by simpa only [material,leftPart,union_empty] using hy
      exact hy'.2
    · intro y hy
      change y ∈ Ioc x p.right ∪ material ps at hy
      rcases hy with hy | hy
      · exact hy.1
      · have hrest : Within p.right b ps := fun q hq =>
          ⟨hbefore q hq,(hw q (List.mem_cons_of_mem p hq)).2⟩
        exact hx.2.trans_lt (material_within hrest hy).1

theorem PrefixSplit.prefix_eq {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) {a b : ℝ} (hab : a ≤ b)
    (hw : Within a b ps) (ho : Ordered ps) :
    material pre = material ps ∩ Iic (endpoint a pre) := by
  obtain ⟨hl,hu,hpre,hsuf⟩ := h.endpoint_spec hab hw ho
  ext x
  constructor
  · intro hx
    exact ⟨by rw [← h.cover]; exact Or.inl hx,hpre hx⟩
  · rintro ⟨hx,hcut⟩
    rw [← h.cover] at hx
    rcases hx with hx | hx
    · exact hx
    · exact (not_lt_of_ge (show x ≤ endpoint a pre from hcut)
        (show endpoint a pre < x from hsuf hx)).elim

theorem PrefixSplit.suffix_eq {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) {a b : ℝ} (hab : a ≤ b)
    (hw : Within a b ps) (ho : Ordered ps) :
    material suf = material ps ∩ Ioi (endpoint a pre) := by
  obtain ⟨hl,hu,hpre,hsuf⟩ := h.endpoint_spec hab hw ho
  ext x
  constructor
  · intro hx
    exact ⟨by rw [← h.cover]; exact Or.inr hx,hsuf hx⟩
  · rintro ⟨hx,hcut⟩
    rw [← h.cover] at hx
    rcases hx with hx | hx
    · exact (not_lt_of_ge (show x ≤ endpoint a pre from hpre hx)
        (show endpoint a pre < x from hcut)).elim
    · exact hx

theorem PrefixSplit.restricted_prefix {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) {a b : ℝ} (hab : a ≤ b)
    (hw : Within a b ps) (ho : Ordered ps) (U : Set ℝ)
    (hmaterial : material ps = U ∩ Ioc a b) :
    material pre = U ∩ Ioc a (endpoint a pre) := by
  rw [h.prefix_eq hab hw ho,hmaterial]
  have he := (h.endpoint_spec hab hw ho).2.1
  ext x
  simp only [mem_inter_iff,mem_Ioc,mem_Iic]
  constructor
  · rintro ⟨⟨hU,hax,hxb⟩,hxe⟩
    exact ⟨hU,hax,hxe⟩
  · rintro ⟨hU,hax,hxe⟩
    exact ⟨⟨hU,hax,hxe.trans he⟩,hxe⟩

/-- The endpoint is a boundary of every retained component, not merely an
almost-everywhere separator of their values. -/
theorem PrefixSplit.component_endpoint_spec {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) {a b : ℝ} (hab : a ≤ b)
    (hw : Within a b ps) (ho : Ordered ps) :
    (∀ p ∈ pre, p.right ≤ endpoint a pre) ∧
      (∀ p ∈ suf, endpoint a pre ≤ p.left) := by
  induction h generalizing a b with
  | zero ps =>
    exact ⟨by simp,fun p hp => (hw p hp).1⟩
  | @cons p ps pre suf h ih =>
    have hp := hw p List.mem_cons_self
    obtain ⟨hbefore,horder⟩ := List.pairwise_cons.mp ho
    have hrest : Within p.right b ps := fun q hq =>
      ⟨hbefore q hq,(hw q (List.mem_cons_of_mem p hq)).2⟩
    have hbound := (h.endpoint_spec hp.2.2 hrest horder).1
    obtain ⟨hpre,hsuf⟩ := ih hp.2.2 hrest horder
    refine ⟨?_,hsuf⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hbound
    · exact hpre q hq
  | cut p ps x values hx =>
    obtain ⟨hbefore,horder⟩ := List.pairwise_cons.mp ho
    constructor
    · intro q hq
      have hq' := List.mem_singleton.mp hq
      subst q
      exact le_rfl
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact le_rfl
      · exact hx.2.trans (hbefore q hq)

end EnvyFreeResearch.Full.Chores.OrderedUnion
