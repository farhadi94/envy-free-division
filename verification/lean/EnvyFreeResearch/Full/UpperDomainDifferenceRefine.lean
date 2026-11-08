import EnvyFreeResearch.Full.UpperRecordedDomain

/-!
# Literal refinement of recorded components

A cut preserves the original carrier's endpoint ownership. Its left child
contains the cut endpoint when the original carrier did; its right child
excludes it. Degenerate singleton and empty children are retained.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain

def leftPart (c : Component) (p : ℝ) (hp : c.left ≤ p ∧ p ≤ c.right) : Component where
  left := c.left
  right := p
  left_nonneg := c.left_nonneg
  left_le_right := hp.1
  right_le_one := hp.2.trans c.right_le_one
  carrier := c.carrier ∩ Iic p
  measurable_carrier := c.measurable_carrier.inter measurableSet_Iic
  interior_subset := fun _ hx => ⟨c.interior_subset ⟨hx.1, hx.2.trans_le hp.2⟩, hx.2.le⟩
  subset_closed := fun _ hx => ⟨(c.subset_closed hx.1).1, hx.2⟩

def rightPart (c : Component) (p : ℝ) (hp : c.left ≤ p ∧ p ≤ c.right) : Component where
  left := p
  right := c.right
  left_nonneg := c.left_nonneg.trans hp.1
  left_le_right := hp.2
  right_le_one := c.right_le_one
  carrier := c.carrier ∩ Ioi p
  measurable_carrier := c.measurable_carrier.inter measurableSet_Ioi
  interior_subset := fun _ hx => ⟨c.interior_subset ⟨hp.1.trans_lt hx.1, hx.2⟩, hx.1⟩
  subset_closed := fun _ hx => ⟨hx.2.le, (c.subset_closed hx.1).2⟩

def splitAt (p : ℝ) (c : Component) : List Component :=
  if hp : c.left ≤ p ∧ p ≤ c.right then [leftPart c p hp, rightPart c p hp] else [c]

theorem domain_append (cs ds : List Component) : domain (cs ++ ds) = domain cs ∪ domain ds := by
  induction cs with
  | nil => simp [domain]
  | cons c cs ih => simp [domain, ih, union_assoc]

theorem splitAt_domain (p : ℝ) (c : Component) : domain (splitAt p c) = c.carrier := by
  unfold splitAt
  split_ifs with hp
  · ext x
    simp only [domain, leftPart, rightPart, union_empty, mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      rcases le_or_gt x p with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  · simp [domain]

theorem splitAt_subpart (p : ℝ) (c d : Component) (hd : d ∈ splitAt p c) :
    d.carrier ⊆ c.carrier ∧ c.left ≤ d.left ∧ d.right ≤ c.right := by
  unfold splitAt at hd
  split_ifs at hd with hp
  · rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨inter_subset_left, le_rfl, hp.2⟩
    · have hd' : d = rightPart c p hp := by simpa using hd
      subst d
      exact ⟨inter_subset_left, hp.1, le_rfl⟩
  · have hd' : d = c := by simpa using hd
    subst d
    exact ⟨Subset.rfl, le_rfl, le_rfl⟩

theorem splitAt_ordered (p : ℝ) (c : Component) : Ordered (splitAt p c) := by
  unfold splitAt
  split_ifs <;> simp [Ordered, leftPart, rightPart]

theorem splitAt_disjoint (p : ℝ) (c : Component) : DisjointComponents (splitAt p c) := by
  unfold splitAt
  split_ifs with hp
  · simp only [DisjointComponents, List.pairwise_cons, List.mem_singleton, forall_eq]
    refine ⟨?_, by simp⟩
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (show x ≤ p from hx.2)) (show p < x from hy.2)
  · simp [DisjointComponents]

/-- If a component extends strictly past a recorded boundary, its carrier
lies strictly past that boundary. Components ending at the boundary retain
all their inherited endpoint fragments. -/
def SeparatedAt (p : ℝ) (cs : List Component) : Prop :=
  ∀ c ∈ cs, p < c.right → c.carrier ⊆ Ioi p

theorem splitAt_separated (p : ℝ) (c : Component) : SeparatedAt p (splitAt p c) := by
  intro d hd hright
  unfold splitAt at hd
  split_ifs at hd with hp
  · rcases List.mem_cons.mp hd with rfl | hd
    · exact False.elim ((lt_irrefl p) hright)
    · have hd' : d = rightPart c p hp := by simpa using hd
      subst d
      exact inter_subset_right
  · have hd' : d = c := by simpa using hd
    subst d
    have hleft : p < c.left := lt_of_not_ge (fun hl => hp ⟨hl, hright.le⟩)
    intro x hx
    exact hleft.trans_le (c.subset_closed hx).1

def refineAt (p : ℝ) (cs : List Component) : List Component := cs.flatMap (splitAt p)

theorem mem_refineAt {p : ℝ} {cs : List Component} {d : Component} :
    d ∈ refineAt p cs ↔ ∃ c ∈ cs, d ∈ splitAt p c := by simp [refineAt]

theorem refineAt_domain (p : ℝ) (cs : List Component) : domain (refineAt p cs) = domain cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change domain (splitAt p c ++ refineAt p cs) = c.carrier ∪ domain cs
    rw [domain_append, splitAt_domain, ih]

theorem refineAt_pairwise (p : ℝ) (R : Component → Component → Prop)
    (hinside : ∀ c, (splitAt p c).Pairwise R)
    (hcross : ∀ c d, R c d → ∀ u ∈ splitAt p c, ∀ v ∈ splitAt p d, R u v)
    (cs : List Component) (hcs : cs.Pairwise R) : (refineAt p cs).Pairwise R := by
  induction cs with
  | nil => simp [refineAt]
  | cons c cs ih =>
    have hh := List.pairwise_cons.mp hcs
    change (splitAt p c ++ refineAt p cs).Pairwise R
    apply List.pairwise_append.mpr
    refine ⟨hinside c, ih hh.2, ?_⟩
    intro u hu v hv
    obtain ⟨d, hd, hv⟩ := mem_refineAt.mp hv
    exact hcross c d (hh.1 d hd) u hu v hv

theorem refineAt_ordered (p : ℝ) (cs : List Component) (hcs : Ordered cs) :
    Ordered (refineAt p cs) := by
  apply refineAt_pairwise p _ (splitAt_ordered p) _ cs hcs
  intro c d hcd u hu v hv
  exact (splitAt_subpart p c u hu).2.2.trans (hcd.trans (splitAt_subpart p d v hv).2.1)

theorem refineAt_disjoint (p : ℝ) (cs : List Component) (hcs : DisjointComponents cs) :
    DisjointComponents (refineAt p cs) := by
  apply refineAt_pairwise p _ (splitAt_disjoint p) _ cs hcs
  intro c d hcd u hu v hv
  exact hcd.mono (splitAt_subpart p c u hu).1 (splitAt_subpart p d v hv).1

theorem refineAt_separated (p : ℝ) (cs : List Component) : SeparatedAt p (refineAt p cs) := by
  intro d hd
  obtain ⟨c, _, hd⟩ := mem_refineAt.mp hd
  exact splitAt_separated p c d hd

theorem refineAt_preserves_separated (p q : ℝ) (cs : List Component) (hcs : SeparatedAt q cs) :
    SeparatedAt q (refineAt p cs) := by
  intro d hd hright
  obtain ⟨c, hc, hd⟩ := mem_refineAt.mp hd
  have hp := splitAt_subpart p c d hd
  exact hp.1.trans (hcs c hc (hright.trans_le hp.2.2))

def Recorded (cs : List Component) (p : ℝ) : Prop :=
  ∃ c ∈ cs, p = c.left ∨ p = c.right

theorem splitAt_endpoints (p : ℝ) (c d : Component) (hd : d ∈ splitAt p c) :
    (d.left = c.left ∨ d.left = p) ∧ (d.right = c.right ∨ d.right = p) := by
  unfold splitAt at hd
  split_ifs at hd with hp
  · rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · have hd' : d = rightPart c p hp := by simpa using hd
      subst d
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  · have hd' : d = c := by simpa using hd
    subst d
    exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem refineAt_recorded (p : ℝ) (cs : List Component) {q : ℝ}
    (hq : Recorded (refineAt p cs) q) : q = p ∨ Recorded cs q := by
  obtain ⟨d, hd, hq⟩ := hq
  obtain ⟨c, hc, hd⟩ := mem_refineAt.mp hd
  have he := splitAt_endpoints p c d hd
  rcases hq with rfl | rfl
  · rcases he.1 with he | he
    · exact Or.inr ⟨c, hc, Or.inl he⟩
    · exact Or.inl he
  · rcases he.2 with he | he
    · exact Or.inr ⟨c, hc, Or.inr he⟩
    · exact Or.inl he


/-- Every old bound remains an explicitly represented bound after refinement,
including the bounds of singleton and empty components. -/
theorem recorded_refineAt (p : ℝ) (cs : List Component) {q : ℝ}
    (hq : Recorded cs q) : Recorded (refineAt p cs) q := by
  obtain ⟨c, hc, hq⟩ := hq
  by_cases hp : c.left ≤ p ∧ p ≤ c.right
  · rcases hq with rfl | rfl
    · refine ⟨leftPart c p hp, mem_refineAt.mpr ⟨c, hc, ?_⟩, Or.inl rfl⟩
      simp [splitAt, hp]
    · refine ⟨rightPart c p hp, mem_refineAt.mpr ⟨c, hc, ?_⟩, Or.inr rfl⟩
      simp [splitAt, hp]
  · exact ⟨c, mem_refineAt.mpr ⟨c, hc, by simp [splitAt, hp]⟩, hq⟩

theorem splitAt_length_le (p : ℝ) (c : Component) : (splitAt p c).length ≤ 2 := by
  unfold splitAt
  split_ifs <;> simp

theorem refineAt_length_le (p : ℝ) (cs : List Component) :
    (refineAt p cs).length ≤ 2 * cs.length := by
  induction cs with
  | nil => simp [refineAt]
  | cons c cs ih =>
    change (splitAt p c ++ refineAt p cs).length ≤ _
    rw [List.length_append, List.length_cons]
    have hh := splitAt_length_le p c
    omega

end EnvyFreeResearch.Full.UpperDomainDifference
