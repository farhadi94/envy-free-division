import EnvyFreeResearch.Full.ChoresUnionCache

/-! Updating the global domain cache after a physical cut of one aligned
window. Every previous recorded endpoint remains a component boundary. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set IntervalOracle InitialPartition

variable {n : ℕ}

theorem material_append (ps qs : List (Parent n)) :
    material (ps ++ qs) = material ps ∪ material qs := by
  induction ps with
  | nil => simp [material]
  | cons p ps ih => simp only [List.cons_append,material,ih,union_assoc]

theorem valid_append (P : Profile (Fin n)) (ps qs : List (Parent n)) :
    Valid P (ps ++ qs) ↔ Valid P ps ∧ Valid P qs := by
  simp only [valid_iff_forall,List.mem_append,or_imp,forall_and]

def before (a : ℝ) (ps : List (Parent n)) : List (Parent n) :=
  ps.filter (fun p => decide (p.right ≤ a))

def after (b : ℝ) (ps : List (Parent n)) : List (Parent n) :=
  ps.filter (fun p => decide (b ≤ p.left))

theorem mem_before {a : ℝ} {ps : List (Parent n)} {p : Parent n} :
    p ∈ before a ps ↔ p ∈ ps ∧ p.right ≤ a := by simp [before]

theorem mem_after {b : ℝ} {ps : List (Parent n)} {p : Parent n} :
    p ∈ after b ps ↔ p ∈ ps ∧ b ≤ p.left := by simp [after]

theorem before_material {a : ℝ} {ps : List (Parent n)} (ha : Aligned ps a) :
    material (before a ps) = material ps ∩ Iic a := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hx
    obtain ⟨hp,hpa⟩ := mem_before.mp hp
    exact ⟨(mem_material_iff _ _).mpr ⟨p,hp,hpx⟩,hpx.2.trans hpa⟩
  · rintro ⟨hx,hxa⟩
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hx
    have hpa : p.right ≤ a := (ha p hp).resolve_right (fun hap =>
      (not_lt_of_ge (show x ≤ a from hxa)) (hap.trans_lt hpx.1))
    exact (mem_material_iff _ _).mpr ⟨p,mem_before.mpr ⟨hp,hpa⟩,hpx⟩

theorem after_material {b : ℝ} {ps : List (Parent n)} (hb : Aligned ps b) :
    material (after b ps) = material ps ∩ Ioi b := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hx
    obtain ⟨hp,hbp⟩ := mem_after.mp hp
    exact ⟨(mem_material_iff _ _).mpr ⟨p,hp,hpx⟩,hbp.trans_lt hpx.1⟩
  · rintro ⟨hx,hbx⟩
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hx
    have hbp : b ≤ p.left := (hb p hp).resolve_left (fun hpb =>
      (not_lt_of_ge (hpx.2.trans hpb)) (show b < x from hbx))
    exact (mem_material_iff _ _).mpr ⟨p,mem_after.mpr ⟨hp,hbp⟩,hpx⟩

theorem decompose_material {a b : ℝ} {ps : List (Parent n)}
    (ha : Aligned ps a) (hb : Aligned ps b) :
    material (before a ps) ∪ (material (window a b ps) ∪ material (after b ps)) = material ps := by
  rw [before_material ha,window_material ha hb,after_material hb]
  ext x
  simp only [mem_union,mem_inter_iff,mem_Iic,mem_Ioc,mem_Ioi]
  constructor
  · rintro (⟨h,_⟩ | ⟨h,_,_⟩ | ⟨h,_⟩) <;> exact h
  · intro hx
    by_cases hxa : x ≤ a
    · exact Or.inl ⟨hx,hxa⟩
    · by_cases hxb : x ≤ b
      · exact Or.inr (Or.inl ⟨hx,lt_of_not_ge hxa,hxb⟩)
      · exact Or.inr (Or.inr ⟨hx,lt_of_not_ge hxb⟩)

def replaceWindow (a b : ℝ) (ps fresh : List (Parent n)) : List (Parent n) :=
  before a ps ++ (fresh ++ after b ps)

theorem replaceWindow_valid (P : Profile (Fin n)) {a b : ℝ} {ps fresh : List (Parent n)}
    (hp : Valid P ps) (hf : Valid P fresh) : Valid P (replaceWindow a b ps fresh) := by
  apply (valid_append _ _ _).mpr
  exact ⟨valid_filter P hp _,(valid_append _ _ _).mpr ⟨hf,valid_filter P hp _⟩⟩

theorem replaceWindow_ordered {a b : ℝ} {ps fresh : List (Parent n)} (hab : a ≤ b)
    (ho : Ordered ps) (hf : Ordered fresh) (hw : Within a b fresh) :
    Ordered (replaceWindow a b ps fresh) := by
  apply List.pairwise_append.mpr
  refine ⟨ho.filter _,?_,?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨hf,ho.filter _,?_⟩
    intro p hp q hq
    exact (hw p hp).2.2.trans (mem_after.mp hq).2
  · intro p hp q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact (mem_before.mp hp).2.trans (hw q hq).1
    · exact ((mem_before.mp hp).2.trans hab).trans (mem_after.mp hq).2

theorem replaceWindow_material {a b : ℝ} {ps fresh : List (Parent n)}
    (ha : Aligned ps a) (hb : Aligned ps b)
    (hf : material fresh = material (window a b ps)) :
    material (replaceWindow a b ps fresh) = material ps := by
  rw [replaceWindow,material_append,material_append,hf,decompose_material ha hb]

theorem replaceWindow_contained {a b : ℝ} {ps fresh : List (Parent n)}
    (hf : ∀ q ∈ fresh, ∃ p ∈ window a b ps, p.left ≤ q.left ∧ q.right ≤ p.right) :
    ∀ q ∈ replaceWindow a b ps fresh, ∃ p ∈ ps, p.left ≤ q.left ∧ q.right ≤ p.right := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact ⟨q,(mem_before.mp hq).1,le_rfl,le_rfl⟩
  · rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨p,hp,hl,hr⟩ := hf q hq
      exact ⟨p,(mem_window.mp hp).1,hl,hr⟩
    · exact ⟨q,(mem_after.mp hq).1,le_rfl,le_rfl⟩

theorem prefixSplit_within (P : Profile (Fin n)) {a b : ℝ}
    {ps pre suf : List (Parent n)} (hs : PrefixSplit ps pre suf)
    (hw : Within a b ps) (hv : Valid P (pre++suf)) : Within a b (pre++suf) := by
  intro q hq
  obtain ⟨p,hp,hl,hr⟩ := hs.component_contained hq
  exact ⟨(hw p hp).1.trans hl,((valid_iff_forall _ _).mp hv q hq).1.2.1,
    hr.trans (hw p hp).2.2⟩

/-- The old and new query boundaries are simultaneously retained. -/
theorem replaceWindow_alignment {a b : ℝ} {ps pre suf : List (Parent n)} (hab : a ≤ b)
    (hs : PrefixSplit (window a b ps) pre suf)
    (hw : Within a b (window a b ps)) (ho : Ordered (window a b ps)) :
    Aligned (replaceWindow a b ps (pre++suf)) (endpoint a pre) ∧
      ∀ x, Aligned ps x → Aligned (replaceWindow a b ps (pre++suf)) x := by
  have he := hs.endpoint_spec hab hw ho
  obtain ⟨hpre,hsuf⟩ := hs.component_endpoint_spec hab hw ho
  constructor
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ((mem_before.mp hq).2.trans he.1)
    · rcases List.mem_append.mp hq with hq | hq
      · rcases List.mem_append.mp hq with hq | hq
        · exact Or.inl (hpre q hq)
        · exact Or.inr (hsuf q hq)
      · exact Or.inr (he.2.1.trans (mem_after.mp hq).2)
  · intro x hx
    apply aligned_of_refinement hx
    apply replaceWindow_contained
    exact fun q hq => hs.component_contained hq

end EnvyFreeResearch.Full.Chores.OrderedUnion
