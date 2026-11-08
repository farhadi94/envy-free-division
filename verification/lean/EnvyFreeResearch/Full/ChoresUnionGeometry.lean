import EnvyFreeResearch.Full.ChoresInitialPartition

/-! Literal geometry and cached values of a prefix of an ordered finite
union. Zero-cost components are retained as material, not discarded. -/

namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set IntervalOracle InitialPartition

variable {n : ℕ}

def material : List (Parent n) → Set ℝ
  | [] => ∅
  | p :: ps => Ioc p.left p.right ∪ material ps

def cachedValue : List (Parent n) → Fin n → ℝ
  | [], _ => 0
  | p :: ps, i => p.value i + cachedValue ps i

def ValidPart (P : Profile (Fin n)) (p : Parent n) : Prop :=
  (0 ≤ p.left ∧ p.left ≤ p.right ∧ p.right ≤ 1) ∧
    ∀ i, p.value i = P.cumulative i p.right - P.cumulative i p.left

def Valid (P : Profile (Fin n)) : List (Parent n) → Prop
  | [] => True
  | p :: ps => ValidPart P p ∧ Valid P ps

def Ordered (ps : List (Parent n)) : Prop :=
  ps.Pairwise (fun p q => p.right ≤ q.left)

def leftPart (p : Parent n) (x : ℝ) (values : Fin n → ℝ) : Parent n :=
  ⟨p.left,x,values⟩

def rightPart (p : Parent n) (x : ℝ) (values : Fin n → ℝ) : Parent n :=
  ⟨x,p.right,fun i => p.value i-values i⟩

/-- A literal prefix consists of whole initial components and at most one
split component. The suffix retains all remaining material. -/
inductive PrefixSplit : List (Parent n) → List (Parent n) → List (Parent n) → Prop
  | zero (ps) : PrefixSplit ps [] ps
  | cons (p) {ps pre suf} : PrefixSplit ps pre suf → PrefixSplit (p::ps) (p::pre) suf
  | cut (p) (ps) (x : ℝ) (values : Fin n → ℝ) (hx : x ∈ Icc p.left p.right) :
      PrefixSplit (p::ps) [leftPart p x values] (rightPart p x values :: ps)

theorem PrefixSplit.cached_add {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) (i : Fin n) :
    cachedValue pre i + cachedValue suf i = cachedValue ps i := by
  induction h with
  | zero ps => simp [cachedValue]
  | cons p h ih => simp only [cachedValue]; linarith
  | cut p ps x values hx => simp only [cachedValue,leftPart,rightPart]; ring

theorem PrefixSplit.cover {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) : material pre ∪ material suf = material ps := by
  induction h with
  | zero ps => simp [material]
  | cons p h ih => simpa only [material,union_assoc] using congrArg (fun s => Ioc p.left p.right ∪ s) ih
  | cut p ps x values hx =>
    simp only [material,leftPart,rightPart,union_empty,← union_assoc,Ioc_union_Ioc_eq_Ioc hx.1 hx.2]

theorem PrefixSplit.component_contained {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) {q : Parent n} (hq : q ∈ pre ++ suf) :
    ∃ p ∈ ps, p.left ≤ q.left ∧ q.right ≤ p.right := by
  induction h with
  | zero ps => exact ⟨q,by simpa using hq,le_rfl,le_rfl⟩
  | @cons p ps pre suf h ih =>
    rcases List.mem_cons.mp hq with heq | hq
    · subst q
      exact ⟨p,List.mem_cons_self,le_rfl,le_rfl⟩
    · obtain ⟨r,hr,hl,hu⟩ := ih hq
      exact ⟨r,List.mem_cons_of_mem p hr,hl,hu⟩
  | cut p ps x values hx =>
    simp only [List.singleton_append,List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact ⟨p,List.mem_cons_self,le_rfl,hx.2⟩
    · exact ⟨p,List.mem_cons_self,hx.1,le_rfl⟩
    · exact ⟨q,List.mem_cons_of_mem p hq,le_rfl,le_rfl⟩

theorem PrefixSplit.ordered {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) (ho : Ordered ps) : Ordered (pre ++ suf) := by
  induction h with
  | zero ps => simpa using ho
  | @cons p ps pre suf h ih =>
    obtain ⟨hp,hps⟩ := List.pairwise_cons.mp ho
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih hps⟩
    intro q hq
    obtain ⟨r,hr,hl,hu⟩ := h.component_contained hq
    exact (hp r hr).trans hl
  | cut p ps x values hx =>
    obtain ⟨hp,hps⟩ := List.pairwise_cons.mp ho
    apply List.pairwise_cons.mpr
    constructor
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact le_rfl
      · exact hx.2.trans (hp q hq)
    · exact List.pairwise_cons.mpr ⟨hp,hps⟩

theorem disjoint_material_of_before (p : Parent n) (ps : List (Parent n))
    (h : ∀ q ∈ ps, p.right ≤ q.left) :
    Disjoint (Ioc p.left p.right) (material ps) := by
  induction ps with
  | nil => simp [material]
  | cons q qs ih =>
    apply disjoint_union_right.mpr
    exact ⟨Ioc_disjoint_Ioc_of_le (h q List.mem_cons_self),
      ih (fun r hr => h r (List.mem_cons_of_mem q hr))⟩

theorem disjoint_material_of_separated (pre suf : List (Parent n))
    (h : ∀ p ∈ pre, ∀ q ∈ suf, p.right ≤ q.left) :
    Disjoint (material pre) (material suf) := by
  induction pre with
  | nil => simp [material]
  | cons p ps ih =>
    exact disjoint_union_left.mpr ⟨disjoint_material_of_before p suf (h p List.mem_cons_self),
      ih (fun q hq => h q (List.mem_cons_of_mem p hq))⟩

theorem PrefixSplit.disjoint {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) (ho : Ordered ps) : Disjoint (material pre) (material suf) := by
  have horder := List.pairwise_append.mp (h.ordered ho)
  exact disjoint_material_of_separated pre suf horder.2.2

theorem PrefixSplit.length_bound {ps pre suf : List (Parent n)}
    (h : PrefixSplit ps pre suf) : pre.length+suf.length ≤ ps.length+1 := by
  induction h with
  | zero ps => simp
  | cons p h ih => simp only [List.length_cons]; omega
  | cut p ps x values hx => simp only [List.length_cons,List.length_nil]; omega

theorem validPart_nonnegative (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    {p : Parent n} (hp : ValidPart P p) (i : Fin n) : 0 ≤ p.value i := by
  rw [hp.2 i]
  exact sub_nonneg.mpr (hmono i hp.1.2.1)

theorem cachedValue_nonnegative (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    {ps : List (Parent n)} (hp : Valid P ps) (i : Fin n) : 0 ≤ cachedValue ps i := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih => exact add_nonneg (validPart_nonnegative P hmono hp.1 i) (ih hp.2)

theorem split_parts_valid (P : Profile (Fin n)) {p : Parent n} (hp : ValidPart P p)
    (x : ℝ) (values : Fin n → ℝ) (hx : x ∈ Icc p.left p.right)
    (hv : ∀ i, values i = P.cumulative i x-P.cumulative i p.left) :
    ValidPart P (leftPart p x values) ∧ ValidPart P (rightPart p x values) := by
  refine ⟨⟨⟨hp.1.1,hx.1,hx.2.trans hp.1.2.2⟩,hv⟩,
    ⟨⟨hp.1.1.trans hx.1,hx.2,hp.1.2.2⟩,?_⟩⟩
  intro i
  change p.value i-values i = P.cumulative i p.right-P.cumulative i x
  rw [hp.2 i,hv i]
  ring

end EnvyFreeResearch.Full.Chores.OrderedUnion
