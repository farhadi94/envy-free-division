import EnvyFreeResearch.Full.ChoresUnionQuery
import Mathlib.Data.List.Sort

/-! Pure cached assembly of disjoint finite-union pieces. Reordering their
recorded components makes another legal query domain without new oracle
calls. Only empty intervals are removed; nonempty zero-cost material stays. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ}

def componentsDisjoint (ps : List (Parent n)) : Prop :=
  ps.Pairwise (fun p q => Disjoint (Ioc p.left p.right) (Ioc q.left q.right))

def beforeComponent (p q : Parent n) : Prop := p.left ≤ q.left
instance : Std.Total (@beforeComponent n) := ⟨fun p q => le_total p.left q.left⟩
instance : IsTrans (Parent n) beforeComponent := ⟨fun _ _ _ => le_trans⟩

def positiveComponents (ps : List (Parent n)) : List (Parent n) :=
  ps.filter (fun p => decide (p.left < p.right))

def assemble (ps : List (Parent n)) : List (Parent n) :=
  (positiveComponents ps).mergeSort (fun p q => decide (beforeComponent p q))

theorem material_perm {ps qs : List (Parent n)} (hp : ps.Perm qs) : material ps=material qs := by
  ext x
  simp only [mem_material_iff]
  exact exists_congr (fun p => and_congr hp.mem_iff Iff.rfl)

theorem cachedValue_sum (ps : List (Parent n)) (i : Fin n) :
    OrderedUnion.cachedValue ps i=(ps.map (fun p => p.value i)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [OrderedUnion.cachedValue,ih]

theorem cachedValue_perm {ps qs : List (Parent n)} (hp : ps.Perm qs) (i : Fin n) :
    OrderedUnion.cachedValue ps i=OrderedUnion.cachedValue qs i := by
  rw [cachedValue_sum,cachedValue_sum]
  exact (hp.map _).sum_eq

theorem positive_material (ps : List (Parent n)) : material (positiveComponents ps)=material ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p.left < p.right
    · simpa only [positiveComponents,List.filter_cons,decide_true,h,if_true,material] using
        congrArg (fun s => Ioc p.left p.right ∪ s) ih
    · have hempty : Ioc p.left p.right=∅ := Ioc_eq_empty_of_le (le_of_not_gt h)
      simpa [positiveComponents,h,material,hempty] using ih

theorem positive_value (P : Profile (Fin n)) (ps : List (Parent n)) (hp : Valid P ps) (i : Fin n) :
    OrderedUnion.cachedValue (positiveComponents ps) i=OrderedUnion.cachedValue ps i := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p.left < p.right
    · simpa [positiveComponents,h,OrderedUnion.cachedValue] using congrArg (fun x => p.value i+x) (ih hp.2)
    · have heq : p.left=p.right := le_antisymm hp.1.1.2.1 (le_of_not_gt h)
      have hz : p.value i=0 := by rw [hp.1.2 i,heq,sub_self]
      simpa [positiveComponents,h,OrderedUnion.cachedValue,hz] using ih hp.2

theorem assemble_material (ps : List (Parent n)) : material (assemble ps)=material ps :=
  (material_perm (List.mergeSort_perm _ _)).trans (positive_material ps)

theorem assemble_valid (P : Profile (Fin n)) {ps : List (Parent n)} (hp : Valid P ps) :
    Valid P (assemble ps) := by
  apply (valid_iff_forall _ _).mpr
  intro p h
  have hf : p ∈ positiveComponents ps := (List.mergeSort_perm _ _).mem_iff.mp h
  exact (valid_iff_forall _ _).mp hp p (List.mem_filter.mp hf).1

theorem assemble_value (P : Profile (Fin n)) {ps : List (Parent n)} (hp : Valid P ps) (i : Fin n) :
    OrderedUnion.cachedValue (assemble ps) i=OrderedUnion.cachedValue ps i :=
  (cachedValue_perm (List.mergeSort_perm _ _) i).trans (positive_value P ps hp i)

theorem assemble_ordered {ps : List (Parent n)} (hd : componentsDisjoint ps) : Ordered (assemble ps) := by
  have hperm : (assemble ps).Perm (positiveComponents ps) := List.mergeSort_perm _ _
  have hds : componentsDisjoint (assemble ps) :=
    hperm.symm.pairwise (hd.filter _) (fun h => h.symm)
  have hs : (assemble ps).Pairwise beforeComponent := List.pairwise_mergeSort' _ _
  apply (hs.and hds).imp_of_mem
  intro p q hp hq h
  have hp' : p.left < p.right := of_decide_eq_true (List.mem_filter.mp (hperm.mem_iff.mp hp)).2
  have hq' : q.left < q.right := of_decide_eq_true (List.mem_filter.mp (hperm.mem_iff.mp hq)).2
  by_contra hn
  have hxq : q.left < min p.right q.right := lt_min (lt_of_not_ge hn) hq'
  exact Set.disjoint_left.mp h.2
    ⟨h.1.trans_lt hxq,min_le_left _ _⟩ ⟨hxq,min_le_right _ _⟩

theorem ordered_components_disjoint {ps : List (Parent n)} (ho : Ordered ps) : componentsDisjoint ps :=
  ho.imp (fun h => Ioc_disjoint_Ioc_of_le h)

theorem material_append (ps qs : List (Parent n)) : material (ps++qs)=material ps ∪ material qs := by
  induction ps with
  | nil => simp [material]
  | cons p ps ih => simp only [List.cons_append,material,ih,union_assoc]

theorem valid_append (P : Profile (Fin n)) (ps qs : List (Parent n)) :
    Valid P (ps++qs) ↔ Valid P ps ∧ Valid P qs := by
  simp only [valid_iff_forall,List.mem_append,or_imp,forall_and]

theorem append_components_disjoint {ps qs : List (Parent n)}
    (hp : componentsDisjoint ps) (hq : componentsDisjoint qs)
    (hd : Disjoint (material ps) (material qs)) : componentsDisjoint (ps++qs) := by
  apply List.pairwise_append.mpr
  refine ⟨hp,hq,?_⟩
  intro p hp q hq
  exact hd.mono (fun x hx => (mem_material_iff _ _).mpr ⟨p,hp,hx⟩)
    (fun x hx => (mem_material_iff _ _).mpr ⟨q,hq,hx⟩)

theorem assemble_join (P : Profile (Fin n)) (ps qs : List (Parent n))
    (hp : Valid P ps) (hq : Valid P qs) (hop : Ordered ps) (hoq : Ordered qs)
    (hd : Disjoint (material ps) (material qs)) :
    Valid P (assemble (ps++qs)) ∧ Ordered (assemble (ps++qs)) ∧
      material (assemble (ps++qs))=material ps ∪ material qs := by
  exact ⟨assemble_valid P ((valid_append P ps qs).mpr ⟨hp,hq⟩),
    assemble_ordered (append_components_disjoint (ordered_components_disjoint hop)
      (ordered_components_disjoint hoq) hd),(assemble_material _).trans (material_append ps qs)⟩

end EnvyFreeResearch.Full.Chores.Augment
