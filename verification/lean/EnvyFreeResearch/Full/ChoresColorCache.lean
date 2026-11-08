import EnvyFreeResearch.Full.ChoresQuantileGeometry
import EnvyFreeResearch.Full.ChoresUnionMeasures
import Mathlib.Data.List.FinRange

/-! Assigning recorded components to colors produces literal disjoint
finite-union pieces. Each color retains its ordered component cache, and
its value is exactly the corresponding sum of recorded component values. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ColorCache
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open scoped Classical BigOperators

variable {n : ℕ} {Color : Type*}

def parts (cache : List (Parent n)) (color : Fin cache.length → Color) (j : Color) : List (Parent n) :=
  ((List.finRange cache.length).filter (fun e => decide (color e=j))).map cache.get

theorem parts_sublist (cache : List (Parent n)) (color : Fin cache.length → Color) (j : Color) :
    List.Sublist (parts cache color j) cache := by
  have h := (List.filter_sublist (p := fun e => decide (color e=j))
    (l := List.finRange cache.length)).map cache.get
  simpa only [parts,← List.ofFn_eq_map,List.ofFn_get] using h

theorem parts_valid (P : Profile (Fin n)) (cache : List (Parent n)) (hv : Valid P cache)
    (color : Fin cache.length → Color) (j : Color) : Valid P (parts cache color j) := by
  apply (valid_iff_forall _ _).mpr
  intro p hp
  exact (valid_iff_forall _ _).mp hv p ((parts_sublist cache color j).subset hp)

theorem parts_ordered (cache : List (Parent n)) (ho : Ordered cache)
    (color : Fin cache.length → Color) (j : Color) : Ordered (parts cache color j) :=
  ho.sublist (parts_sublist cache color j)

theorem mem_material_parts (cache : List (Parent n)) (color : Fin cache.length → Color)
    (j : Color) (x : ℝ) : x ∈ material (parts cache color j) ↔
      ∃ e : Fin cache.length, color e=j ∧ x ∈ Ioc (cache.get e).left (cache.get e).right := by
  constructor
  · intro hx
    obtain ⟨p,hp,hx⟩ := (mem_material_iff _ _).mp hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact ⟨e,of_decide_eq_true (List.mem_filter.mp he).2,hx⟩
  · rintro ⟨e,he,hx⟩
    apply (mem_material_iff _ _).mpr
    refine ⟨cache.get e,?_,hx⟩
    exact List.mem_map.mpr ⟨e,List.mem_filter.mpr ⟨List.mem_finRange e,by simpa only [decide_eq_true_eq]⟩,rfl⟩

theorem parts_cover (cache : List (Parent n)) (color : Fin cache.length → Color) :
    (⋃ j, material (parts cache color j))=material cache := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    obtain ⟨e,_,he⟩ := (mem_material_parts cache color j x).mp hj
    exact (mem_material_iff _ _).mpr ⟨cache.get e,List.get_mem _ _,he⟩
  · intro hx
    obtain ⟨p,hp,hx⟩ := (mem_material_iff _ _).mp hx
    obtain ⟨e,rfl⟩ := List.mem_iff_get.mp hp
    exact mem_iUnion.mpr ⟨color e,(mem_material_parts cache color (color e) x).mpr ⟨e,rfl,hx⟩⟩

theorem parts_disjoint (cache : List (Parent n)) (ho : Ordered cache)
    (color : Fin cache.length → Color) : Pairwise (fun j k =>
      Disjoint (material (parts cache color j)) (material (parts cache color k))) := by
  intro j k hjk
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨e,he,hxe⟩ := (mem_material_parts cache color j x).mp hx
  obtain ⟨f,hf,hxf⟩ := (mem_material_parts cache color k x).mp hy
  have hne : e ≠ f := fun h => hjk (he.symm.trans (h ▸ hf))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hbefore := List.pairwise_iff_get.mp ho e f hlt
    exact not_lt_of_ge (hxe.2.trans hbefore) hxf.1
  · have hbefore := List.pairwise_iff_get.mp ho f e hgt
    exact not_lt_of_ge (hxf.2.trans hbefore) hxe.1

theorem cachedValue_eq_sum (cache : List (Parent n)) (i : Fin n) :
    cachedValue cache i = (cache.map (fun p => p.value i)).sum := by
  induction cache with
  | nil => rfl
  | cons p cache ih => simp only [cachedValue,List.map_cons,List.sum_cons,ih]

theorem sum_filter_map {α : Type*} (xs : List α) (keep : α → Bool) (f : α → ℝ) :
    ((xs.filter keep).map f).sum=(xs.map (fun a => if keep a then f a else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : keep a <;> simp [List.filter_cons,h,ih]

theorem parts_value (cache : List (Parent n)) (color : Fin cache.length → Color)
    (j : Color) (i : Fin n) : cachedValue (parts cache color j) i =
      ∑ e : Fin cache.length, if color e=j then (cache.get e).value i else 0 := by
  rw [cachedValue_eq_sum,parts,List.map_map,sum_filter_map]
  simp only [Function.comp_apply,decide_eq_true_eq,← List.ofFn_eq_map,List.sum_ofFn]

theorem parts_measure (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (cache : List (Parent n)) (hv : Valid (measureProfile cost) cache) (ho : Ordered cache)
    (color : Fin cache.length → Color) (j : Color) (i : Fin n) :
    (cost i).real (material (parts cache color j)) =
      ∑ e : Fin cache.length, if color e=j then (cache.get e).value i else 0 := by
  rw [material_value cost _ (parts_valid _ cache hv color j) (parts_ordered cache ho color j),parts_value]

end EnvyFreeResearch.Full.Chores.ColorCache
