import EnvyFreeResearch.Full.ChoresEqualizerTable
import Mathlib.Data.List.Sort

/-! Original atoms between recorded equalizer marks. An atom can cross
several old physical components: its domain is the original piece intersected
with one endpoint interval. Its cost is computed from recorded prefix values,
not by pretending that the entire endpoint interval has the masked cost. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OriginalAtoms
open Set MeasureTheory OrderedUnion InitialPartition Equalizers
open scoped Classical

structure Mark (n : ℕ) where
  point : ℝ
  values : Fin n → ℝ

structure Atom (n : ℕ) where
  left : ℝ
  right : ℝ
  values : Fin n → ℝ

def Atom.domain {n : ℕ} (P : Set ℝ) (atom : Atom n) : Set ℝ := P ∩ Ioc atom.left atom.right

def fromMarks {n : ℕ} (previous : Mark n) : List (Mark n) → List (Atom n)
  | [] => []
  | current::rest => ⟨previous.point,current.point,fun i => current.values i-previous.values i⟩ ::
      fromMarks current rest

theorem fromMarks_length {n : ℕ} (previous : Mark n) (marks : List (Mark n)) :
    (fromMarks previous marks).length = marks.length := by
  induction marks generalizing previous with
  | nil => rfl
  | cons current rest ih => simp only [fromMarks,List.length_cons,ih]

def beforeMark {n : ℕ} (a b : Mark n) : Prop := a.point ≤ b.point
instance {n : ℕ} : Std.Total (@beforeMark n) := ⟨fun a b => le_total a.point b.point⟩
instance {n : ℕ} : IsTrans (Mark n) beforeMark := ⟨fun _ _ _ => le_trans⟩

def sortedMarks {n : ℕ} (marks : List (Mark n)) : List (Mark n) :=
  marks.mergeSort (fun a b => decide (beforeMark a b))

theorem sorted_marks_order {n : ℕ} (marks : List (Mark n)) :
    (sortedMarks marks).Pairwise beforeMark := List.pairwise_mergeSort' _ _

theorem sorted_marks_perm {n : ℕ} (marks : List (Mark n)) : (sortedMarks marks).Perm marks :=
  List.mergeSort_perm _ _

def Mark.Sound {n : ℕ} (cost : Fin n → Measure ℝ) (P : Set ℝ) (r : Mark n) : Prop :=
  r.point ∈ Icc (0 : ℝ) 1 ∧ ∀ i, r.values i = (cost i).real (P ∩ Iic r.point)

def Atom.Sound {n : ℕ} (cost : Fin n → Measure ℝ) (P : Set ℝ) (a : Atom n) : Prop :=
  (0 ≤ a.left ∧ a.left ≤ a.right ∧ a.right ≤ 1) ∧
    ∀ i, a.values i = (cost i).real (a.domain P)

theorem prefix_difference (μ : Measure ℝ) [IsFiniteMeasure μ]
    (P : Set ℝ) (hP : MeasurableSet P) {a b : ℝ} (hab : a ≤ b) :
    μ.real (P ∩ Iic b)-μ.real (P ∩ Iic a) = μ.real (P ∩ Ioc a b) := by
  have hsub : P ∩ Iic a ⊆ P ∩ Iic b := inter_subset_inter_right P (Iic_subset_Iic.mpr hab)
  have hset : (P ∩ Iic b) \ (P ∩ Iic a) = P ∩ Ioc a b := by
    ext x
    simp only [mem_sdiff,mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · rintro ⟨⟨hPx,hxb⟩,hn⟩
      exact ⟨hPx,lt_of_not_ge (fun hxa => hn ⟨hPx,hxa⟩),hxb⟩
    · rintro ⟨hPx,hax,hxb⟩
      exact ⟨⟨hPx,hxb⟩,fun h => not_lt_of_ge h.2 hax⟩
  rw [← measureReal_sdiff hsub (hP.inter measurableSet_Iic),hset]

theorem fromMarks_sound {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] (P : Set ℝ) (hP : MeasurableSet P)
    (previous : Mark n) (marks : List (Mark n)) (hprevious : previous.Sound cost P)
    (hmarks : ∀ r ∈ marks, r.Sound cost P) (horder : marks.Pairwise beforeMark)
    (hlower : ∀ r ∈ marks, previous.point ≤ r.point) :
    ∀ atom ∈ fromMarks previous marks, atom.Sound cost P := by
  induction marks generalizing previous with
  | nil => simp [fromMarks]
  | cons current rest ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp horder
    have hc := hmarks current List.mem_cons_self
    intro atom hm
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨⟨hprevious.1.1,hlower current List.mem_cons_self,hc.1.2⟩,?_⟩
      intro i
      change current.values i-previous.values i = _
      rw [hc.2 i,hprevious.2 i]
      exact prefix_difference (cost i) P hP (hlower current List.mem_cons_self)
    · exact ih current hc (fun r hr => hmarks r (List.mem_cons_of_mem current hr)) hrest hfront atom hm

def lastPoint {n : ℕ} (previous : Mark n) : List (Mark n) → ℝ
  | [] => previous.point
  | current::rest => lastPoint current rest

theorem le_lastPoint {n : ℕ} (previous : Mark n) (marks : List (Mark n))
    (horder : marks.Pairwise beforeMark) (hlower : ∀ r ∈ marks, previous.point ≤ r.point) :
    previous.point ≤ lastPoint previous marks := by
  induction marks generalizing previous with
  | nil => exact le_rfl
  | cons current rest ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp horder
    exact (hlower current List.mem_cons_self).trans (ih current hrest hfront)

theorem mem_le_lastPoint {n : ℕ} (previous : Mark n) (marks : List (Mark n))
    (horder : marks.Pairwise beforeMark) (r : Mark n) (hr : r ∈ marks) :
    r.point ≤ lastPoint previous marks := by
  induction marks generalizing previous with
  | nil => cases hr
  | cons current rest ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp horder
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_lastPoint r rest hrest hfront
    · exact ih current hrest hr

theorem atom_left_ge {n : ℕ} (previous : Mark n) (marks : List (Mark n))
    (horder : marks.Pairwise beforeMark) (hlower : ∀ r ∈ marks, previous.point ≤ r.point)
    (atom : Atom n) (ha : atom ∈ fromMarks previous marks) : previous.point ≤ atom.left := by
  induction marks generalizing previous with
  | nil => cases ha
  | cons current rest ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp horder
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_rfl
    · exact (hlower current List.mem_cons_self).trans (ih current hrest hfront ha)

theorem fromMarks_disjoint {n : ℕ} (P : Set ℝ) (previous : Mark n) (marks : List (Mark n))
    (horder : marks.Pairwise beforeMark) (hlower : ∀ r ∈ marks, previous.point ≤ r.point) :
    (fromMarks previous marks).Pairwise (fun a b => Disjoint (a.domain P) (b.domain P)) := by
  induction marks generalizing previous with
  | nil => exact List.Pairwise.nil
  | cons current rest ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp horder
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih current hrest hfront⟩
    intro atom ha
    have hleft := atom_left_ge current rest hrest hfront atom ha
    apply disjoint_left.mpr
    intro x hx hy
    exact not_lt_of_ge (hx.2.2.trans hleft) hy.2.1

def atomMaterial {n : ℕ} (P : Set ℝ) : List (Atom n) → Set ℝ
  | [] => ∅
  | atom::rest => atom.domain P ∪ atomMaterial P rest

theorem fromMarks_cover {n : ℕ} (P : Set ℝ) (previous : Mark n) (marks : List (Mark n))
    (horder : marks.Pairwise beforeMark) (hlower : ∀ r ∈ marks, previous.point ≤ r.point) :
    atomMaterial P (fromMarks previous marks) = P ∩ Ioc previous.point (lastPoint previous marks) := by
  induction marks generalizing previous with
  | nil => simp [fromMarks,atomMaterial,lastPoint]
  | cons current rest ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp horder
    simp only [fromMarks,atomMaterial,Atom.domain,lastPoint]
    rw [ih current hrest hfront,← inter_union_distrib_left,
      Ioc_union_Ioc_eq_Ioc (hlower current List.mem_cons_self) (le_lastPoint current rest hrest hfront)]

end EnvyFreeResearch.Full.Chores.OriginalAtoms
