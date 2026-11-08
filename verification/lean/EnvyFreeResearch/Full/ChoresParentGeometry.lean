import EnvyFreeResearch.Full.ChoresInitialPartition

/-!
# Literal geometry of the recorded parent partition

The queried parent list is adjacent in physical space, covers the original
half-open interval exactly and has disjoint members. Indexing it by the
population preserves all these facts, including zero-length parents.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.InitialPartition

open Set IntervalOracle

theorem Chain.member_bounds {n : ℕ} (P : Profile (Fin n)) (parents : List (Parent n))
    (a b : ℝ) (hchain : Chain P a b parents) :
    ∀ p ∈ parents, a ≤ p.left ∧ p.left ≤ p.right ∧ p.right ≤ b := by
  induction parents generalizing a with
  | nil => simp
  | cons q rest ih =>
    obtain ⟨hq, haq, hqb, _, htail⟩ := hchain
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hq.ge, hq ▸ haq, hqb⟩
    · obtain ⟨hl, hm, hr⟩ := ih q.right htail p hp
      exact ⟨haq.trans hl, hm, hr⟩

theorem Chain.member_value {n : ℕ} (P : Profile (Fin n)) (parents : List (Parent n))
    (a b : ℝ) (hchain : Chain P a b parents) :
    ∀ p ∈ parents, ∀ i, p.value i = P.cumulative i p.right - P.cumulative i p.left := by
  induction parents generalizing a with
  | nil => simp
  | cons q rest ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hchain.2.2.2.1
    · exact ih q.right hchain.2.2.2.2 p hp

theorem Chain.pairwise_order {n : ℕ} (P : Profile (Fin n)) (parents : List (Parent n))
    (a b : ℝ) (hchain : Chain P a b parents) :
    List.Pairwise (fun p q : Parent n => p.right ≤ q.left) parents := by
  induction parents generalizing a with
  | nil => simp
  | cons p rest ih =>
    apply List.pairwise_cons.mpr
    exact ⟨fun q hq => (hchain.2.2.2.2.member_bounds P rest p.right b q hq).1,
      ih p.right hchain.2.2.2.2⟩

theorem Chain.union_eq {n : ℕ} (P : Profile (Fin n)) (parents : List (Parent n))
    (a b : ℝ) (hchain : Chain P a b parents) :
    (⋃ p ∈ parents, Ioc p.left p.right) = Ioc a b := by
  induction parents generalizing a with
  | nil => simpa only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, Ioc_self] using
      (show (∅ : Set ℝ) = Ioc a b from by rw [hchain]; simp)
  | cons p rest ih =>
    simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
    rw [ih p.right hchain.2.2.2.2, hchain.1]
    exact Ioc_union_Ioc_eq_Ioc hchain.2.1 hchain.2.2.1

def indexed {n : ℕ} (parents : List (Parent n)) (hlen : parents.length = n) (p : Fin n) : Parent n :=
  parents.get (Fin.cast hlen.symm p)

lemma indexed_mem {n : ℕ} (parents : List (Parent n)) (hlen : parents.length = n) (p : Fin n) :
    indexed parents hlen p ∈ parents := List.get_mem _ _

lemma exists_indexed {n : ℕ} (parents : List (Parent n)) (hlen : parents.length = n)
    (p : Parent n) (hp : p ∈ parents) : ∃ i : Fin n, indexed parents hlen i = p := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  refine ⟨Fin.cast hlen i, ?_⟩
  simpa only [indexed, Fin.cast_cast, Fin.cast_eq_self] using hi

theorem indexed_disjoint {n : ℕ} (P : Profile (Fin n)) (parents : List (Parent n))
    (a b : ℝ) (hchain : Chain P a b parents) (hlen : parents.length = n) :
    Pairwise (fun p q : Fin n => Disjoint (Ioc (indexed parents hlen p).left (indexed parents hlen p).right)
      (Ioc (indexed parents hlen q).left (indexed parents hlen q).right)) := by
  intro p q hpq
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · exact Ioc_disjoint_Ioc_of_le ((hchain.pairwise_order P parents a b).rel_get_of_lt
      (show Fin.cast hlen.symm p < Fin.cast hlen.symm q from hpq))
  · exact (Ioc_disjoint_Ioc_of_le ((hchain.pairwise_order P parents a b).rel_get_of_lt
      (show Fin.cast hlen.symm q < Fin.cast hlen.symm p from hqp))).symm

theorem indexed_union {n : ℕ} (P : Profile (Fin n)) (parents : List (Parent n))
    (a b : ℝ) (hchain : Chain P a b parents) (hlen : parents.length = n) :
    (⋃ p : Fin n, Ioc (indexed parents hlen p).left (indexed parents hlen p).right) = Ioc a b := by
  rw [← hchain.union_eq P parents a b]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨indexed parents hlen p, indexed_mem parents hlen p, hp⟩
  · rintro ⟨p, hp, hxp⟩
    obtain ⟨i, rfl⟩ := exists_indexed parents hlen p hp
    exact ⟨i, hxp⟩

end EnvyFreeResearch.Full.Chores.InitialPartition
