import EnvyFreeResearch.Full.ChoresOuterInitial
import EnvyFreeResearch.Full.ChoresOuterFilterSound
import EnvyFreeResearch.Full.ChoresProtectedPivot

/-! Finite entrance selection reads only the recorded original gaps and
residue values. Unselected original roots remain in the closed pool. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot
open scoped Classical

structure EntranceChoice (n J : ℕ) where
  pivot : Fin n
  roots : Finset (Fin J)

def EntranceChoice.Admissible {n J : ℕ} (a : EntranceChoice n J)
    (original : Fin J → Snapshot.Output n) (c : Fin n)
    (r : Fin n → ℝ) (H : ℝ) (S : ℕ) : Prop :=
  a.pivot ≠ c ∧ a.roots.card=S ∧
    ∀ s ∈ a.roots, c ∉ ProtectedPivot.eligible (original s) H r a.pivot

def entranceChoice {n J : ℕ} (original : Fin J → Snapshot.Output n)
    (c : Fin n) (r : Fin n → ℝ) (H : ℝ) (S : ℕ) : Option (EntranceChoice n J) :=
  if h : ∃ a : EntranceChoice n J, a.Admissible original c r H S then
    some h.choose else none

def EntranceChoice.data {n J : ℕ} (a : EntranceChoice n J)
    (original : Fin J → Snapshot.Output n) : Data n (Fin J) :=
  (initialData original).filter a.roots.toList

variable {n : ℕ} (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U R : Set ℝ} (c : Fin n) (xs : List (Snapshot.Output n))
  (cache : List (Parent n)) (chain : Snapshot.Chain cost c U xs cache)

include chain

theorem entrance_good (a : EntranceChoice n xs.length) (H : ℝ) (hH : 0 < H) :
    (a.data xs.get).Good xs.get cost (fun i => (cost i).real R) H := by
  have hs : ∀ s, ∃ domain, Snapshot.Sound cost domain c (xs.get s) :=
    fun s => chain.member_sound _ (List.get_mem _ s)
  exact filter_good (initialData xs.get) xs.get cost _ H
    (initial_good cost xs.get c hs _ H (fun i => measureReal_nonneg) hH)
    a.roots.toList (Finset.nodup_toList _)

theorem entrance_selection (hn : 2 ≤ n) (hR : R ⊆ material cache)
    (hr : 0 < (cost c).real R) (H : ℝ) (hH : (n-1 : ℕ) < H)
    (S : ℕ) (hcount : (S-1)*(n-1) < xs.length) :
    ∃ a, entranceChoice xs.get c (fun i => (cost i).real R) H S=some a ∧
      a.Admissible xs.get c (fun i => (cost i).real R) H S := by
  have hex : ∃ a : EntranceChoice n xs.length,
      a.Admissible xs.get c (fun i => (cost i).real R) H S := by
    obtain ⟨p,hp,selected,hsize,homit⟩ :=
      ProtectedPivot.common_omitted_exact hn cost c xs cache chain hR hr H hH S hcount
    exact ⟨⟨p,selected⟩,hp,hsize,homit⟩
  refine ⟨hex.choose,?_,hex.choose_spec⟩
  simp only [entranceChoice,dif_pos hex]

omit chain in
theorem entrance_size (a : EntranceChoice n xs.length) (H : ℝ) (S : ℕ)
    (ha : a.Admissible xs.get c (fun i => (cost i).real R) H S) :
    (a.data xs.get).size=S := by
  change a.roots.toList.length=S
  simpa only [Finset.length_toList] using ha.2.1

omit chain in
theorem entrance_omission (a : EntranceChoice n xs.length) (H : ℝ) (S : ℕ)
    (ha : a.Admissible xs.get c (fun i => (cost i).real R) H S)
    (s : Fin (a.data xs.get).size) :
    c ∉ ProtectedPivot.eligible (xs.get ((a.data xs.get).source s)) H
      (fun i => (cost i).real R) a.pivot := by
  exact ha.2.2 (a.roots.toList.get s) (Finset.mem_toList.mp (List.get_mem _ s))

end EnvyFreeResearch.Full.Chores.Outer
