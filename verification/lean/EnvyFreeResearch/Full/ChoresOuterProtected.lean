import EnvyFreeResearch.Full.ChoresOuterInitial
import EnvyFreeResearch.Full.ChoresOuterOutside
import EnvyFreeResearch.Full.ChoresProtectedPivot

/-! The protected original label persists through actual scheduler updates. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler Components
open scoped Classical
variable {n J : ℕ} {RootId : Type*}

structure Protected (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (c pivot : Fin n) (r : Fin n → ℝ) (H : ℝ) : Prop where
  representative : data.pending.partition.representative pivot = pivot
  omitted : ∀ s, c ∉ ProtectedPivot.eligible (original (data.source s)) H r pivot

namespace Protected
variable {data next : Data n RootId} {original : RootId → Snapshot.Output n}
    {c pivot : Fin n} {r : Fin n → ℝ} {H : ℝ}

theorem initial (original : Fin J → Snapshot.Output n) (c pivot : Fin n)
    (r : Fin n → ℝ) (H : ℝ)
    (h : ∀ s, c ∉ ProtectedPivot.eligible (original s) H r pivot) :
    Protected (initialData original) original c pivot r H := ⟨rfl,h⟩

theorem filter (h : Protected data original c pivot r H) (roots : List (Fin data.size)) :
    Protected (data.filter roots) original c pivot r H :=
  ⟨h.representative, fun s => h.omitted (roots.get s)⟩

theorem reveal (h : Protected data original c pivot r H) (p : Fin n)
    (hp : p ∈ data.pending.partition.labels) (q : Proposal (Fin data.size) (Fin n))
    (hq : q.Valid data.pending.partition p) :
    Protected (data.reveal p hp q hq) original c pivot r H :=
  ⟨h.representative,h.omitted⟩

theorem full_component_label (h : Protected data original c pivot r H) (p : Fin n)
    (hfull : data.pending.partition.component p=Finset.univ) : p=pivot := by
  have hm : pivot ∈ data.pending.partition.component p := by rw [hfull]; exact Finset.mem_univ _
  have he := (Partition.mem_component _ _ _).mp hm
  exact he.symm.trans h.representative

theorem terminal_entrance (h : Protected data original c pivot r H) (p : Fin n) (s : Fin data.size) :
    data.pending.partition.component p ≠ Finset.univ ∨
      c ∉ ProtectedPivot.eligible (original (data.source s)) H r p := by
  by_cases hf : data.pending.partition.component p=Finset.univ
  · right
    rw [h.full_component_label p hf]
    exact h.omitted s
  · exact Or.inl hf

/-- Only literal source/partition identities are needed at batch commit. -/
theorem merge_restrict (h : Protected data original c pivot r H)
    (selected : Finset (Fin n)) (hsub : selected ⊆ data.pending.partition.labels)
    (hne : selected.Nonempty) (includeRoot : Fin next.size → Fin data.size)
    (hsource : next.source=data.source ∘ includeRoot)
    (hpartition : next.pending.partition=data.pending.partition.merge selected
      (Partition.keepLabel pivot selected hne) hsub (Partition.keepLabel_mem _ _ _)) :
    Protected next original c pivot r H := by
  constructor
  · rw [hpartition]
    exact Partition.merge_protected _ selected hsub hne pivot h.representative
  · intro s
    rw [hsource]
    exact h.omitted (includeRoot s)

end Protected
end EnvyFreeResearch.Full.Chores.Outer
