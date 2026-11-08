import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# A finite bottleneck spanning tree

Ascending finite distance thresholds extend an acyclic forest to span each
threshold graph. This is the Kruskal form of the minimum-spanning-tree
bottleneck property, with no assumed tree or assumed path bound.
-/

noncomputable section

open SimpleGraph
open scoped Classical

namespace EnvyFreeResearch.Full.UpperGridSensitivity

variable {Vertex : Type*}

def threshold (weight : Vertex → Vertex → ℝ) (hsymm : ∀ u v, weight u v = weight v u)
    (r : ℝ) : SimpleGraph Vertex where
  Adj u v := u ≠ v ∧ weight u v ≤ r
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, by simpa only [hsymm] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

/-- A single forest spans every processed threshold at that threshold. -/
theorem exists_threshold_forest (weight : Vertex → Vertex → ℝ)
    (hsymm : ∀ u v, weight u v = weight v u) (levels : Finset ℝ) :
    ∃ forest : SimpleGraph Vertex, forest.IsAcyclic ∧
      (∀ u v, forest.Adj u v → ∃ r ∈ levels, weight u v ≤ r) ∧
      ∀ r ∈ levels, ∀ u v, (threshold weight hsymm r).Reachable u v →
        (forest ⊓ threshold weight hsymm r).Reachable u v := by
  induction levels using Finset.induction_on_max with
  | empty =>
    refine ⟨⊥, isAcyclic_bot, ?_, ?_⟩
    · intro u v h; cases h
    · simp
  | insert r levels hmax ih =>
    obtain ⟨forest, hacyclic, hweight, hreach⟩ := ih
    have hle : forest ≤ threshold weight hsymm r := by
      intro u v huv
      obtain ⟨s, hs, hws⟩ := hweight u v huv
      exact ⟨huv.ne, hws.trans (hmax s hs).le⟩
    obtain ⟨next, hforest, hnext, hacyclic', hreach'⟩ :=
      (threshold weight hsymm r).exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hle hacyclic
    refine ⟨next, hacyclic', ?_, ?_⟩
    · intro u v huv
      exact ⟨r, Finset.mem_insert_self _ _, (hnext huv).2⟩
    · intro s hs u v huv
      rcases Finset.mem_insert.mp hs with rfl | hs
      · rw [inf_eq_left.mpr hnext, hreach']
        exact huv
      · exact (hreach s hs u v huv).mono (inf_le_inf hforest le_rfl)

/-- Every finite symmetric weight table has a spanning tree connecting each
pair by a path consisting only of edges at most that pair's own weight.
Zero weights and coincident rows require no quotient construction. -/
theorem exists_bottleneck_tree [Fintype Vertex] [Nonempty Vertex]
    (weight : Vertex → Vertex → ℝ) (hsymm : ∀ u v, weight u v = weight v u) :
    ∃ tree : SimpleGraph Vertex, tree.IsTree ∧
      ∀ u v, (tree ⊓ threshold weight hsymm (weight u v)).Reachable u v := by
  let levels := Finset.univ.image (fun uv : Vertex × Vertex => weight uv.1 uv.2)
  obtain ⟨tree, hacyclic, _, hreach⟩ := exists_threshold_forest weight hsymm levels
  have hpair (u v : Vertex) :
      (tree ⊓ threshold weight hsymm (weight u v)).Reachable u v := by
    by_cases huv : u = v
    · subst v; exact .refl _
    · exact hreach _ (Finset.mem_image.mpr ⟨(u, v), Finset.mem_univ _, rfl⟩) u v
        (SimpleGraph.Adj.reachable ⟨huv, le_rfl⟩)
  refine ⟨tree, ⟨?_, hacyclic⟩, hpair⟩
  exact ⟨fun u v => (hpair u v).mono inf_le_left⟩

end EnvyFreeResearch.Full.UpperGridSensitivity
