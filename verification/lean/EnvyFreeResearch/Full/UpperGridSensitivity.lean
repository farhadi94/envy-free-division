import EnvyFreeResearch.Full.UpperGridSensitivityTree

/-! The finite row sensitivity bound on arbitrary real cell-mass tables. -/

noncomputable section

open SimpleGraph
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridSensitivity

variable {Row Coord : Type*} [Fintype Coord]

def distance (x : Row → Coord → ℝ) (u v : Row) : ℝ := ∑ a, |x u a - x v a|

theorem distance_nonneg (x : Row → Coord → ℝ) (u v : Row) : 0 ≤ distance x u v :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem distance_symm (x : Row → Coord → ℝ) (u v : Row) : distance x u v = distance x v u := by
  apply Finset.sum_congr rfl
  intro a _
  exact abs_sub_comm _ _

theorem coord_le_distance (x : Row → Coord → ℝ) (u v : Row) (a : Coord) :
    |x u a - x v a| ≤ distance x u v := by
  exact Finset.single_le_sum (f := fun b => |x u b - x v b|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ a)

def edgeMagnitude (x : Row → Coord → ℝ) (a : Coord) : Sym2 Row → ℝ :=
  Sym2.lift ⟨fun u v => |x u a - x v a|, fun u v => abs_sub_comm (x u a) (x v a)⟩

def edgeLength (x : Row → Coord → ℝ) : Sym2 Row → ℝ :=
  Sym2.lift ⟨distance x, distance_symm x⟩

def edgeRatio (x : Row → Coord → ℝ) (a : Coord) (edge : Sym2 Row) : ℝ :=
  edgeMagnitude x a edge / edgeLength x edge

@[simp] theorem edgeMagnitude_mk (x : Row → Coord → ℝ) (a : Coord) (u v : Row) :
    edgeMagnitude x a s(u, v) = |x u a - x v a| := rfl

@[simp] theorem edgeLength_mk (x : Row → Coord → ℝ) (u v : Row) :
    edgeLength x s(u, v) = distance x u v := rfl

@[simp] theorem edgeRatio_mk (x : Row → Coord → ℝ) (a : Coord) (u v : Row) :
    edgeRatio x a s(u, v) = |x u a - x v a| / distance x u v := rfl

theorem edgeRatio_nonneg (x : Row → Coord → ℝ) (a : Coord) (e : Sym2 Row) :
    0 ≤ edgeRatio x a e := by
  cases e with
  | _ u v => exact div_nonneg (abs_nonneg _) (distance_nonneg x u v)

theorem edgeRatio_sum_le_one (x : Row → Coord → ℝ) (e : Sym2 Row) :
    ∑ a, edgeRatio x a e ≤ 1 := by
  cases e with
  | _ u v =>
    simp only [edgeRatio_mk, ← Finset.sum_div]
    change distance x u v / distance x u v ≤ 1
    by_cases h : distance x u v = 0
    · simp [h]
    · exact le_of_eq (div_self h)

/-- A zero-length edge has zero numerator. A positive shorter edge has the
larger normalized coordinate contribution. -/
theorem ratio_le_edgeRatio (x : Row → Coord → ℝ) (a : Coord) (u v : Row)
    (d : ℝ) (hd : 0 < d) (hshort : distance x u v ≤ d) :
    |x u a - x v a| / d ≤ edgeRatio x a s(u, v) := by
  by_cases hzero : distance x u v = 0
  · have hz : |x u a - x v a| = 0 :=
      le_antisymm (by simpa [hzero] using coord_le_distance x u v a) (abs_nonneg _)
    simp [edgeRatio_mk, hz]
  · exact div_le_div_of_nonneg_left (abs_nonneg _)
      (lt_of_le_of_ne (distance_nonneg x u v) (Ne.symm hzero)) hshort

/-- Telescope along the actual bounded-edge walk. -/
theorem walk_ratio_le (x : Row → Coord → ℝ) (a : Coord) (graph : SimpleGraph Row)
    (d : ℝ) (hd : 0 < d) (hshort : ∀ u v, graph.Adj u v → distance x u v ≤ d)
    {u v : Row} (p : graph.Walk u v) :
    |x u a - x v a| / d ≤ (p.edges.map (edgeRatio x a)).sum := by
  induction p with
  | nil => simp
  | @cons u v w hadj tail ih =>
    simp only [Walk.edges_cons, List.map_cons, List.sum_cons]
    calc
      |x u a - x w a| / d ≤ (|x u a - x v a| + |x v a - x w a|) / d :=
        div_le_div_of_nonneg_right (abs_sub_le _ _ _) hd.le
      _ = |x u a - x v a| / d + |x v a - x w a| / d := add_div _ _ _
      _ ≤ edgeRatio x a s(u, v) + (tail.edges.map (edgeRatio x a)).sum :=
        add_le_add (ratio_le_edgeRatio x a u v d hd (hshort u v hadj)) ih

variable [Fintype Row] [Nonempty Row]

/-- Maximum over all ordered row pairs; diagonal and duplicate-row quotients
are zero under the ordinary real division convention. -/
def sensitivity (x : Row → Coord → ℝ) (a : Coord) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun uv : Row × Row => |x uv.1 a - x uv.2 a| / distance x uv.1 uv.2)

theorem ratio_le_sensitivity (x : Row → Coord → ℝ) (a : Coord) (u v : Row) :
    |x u a - x v a| / distance x u v ≤ sensitivity x a := by
  exact Finset.le_sup' (fun uv : Row × Row =>
    |x uv.1 a - x uv.2 a| / distance x uv.1 uv.2) (Finset.mem_univ (u, v))

theorem sensitivity_nonneg (x : Row → Coord → ℝ) (a : Coord) : 0 ≤ sensitivity x a := by
  obtain ⟨u⟩ := ‹Nonempty Row›
  simpa using ratio_le_sensitivity x a u u

theorem ratio_le_tree_sum (x : Row → Coord → ℝ) (tree : SimpleGraph Row)
    (hpath : ∀ u v, (tree ⊓ threshold (distance x) (distance_symm x) (distance x u v)).Reachable u v)
    (a : Coord) (u v : Row) :
    |x u a - x v a| / distance x u v ≤ ∑ e ∈ tree.edgeFinset, edgeRatio x a e := by
  by_cases hz : distance x u v = 0
  · simp only [hz, div_zero]
    exact Finset.sum_nonneg (fun e _ => edgeRatio_nonneg x a e)
  · obtain ⟨p, hp⟩ := (hpath u v).exists_isPath
    have hbound := walk_ratio_le x a
      (tree ⊓ threshold (distance x) (distance_symm x) (distance x u v)) (distance x u v)
      (lt_of_le_of_ne (distance_nonneg x u v) (Ne.symm hz))
      (fun i j hij => hij.2.2) p
    apply hbound.trans
    rw [← List.sum_toFinset _ hp.isTrail.edges_nodup]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      apply SimpleGraph.mem_edgeFinset.mpr
      exact SimpleGraph.edgeSet_mono inf_le_left (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
    · intro e _ _
      exact edgeRatio_nonneg x a e

/-- The finite sensitivity total is at most one per spanning-tree edge,
namely `card Row - 1`. No positivity or normalization of row entries is needed. -/
theorem sum_sensitivity_le (x : Row → Coord → ℝ) :
    ∑ a, sensitivity x a ≤ (Fintype.card Row : ℝ) - 1 := by
  obtain ⟨tree, htree, hpath⟩ := exists_bottleneck_tree (distance x) (distance_symm x)
  have htotal : ∑ a, sensitivity x a ≤ (tree.edgeFinset.card : ℝ) := calc
    ∑ a, sensitivity x a ≤ ∑ a, ∑ e ∈ tree.edgeFinset, edgeRatio x a e := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sup'_le _ _ (fun uv _ => ratio_le_tree_sum x tree hpath a uv.1 uv.2)
    _ = ∑ e ∈ tree.edgeFinset, ∑ a, edgeRatio x a e := Finset.sum_comm
    _ ≤ ∑ _e ∈ tree.edgeFinset, (1 : ℝ) :=
      Finset.sum_le_sum (fun e _ => edgeRatio_sum_le_one x e)
    _ = (tree.edgeFinset.card : ℝ) := by simp
  have hcard := htree.card_edgeFinset
  have hcard' : (tree.edgeFinset.card : ℝ) + 1 = Fintype.card Row := by exact_mod_cast hcard
  linarith

end EnvyFreeResearch.Full.UpperGridSensitivity
