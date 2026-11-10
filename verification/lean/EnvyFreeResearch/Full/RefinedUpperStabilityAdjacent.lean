import EnvyFreeResearch.Full.RefinedUpperStabilityIntervalEdit
import EnvyFreeResearch.Full.RefinedUpperPeelingPhysicalLabels
import EnvyFreeResearch.Full.UpperGridInterpolationSortDelete

/-! The physical cell list of an actual sorted grid, and its local deletion. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperSortedGrid
open scoped Classical

/-- Consecutive physical intervals, retaining duplicate zero intervals. -/
def edges {Point : Type*} : List Point → List (Point × Point)
  | [] => []
  | [_] => []
  | a::b::rest => (a,b)::edges (b::rest)

lemma edges_ofFn {Point : Type*} {m : ℕ} (points : Fin (m+1) → Point) :
    edges (List.ofFn points) = List.ofFn (fun i : Fin m => (points i.castSucc,points i.succ)) := by
  induction m with
  | zero => simp [List.ofFn_succ,edges]
  | succ m ih =>
    rw [List.ofFn_succ]
    rw [List.ofFn_succ]
    simp only [edges]
    rw [List.ofFn_succ]
    congr 1
    simpa only [List.ofFn_succ,Fin.castSucc_succ] using ih (fun i => points i.succ)

lemma edges_append_cons {Point : Type*} (before : List Point) (a : Point) (after : List Point) :
    edges (before++a::after) = edges (before++[a])++edges (a::after) := by
  induction before with
  | nil => simp [edges]
  | cons b bs ih =>
    cases bs with
    | nil => cases after <;> simp [edges]
    | cons c cs => simpa [edges] using congrArg (List.cons (b,c)) ih

lemma edges_split {Point : Type*} (before after : List Point) (a t b : Point) :
    edges (before++a::t::b::after) =
      edges (before++[a])++[(a,t),(t,b)]++edges (b::after) := by
  rw [edges_append_cons]
  simp [edges,List.append_assoc]

lemma edges_merge {Point : Type*} (before after : List Point) (a b : Point) :
    edges (before++a::b::after) = edges (before++[a])++[(a,b)]++edges (b::after) := by
  rw [edges_append_cons]
  simp [edges,List.append_assoc]

lemma edges_mem_endpoints {Point : Type*} (points : List Point) (c : Point × Point)
    (hc : c ∈ edges points) : c.1 ∈ points ∧ c.2 ∈ points := by
  induction points with
  | nil => simp [edges] at hc
  | cons a ps ih =>
    cases ps with
    | nil => simp [edges] at hc
    | cons b ps =>
      simp only [edges,List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · exact ⟨List.mem_cons_of_mem _ (ih hc).1,List.mem_cons_of_mem _ (ih hc).2⟩

/-- Deleting an interior point is exactly one local split/merge in the
consecutive physical interval list; unrelated repeated coordinates remain. -/
theorem edges_local_filter (before after : List ℝ) (a t b : ℝ)
    (ha : a < t) (hb : t < b)
    (hbefore : ∀ x ∈ before, x ≤ a) (hafter : ∀ x ∈ after, b ≤ x) :
    (edges (before++a::t::b::after)).filter (fun c => c.1 ≠ t ∧ c.2 ≠ t) =
      (edges (before++a::b::after)).filter (fun c => c ≠ (a,b)) := by
  rw [edges_split,edges_merge]
  apply split_merge_filter _ _ a t b (ne_of_lt ha) (ne_of_gt hb)
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · have he := edges_mem_endpoints (before++[a]) c hc
      have hp (x : ℝ) (hx : x ∈ before++[a]) : x ≤ a := by
        rcases List.mem_append.mp hx with hx | hx
        · exact hbefore x hx
        · exact (List.mem_singleton.mp hx).le
      exact ⟨ne_of_lt ((hp c.1 he.1).trans_lt ha),ne_of_lt ((hp c.2 he.2).trans_lt ha)⟩
    · have he := edges_mem_endpoints (b::after) c hc
      have hp (x : ℝ) (hx : x ∈ b::after) : b ≤ x := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact hafter x hx
      exact ⟨ne_of_gt (hb.trans_le (hp c.1 he.1)),ne_of_gt (hb.trans_le (hp c.2 he.2))⟩
  · intro hc
    rcases List.mem_append.mp hc with hc | hc
    · have he := (edges_mem_endpoints (before++[a]) (a,b) hc).2
      rcases List.mem_append.mp he with he | he
      · exact (not_le_of_gt (ha.trans hb)) (hbefore b he)
      · have heq := List.mem_singleton.mp he
        linarith
    · have he := (edges_mem_endpoints (b::after) (a,b) hc).1
      rcases List.mem_cons.mp he with he | he
      · linarith
      · exact (not_le_of_gt (ha.trans hb)) (hafter a he)

end EnvyFreeResearch.Full.RefinedUpperPeeling
