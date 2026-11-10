import EnvyFreeResearch.Full.RefinedUpperStabilityCharges

/-! Concrete interval endpoints for the split/merge charging argument. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open scoped Classical

/-- The two refined intervals created by inserting `t` are the only old
intervals removed when filtering incidence with `t`. The replacement interval
can be removed by its coarse parent in the alternate execution. -/
theorem split_merge_filter {Point : Type*} [DecidableEq Point]
    (before after : List (Point × Point)) (a t b : Point)
    (ha : a ≠ t) (hb : b ≠ t)
    (hfresh : ∀ c ∈ before++after, c.1 ≠ t ∧ c.2 ≠ t)
    (hmerged : (a,b) ∉ before++after) :
    (before++[(a,t),(t,b)]++after).filter (fun c => c.1 ≠ t ∧ c.2 ≠ t) =
      (before++[(a,b)]++after).filter (fun c => c ≠ (a,b)) := by
  have hbefore : before.filter (fun c => c.1 ≠ t ∧ c.2 ≠ t) = before := by
    apply List.filter_eq_self.mpr
    intro c hc
    simpa using hfresh c (List.mem_append_left after hc)
  have hafter : after.filter (fun c => c.1 ≠ t ∧ c.2 ≠ t) = after := by
    apply List.filter_eq_self.mpr
    intro c hc
    simpa using hfresh c (List.mem_append_right before hc)
  have hbefore' : before.filter (fun c => c ≠ (a,b)) = before := by
    apply List.filter_eq_self.mpr
    intro c hc
    simp only [decide_eq_true_eq]
    intro he
    exact hmerged (he ▸ List.mem_append_left after hc)
  have hafter' : after.filter (fun c => c ≠ (a,b)) = after := by
    apply List.filter_eq_self.mpr
    intro c hc
    simp only [decide_eq_true_eq]
    intro he
    exact hmerged (he ▸ List.mem_append_right before hc)
  simp only [List.filter_append,hbefore,hafter,hbefore',hafter']
  simp [ha,hb]

variable {Index Point : Type*} [Fintype Index] [DecidableEq Index] [DecidableEq Point]

/-- Actual sample indices incident with a physical interval endpoint. -/
def sampleEndpoints (sample : Index → Point) (cell : Point × Point) : Finset Index :=
  Finset.univ.filter (fun i => sample i = cell.1) ∪
    Finset.univ.filter (fun i => sample i = cell.2)

@[simp] theorem mem_sampleEndpoints (sample : Index → Point) (cell : Point × Point) (i : Index) :
    i ∈ sampleEndpoints sample cell ↔ sample i = cell.1 ∨ sample i = cell.2 := by
  simp [sampleEndpoints]

/-- Noncolliding samples yield at most two charged labels per interval. -/
theorem sampleEndpoints_card (sample : Index → Point) (hinj : Function.Injective sample)
    (cell : Point × Point) : (sampleEndpoints sample cell).card ≤ 2 := by
  have hfiber (p : Point) : (Finset.univ.filter (fun i => sample i = p)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hinj ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hu := Finset.card_union_le (Finset.univ.filter (fun i => sample i = cell.1))
    (Finset.univ.filter (fun i => sample i = cell.2))
  have h1 := hfiber cell.1
  have h2 := hfiber cell.2
  unfold sampleEndpoints
  omega

/-- Concrete selected interval endpoints obey the complete charging budget. -/
theorem sample_charges_card (sample : Index → Point) (hinj : Function.Injective sample)
    (selected finalWitnesses : List ((Point × Point) × (Point × Point))) :
    (charges (sampleEndpoints sample) (selected++finalWitnesses)).card ≤
      4*selected.length+4*finalWitnesses.length :=
  total_charges_card _ _ _ (sampleEndpoints_card sample hinj)

end EnvyFreeResearch.Full.RefinedUpperPeeling
