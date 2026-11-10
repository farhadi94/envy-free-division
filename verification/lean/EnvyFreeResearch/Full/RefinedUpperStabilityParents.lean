import EnvyFreeResearch.Full.RefinedUpperPeelingPhysicalLabels

/-! Coarse parent consistency of the two actual cells split at a sample. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open Set UpperLogicalCells
open scoped Classical

lemma firstIntervalParent_spec {a : ℕ} (coarse : Fin (a+2) → ℝ) (interval : ℝ × ℝ)
    (js : List (Fin (a+1)))
    (hex : ∃ j ∈ js, intervalFits coarse interval j) :
    intervalFits coarse interval (firstIntervalParent coarse interval js) := by
  induction js with
  | nil => simp at hex
  | cons j js ih =>
    by_cases h : intervalFits coarse interval j
    · simpa [firstIntervalParent,h] using h
    · rw [firstIntervalParent,if_neg h]
      apply ih
      obtain ⟨k,hk,hfit⟩ := hex
      rcases List.mem_cons.mp hk with rfl | hk
      · exact False.elim (h hfit)
      · exact ⟨k,hk,hfit⟩

lemma intervalParent_spec {a : ℕ} (coarse : Fin (a+2) → ℝ) (interval : ℝ × ℝ)
    (hex : ∃ j, intervalFits coarse interval j) :
    intervalFits coarse interval (intervalParent coarse interval) := by
  apply firstIntervalParent_spec
  obtain ⟨j,hj⟩ := hex
  exact ⟨j,by simp,hj⟩

lemma intervalFits_unique {a : ℕ} (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse)
    (l r : ℝ) (hlr : l < r) (j k : Fin (a+1))
    (hj : intervalFits coarse (l,r) j) (hk : intervalFits coarse (l,r) k) : j = k := by
  by_contra hne
  have hd := consecutive_disjoint coarse hc hne
  exact Set.disjoint_left.mp hd ⟨hj.1.trans_lt hlr,hj.2⟩ ⟨hk.1.trans_lt hlr,hk.2⟩

/-- Both adjacent cells inherit precisely the merged cell's coarse parent.
No tie-breaking uniqueness is assumed for null coarse cells. -/
theorem split_interval_parent {a : ℕ} (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse)
    (l t r : ℝ) (hlt : l < t) (htr : t < r)
    (hfit : intervalFits coarse (l,r) (intervalParent coarse (l,r))) :
    intervalParent coarse (l,t) = intervalParent coarse (l,r) ∧
      intervalParent coarse (t,r) = intervalParent coarse (l,r) := by
  have hl : intervalFits coarse (l,t) (intervalParent coarse (l,r)) := ⟨hfit.1,htr.le.trans hfit.2⟩
  have hr : intervalFits coarse (t,r) (intervalParent coarse (l,r)) := ⟨hfit.1.trans hlt.le,hfit.2⟩
  exact ⟨intervalFits_unique coarse hc l t hlt _ _
      (intervalParent_spec coarse (l,t) ⟨_,hl⟩) hl,
    intervalFits_unique coarse hc t r htr _ _
      (intervalParent_spec coarse (t,r) ⟨_,hr⟩) hr⟩

end EnvyFreeResearch.Full.RefinedUpperPeeling
