import EnvyFreeResearch.Full.RefinedUpperStabilitySortedDelete
import EnvyFreeResearch.Full.RefinedUpperStabilityParents

/-! Pointwise two-sided discrepancy control for actual sorted-grid deletion. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperSortedGrid UpperGridInterpolation UpperRepresentativeSupply
open scoped Classical

variable {Row : Type*} {a m : ℕ}

/-- The uncharged test point obeys both partial-cell discrepancy bounds on
the actual sorted augmented/deleted grids. Parent agreement, local editing,
and determinant control are conclusions of the concrete implementation. -/
theorem sorted_deletion_partial_control
    (values : Row → (ℝ × ℝ) → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse)
    (rawValues : Fin (m+2) → ℝ) (raw : Fin (m+2)) (p : Fin m)
    (hrank : (UpperSortedGrid.select rawValues).symm raw = p.succ.castSucc)
    (hunique : ∀ j, sorted rawValues j = sorted rawValues p.succ.castSucc → j = p.succ.castSucc)
    (hfit : intervalFits coarse
      (sorted rawValues p.castSucc.castSucc, sorted rawValues p.succ.succ)
      (intervalParent coarse (sorted rawValues p.castSucc.castSucc, sorted rawValues p.succ.succ)))
    (jobs : List (Row × Row)) (removed final final' : Finset (Fin (a+1)))
    (pairs pairs' : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hexec : run values (intervalParent coarse)
      (List.ofFn (intervalLabel (sorted rawValues))) jobs removed = some (pairs,final))
    (hexec' : run values (intervalParent coarse)
      (List.ofFn (fun i : Fin m => (sorted (raw.removeNth rawValues) i.castSucc,
        sorted (raw.removeNth rawValues) i.succ))) jobs removed = some (pairs',final'))
    (hsurvives : intervalParent coarse
      (sorted rawValues p.castSucc.castSucc,sorted rawValues p.succ.succ) ∉ final')
    (hunchosen : ∀ pair ∈ pairs,
      pair.1.1 ≠ rawValues raw ∧ pair.1.2 ≠ rawValues raw ∧
      pair.2.1 ≠ rawValues raw ∧ pair.2.2 ≠ rawValues raw)
    (i j : Row) (F G : ℝ × ℝ)
    (hw : select (values i) (values j)
      (available (intervalParent coarse) final (List.ofFn (intervalLabel (sorted rawValues)))) = some (F,G))
    (hF : F.1 ≠ rawValues raw ∧ F.2 ≠ rawValues raw)
    (hG : G.1 ≠ rawValues raw ∧ G.2 ≠ rawValues raw)
    (u v A : ℝ)
    (hA : ∀ c ∈ (List.ofFn (fun i : Fin m => (sorted (raw.removeNth rawValues) i.castSucc,
        sorted (raw.removeNth rawValues) i.succ))), intervalParent coarse c ∉ final' →
        |u*values i c-v*values j c| ≤ A) :
    |u*values i (sorted rawValues p.castSucc.castSucc,rawValues raw)-
      v*values j (sorted rawValues p.castSucc.castSucc,rawValues raw)| ≤ 2*A ∧
    |u*values i (rawValues raw,sorted rawValues p.succ.succ)-
      v*values j (rawValues raw,sorted rawValues p.succ.succ)| ≤ 2*A := by
  let l := sorted rawValues p.castSucc.castSucc
  let t := rawValues raw
  let r := sorted rawValues p.succ.succ
  have ht : t = sorted rawValues p.succ.castSucc := by
    change rawValues raw = sorted rawValues p.succ.castSucc
    rw [← hrank]
    simp [UpperSortedGrid.sorted]
  have hlt : l < t := by
    rw [ht]
    have hle : l ≤ sorted rawValues p.succ.castSucc := sorted_monotone rawValues (by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    by_contra hn
    have hi := congrArg Fin.val (hunique p.castSucc.castSucc (le_antisymm hle (le_of_not_gt hn)))
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  have htr : t < r := by
    rw [ht]
    have hle : sorted rawValues p.succ.castSucc ≤ r := sorted_monotone rawValues (by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    by_contra hn
    have hi := congrArg Fin.val (hunique p.succ.succ (le_antisymm hle (le_of_not_gt hn)).symm)
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  have hparents := split_interval_parent coarse hc l t r hlt htr hfit
  have hoff := sorted_interval_delete_filter rawValues raw p hrank hunique
  have hlocal : ∀ c : ℝ × ℝ, decide (c ≠ (l,r)) = false →
      intervalParent coarse c = intervalParent coarse (l,r) := by
    intro c hh
    have he : c = (l,r) := by simpa only [decide_eq_false_iff_not,not_not] using hh
    rw [he]
  have hkeep : ∀ pair ∈ pairs,
      decide (pair.1.1 ≠ t ∧ pair.1.2 ≠ t) = true ∧
      decide (pair.2.1 ≠ t ∧ pair.2.2 ≠ t) = true := by
    intro pair hp
    have hh := hunchosen pair hp
    exact ⟨by simpa [t] using And.intro hh.1 hh.2.1,by simpa [t] using hh.2.2⟩
  have hbound (E : ℝ × ℝ) (hE : E ∈ List.ofFn (intervalLabel (sorted rawValues)))
      (hpE : intervalParent coarse E = intervalParent coarse (l,r)) :
      |u*values i E-v*values j E| ≤ 2*A :=
    local_edit_partial_control values hnonneg (intervalParent coarse) _ _ jobs removed final final'
      pairs pairs' (intervalParent coarse (l,r))
      (fun c => decide (c.1 ≠ t ∧ c.2 ≠ t)) (fun c => decide (c ≠ (l,r)))
      hoff hlocal hexec hexec' hsurvives hkeep i j F G E hw
      (by simpa [t] using hF) (by simpa [t] using hG) hE hpE u v A hA
  constructor
  · apply hbound (l,t)
    · apply List.mem_ofFn.mpr
      refine ⟨p.castSucc,?_⟩
      simp [intervalLabel,l,ht,Fin.castSucc_succ]
    · exact hparents.1
  · apply hbound (t,r)
    · apply List.mem_ofFn.mpr
      refine ⟨p.succ,?_⟩
      simp [intervalLabel,r,ht]
    · exact hparents.2

end EnvyFreeResearch.Full.RefinedUpperPeeling
