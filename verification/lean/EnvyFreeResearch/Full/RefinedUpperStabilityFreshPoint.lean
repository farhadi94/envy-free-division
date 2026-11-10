import EnvyFreeResearch.Full.RefinedUpperStability
import EnvyFreeResearch.Full.UpperGridInterpolationRawDelete
import EnvyFreeResearch.Full.UpperGridInterpolationKernel

/-! Applying the deletion certificate to a fresh physical coordinate.
All sorting ranks and the restored grid are derived from literal insertion. -/
noncomputable section
open Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperStability
open RefinedUpperPeeling UpperGridInterpolation UpperSortedGrid
variable {Row : Type*} {a b m : ℕ}

theorem fresh_point_control
    (F : Row → ℝ → ℝ) (hF : ∀ i, Monotone (F i))
    (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse)
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ) (z : ℝ)
    (hz : 0 < z ∧ z < 1) (hnew : ∀ e, augmented permanent samples e ≠ z)
    (jobs finalJobs : List (Row × Row))
    (pairs : List (Fin (b+m+2) × Fin (b+m+2)))
    (pairs' : List (Fin (b+m+1) × Fin (b+m+1)))
    (final final' : Finset (Fin (a+1)))
    (hexec : pointRun F coarse jobs (sorted (augmented permanent (Fin.cons z samples))) = some (pairs,final))
    (hexec' : pointRun F coarse jobs (sorted (augmented permanent samples)) = some (pairs',final'))
    (hfit : ∀ e : Fin (b+m+1), intervalFits coarse
      (sorted (augmented permanent samples) e.castSucc, sorted (augmented permanent samples) e.succ)
      (intervalParent coarse
        (sorted (augmented permanent samples) e.castSucc, sorted (augmented permanent samples) e.succ)))
    (hsurvive : ∀ e : Fin (b+m+1),
      sorted (augmented permanent samples) e.castSucc < z →
      z < sorted (augmented permanent samples) e.succ →
      intervalParent coarse
        (sorted (augmented permanent samples) e.castSucc, sorted (augmented permanent samples) e.succ) ∉ final')
    (hbad : z ∉ protectedBad (endpointProcedure F coarse jobs finalJobs) permanent samples)
    (i j : Row) (hij : (i,j) ∈ finalJobs) (u v A : ℝ)
    (hA : ∀ c ∈ List.ofFn (intervalLabel (sorted (augmented permanent samples))),
      intervalParent coarse c ∉ final' → |u*intervalValues F i c-v*intervalValues F j c| ≤ A) :
    ∃ e : Fin (b+m+1),
      sorted (augmented permanent samples) e.castSucc < z ∧
      z < sorted (augmented permanent samples) e.succ ∧
      |u*intervalValues F i (sorted (augmented permanent samples) e.castSucc,z)-
        v*intervalValues F j (sorted (augmented permanent samples) e.castSucc,z)| ≤ 2*A ∧
      |u*intervalValues F i (z,sorted (augmented permanent samples) e.succ)-
        v*intervalValues F j (z,sorted (augmented permanent samples) e.succ)| ≤ 2*A := by
  let rawValues := augmented permanent (Fin.cons z samples)
  let raw := sampleLabel (b := b) (0 : Fin (m+1))
  obtain ⟨p,hrank⟩ := augmented_test_interior permanent samples z hz
  have hraw : rawValues raw = z := by simp [rawValues,raw,augmented_sample]
  have htest : sorted rawValues p.succ.castSucc = z := by
    rw [← hrank]
    change rawValues (UpperSortedGrid.select rawValues ((UpperSortedGrid.select rawValues).symm raw)) = z
    rw [Equiv.apply_symm_apply]
    exact hraw
  have hunique : ∀ e, sorted rawValues e = sorted rawValues p.succ.castSucc → e = p.succ.castSucc := by
    intro e he
    have hrawUnique := augmented_test_unique permanent samples z hnew
    have hlabel : UpperSortedGrid.select rawValues e = raw := hrawUnique _ (he.trans htest)
    exact ((UpperSortedGrid.select rawValues).eq_symm_apply.mpr hlabel).trans hrank
  have hleft : sorted (augmented permanent samples) p.castSucc =
      sorted rawValues p.castSucc.castSucc := by
    rw [← augmented_remove_test permanent samples z, sorted_removeNth, hrank, remove_left]
  have hright : sorted (augmented permanent samples) p.succ =
      sorted rawValues p.succ.succ := by
    rw [← augmented_remove_test permanent samples z, sorted_removeNth, hrank, remove_right]
  have hl : sorted (augmented permanent samples) p.castSucc < z := by
    rw [hleft,← htest]
    have hm := sorted_monotone rawValues (show p.castSucc.castSucc ≤ p.succ.castSucc by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    apply lt_of_le_of_ne hm
    intro he
    have hi := congrArg Fin.val (hunique p.castSucc.castSucc he)
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  have hr : z < sorted (augmented permanent samples) p.succ := by
    rw [hright,← htest]
    have hm := sorted_monotone rawValues (show p.succ.castSucc ≤ p.succ.succ by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    apply lt_of_le_of_ne hm
    intro he
    have hi := congrArg Fin.val (hunique p.succ.succ he.symm)
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  have hfit' := hfit p
  rw [hleft,hright] at hfit'
  have hs := hsurvive p hl hr
  rw [hleft,hright] at hs
  have he' : pointRun F coarse jobs (sorted (raw.removeNth rawValues)) = some (pairs',final') := by
    simpa only [raw,rawValues,augmented_remove_test] using hexec'
  have huncharged : ∀ e, endpointProcedure F coarse jobs finalJobs (sorted rawValues) e ≠ rawValues raw := by
    intro e he
    exact hbad ⟨e,he.trans hraw⟩
  have hA' : ∀ c ∈ List.ofFn (intervalLabel (sorted (raw.removeNth rawValues))),
      intervalParent coarse c ∉ final' → |u*intervalValues F i c-v*intervalValues F j c| ≤ A := by
    simpa only [raw,rawValues,augmented_remove_test] using hA
  have h := point_unprotected_control F hF coarse hc rawValues raw p hrank hunique hfit'
    jobs finalJobs pairs pairs' final final' hexec he' hs huncharged i j hij u v A hA'
  refine ⟨p,hl,hr,?_⟩
  simpa only [hleft,hright,hraw] using h

end EnvyFreeResearch.Full.RefinedUpperStability
