import EnvyFreeResearch.Full.RefinedUpperStabilityPointTransport
import EnvyFreeResearch.Full.RefinedUpperStabilityProcedureCoverage

/-! Bad partial-cell discrepancies imply an actual protected endpoint. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperSortedGrid UpperGridInterpolation UpperRepresentativeSupply
open scoped Classical
variable {Row : Type*} {a m : ℕ}

/-- Pointwise stability of the concrete cumulative-grid procedure. All
witnesses are computed by its actual selectors. An unprotected sample that
survives deletion obeys both partial-cell bounds for every final row pair. -/
theorem point_unprotected_control
    (F : Row → ℝ → ℝ) (hF : ∀ i, Monotone (F i))
    (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse)
    (rawValues : Fin (m+3) → ℝ) (raw : Fin (m+3)) (p : Fin (m+1))
    (hrank : (UpperSortedGrid.select rawValues).symm raw = p.succ.castSucc)
    (hunique : ∀ j, sorted rawValues j = sorted rawValues p.succ.castSucc → j = p.succ.castSucc)
    (hfit : intervalFits coarse
      (sorted rawValues p.castSucc.castSucc,sorted rawValues p.succ.succ)
      (intervalParent coarse (sorted rawValues p.castSucc.castSucc,sorted rawValues p.succ.succ)))
    (jobs finalJobs : List (Row × Row))
    (pairs : List (Fin (m+2) × Fin (m+2))) (pairs' : List (Fin (m+1) × Fin (m+1)))
    (final final' : Finset (Fin (a+1)))
    (hexec : pointRun F coarse jobs (sorted rawValues) = some (pairs,final))
    (hexec' : pointRun F coarse jobs (sorted (raw.removeNth rawValues)) = some (pairs',final'))
    (hsurvives : intervalParent coarse
      (sorted rawValues p.castSucc.castSucc,sorted rawValues p.succ.succ) ∉ final')
    (huncharged : ∀ k, endpointProcedure F coarse jobs finalJobs (sorted rawValues) k ≠ rawValues raw)
    (i j : Row) (hij : (i,j) ∈ finalJobs) (u v A : ℝ)
    (hA : ∀ c ∈ List.ofFn (intervalLabel (sorted (raw.removeNth rawValues))),
      intervalParent coarse c ∉ final' → |u*intervalValues F i c-v*intervalValues F j c| ≤ A) :
    |u*intervalValues F i (sorted rawValues p.castSucc.castSucc,rawValues raw)-
      v*intervalValues F j (sorted rawValues p.castSucc.castSucc,rawValues raw)| ≤ 2*A ∧
    |u*intervalValues F i (rawValues raw,sorted rawValues p.succ.succ)-
      v*intervalValues F j (rawValues raw,sorted rawValues p.succ.succ)| ≤ 2*A := by
  let oldPoints := sorted rawValues
  let newPoints := sorted (raw.removeNth rawValues)
  let oldCells := List.ofFn (intervalLabel oldPoints)
  let newCells := List.ofFn (intervalLabel newPoints)
  let oldPairs := pairs.map (fun q => (intervalLabel oldPoints q.1,intervalLabel oldPoints q.2))
  let newPairs := pairs'.map (fun q => (intervalLabel newPoints q.1,intervalLabel newPoints q.2))
  let l := oldPoints p.castSucc.castSucc
  let t := rawValues raw
  let r := oldPoints p.succ.succ
  let Q := intervalParent coarse (l,r)
  have hexecO : pointRun F coarse jobs oldPoints = some (pairs,final) := hexec
  have ht : t = oldPoints p.succ.castSucc := by
    change rawValues raw = sorted rawValues p.succ.castSucc
    rw [← hrank]
    simp [UpperSortedGrid.sorted]
  have hlt : l < t := by
    rw [ht]
    have hle : l ≤ oldPoints p.succ.castSucc := sorted_monotone rawValues (by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    by_contra hn
    have hi := congrArg Fin.val (hunique p.castSucc.castSucc (le_antisymm hle (le_of_not_gt hn)))
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  have htr : t < r := by
    rw [ht]
    have hle : oldPoints p.succ.castSucc ≤ r := sorted_monotone rawValues (by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    by_contra hn
    have hi := congrArg Fin.val (hunique p.succ.succ (le_antisymm hle (le_of_not_gt hn)).symm)
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  have hparents := split_interval_parent coarse hc l t r hlt htr hfit
  have hrun : run (intervalValues F) (intervalParent coarse) oldCells jobs ∅ = some (oldPairs,final) := by
    have h := pointRun_interval_run F hF coarse jobs oldPoints (sorted_monotone rawValues)
    rw [hexec] at h
    exact h
  have hrun' : run (intervalValues F) (intervalParent coarse) newCells jobs ∅ = some (newPairs,final') := by
    have h := pointRun_interval_run F hF coarse jobs newPoints (sorted_monotone _)
    rw [hexec'] at h
    exact h
  have hprotected := uncharged_protected_endpoints F coarse jobs finalJobs oldPoints pairs final
    hexec t huncharged
  have hselEndpoints : ∀ q ∈ pairs,
      oldPoints q.1.castSucc ≠ t ∧ oldPoints q.1.succ ≠ t ∧
      oldPoints q.2.castSucc ≠ t ∧ oldPoints q.2.succ ≠ t := by
    intro q hq
    apply hprotected q
    simp only [protectedPairs,pointResult,hexecO,Option.getD_some,Prod.fst]
    exact List.mem_append_left _ hq
  have hunchosen : ∀ pair ∈ oldPairs,
      pair.1.1 ≠ t ∧ pair.1.2 ≠ t ∧ pair.2.1 ≠ t ∧ pair.2.2 ≠ t := by
    intro pair hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hselEndpoints q hq
  have hoff := sorted_interval_delete_filter rawValues raw p hrank hunique
  have hlocal : ∀ c : ℝ × ℝ, decide (c ≠ (l,r)) = false → intervalParent coarse c = Q := by
    intro c hh
    have he : c = (l,r) := by simpa only [decide_eq_false_iff_not,not_not] using hh
    rw [he]
  have hkeep : ∀ pair ∈ oldPairs,
      decide (pair.1.1 ≠ t ∧ pair.1.2 ≠ t) = true ∧
      decide (pair.2.1 ≠ t ∧ pair.2.2 ≠ t) = true := by
    intro pair hp
    have hh := hunchosen pair hp
    exact ⟨by simpa using And.intro hh.1 hh.2.1,by simpa using hh.2.2⟩
  have hsame := local_edit_agrees (intervalValues F) (intervalParent coarse) oldCells newCells
    jobs ∅ final final' oldPairs newPairs Q
    (fun c => decide (c.1 ≠ t ∧ c.2 ≠ t)) (fun c => decide (c ≠ (l,r)))
    hoff hlocal hrun hrun' hsurvives hkeep
  have hEparent : pointParents coarse oldPoints p.castSucc = Q := by
    change intervalParent coarse (oldPoints p.castSucc.castSucc,oldPoints p.castSucc.succ) = Q
    simpa only [← Fin.castSucc_succ,← ht] using hparents.1
  have hEnot : pointParents coarse oldPoints p.castSucc ∉ final := by
    rw [hEparent,hsame.2]
    exact hsurvives
  have hnonempty : available (pointParents coarse oldPoints) final (List.finRange (m+2)) ≠ [] := by
    have hm := (mem_available (pointParents coarse oldPoints) final (List.finRange (m+2)) p.castSucc).mpr
      ⟨by simp,hEnot⟩
    intro he
    simpa [he] using hm
  have hn (s : Row) (c : Fin (m+2)) : 0 ≤ pointValues F oldPoints s c := by
    apply sub_nonneg.mpr
    exact hF s (sorted_monotone rawValues (by simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega))
  obtain ⟨f,g,hchoice,_,_,_⟩ := select_spec (pointValues F oldPoints i) (pointValues F oldPoints j)
    (available (pointParents coarse oldPoints) final (List.finRange (m+2))) hnonempty
    (fun c _ => hn i c) (fun c _ => hn j c)
  have hfinalPair : finalPair F coarse jobs oldPoints (i,j) = (f,g) := by
    simp only [finalPair,pointResult,hexecO,Option.getD_some,Prod.snd,hchoice]
  have hfg : (f,g) ∈ protectedPairs F coarse jobs finalJobs oldPoints := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(i,j),hij,hfinalPair⟩
  have havoid := hprotected (f,g) hfg
  have hw : select (intervalValues F i) (intervalValues F j)
      (available (intervalParent coarse) final oldCells) =
        some (intervalLabel oldPoints f,intervalLabel oldPoints g) := by
    rw [pointSelect_interval_select F hF coarse oldPoints (sorted_monotone rawValues) final i j,hchoice]
    rfl
  exact sorted_deletion_partial_control (intervalValues F) (intervalValues_nonneg F) coarse hc
    rawValues raw p hrank hunique hfit jobs ∅ final final' oldPairs newPairs hrun hrun' hsurvives
    hunchosen i j (intervalLabel oldPoints f) (intervalLabel oldPoints g) hw
    ⟨havoid.1,havoid.2.1⟩ havoid.2.2 u v A hA

end EnvyFreeResearch.Full.RefinedUpperPeeling
