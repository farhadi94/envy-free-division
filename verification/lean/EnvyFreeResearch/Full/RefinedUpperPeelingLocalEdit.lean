import EnvyFreeResearch.Full.RefinedUpperPeelingStability

/-! Local replacement of refined cells, with exact charge to selected cells. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperRepresentativeSupply
open scoped Classical
variable {Cell Parent Row : Type*} [DecidableEq Parent]

/-- Every physically selected parent appears in the final removal set. -/
theorem run_selected_parent_mem (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells : List Cell) (jobs : List (Row × Row)) (removed final : Finset Parent)
    (pairs : List (Cell × Cell))
    (hexec : run values parent cells jobs removed = some (pairs,final)) :
    ∀ pair ∈ pairs, parent pair.1 ∈ final ∧ parent pair.2 ∈ final := by
  induction jobs generalizing removed pairs final with
  | nil =>
    have heq : ([],removed) = (pairs,final) := by simpa only [run,Option.some.injEq] using hexec
    cases heq
    simp
  | cons job jobs ih =>
    cases hs : select (values job.1) (values job.2) (available parent removed cells) with
    | none => simp [run,hs] at hexec
    | some pair =>
      cases ht : run values parent cells jobs (addParents parent pair removed) with
      | none => simp [run,hs,ht] at hexec
      | some result =>
        rcases result with ⟨tail,final'⟩
        have heq : (pair::tail,final') = (pairs,final) := by
          simpa only [run,hs,Option.bind_some,ht,Option.map_some,Option.some.injEq] using hexec
        cases heq
        have hsub := run_removed_subset values parent cells jobs (addParents parent pair removed)
          final tail ht
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hsub (by simp [addParents]),hsub (by simp [addParents])⟩
        · exact ih _ _ _ ht p hp

/-- Replacing local cells can alter a surviving-parent execution only if
one of the replaced original cells was actually selected. It is a theorem
of the concrete lexicographic implementation, not a stability hypothesis. -/
theorem local_edit_agrees (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells cells' : List Cell) (jobs : List (Row × Row)) (removed final final' : Finset Parent)
    (pairs pairs' : List (Cell × Cell)) (Q : Parent) (keep keep' : Cell → Bool)
    (hoff : cells.filter keep = cells'.filter keep')
    (hlocal : ∀ c, keep' c = false → parent c = Q)
    (hexec : run values parent cells jobs removed = some (pairs,final))
    (hexec' : run values parent cells' jobs removed = some (pairs',final'))
    (hQ' : Q ∉ final')
    (hkeep : ∀ pair ∈ pairs, keep pair.1 = true ∧ keep pair.2 = true) :
    pairs = pairs' ∧ final = final' := by
  have hp' := run_selected_parent_mem values parent cells' jobs removed final' pairs' hexec'
  have hk' : ∀ pair ∈ pairs', keep' pair.1 = true ∧ keep' pair.2 = true := by
    intro p hp
    have hm := hp' p hp
    constructor
    · cases hk : keep' p.1 with
      | true => rfl
      | false => exact False.elim (hQ' ((hlocal p.1 hk) ▸ hm.1))
    · cases hk : keep' p.2 with
      | true => rfl
      | false => exact False.elim (hQ' ((hlocal p.2 hk) ▸ hm.2))
  have h := run_filter_unchosen values parent cells jobs removed final pairs keep hexec hkeep
  have h' := run_filter_unchosen values parent cells' jobs removed final' pairs' keep' hexec' hk'
  rw [hoff,h'] at h
  exact Prod.mk.inj (Option.some.inj h.symm)

theorem local_edit_forces_selected_cell (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells cells' : List Cell) (jobs : List (Row × Row)) (removed final final' : Finset Parent)
    (pairs pairs' : List (Cell × Cell)) (Q : Parent) (keep keep' : Cell → Bool)
    (hoff : cells.filter keep = cells'.filter keep')
    (hlocal : ∀ c, keep' c = false → parent c = Q)
    (hexec : run values parent cells jobs removed = some (pairs,final))
    (hexec' : run values parent cells' jobs removed = some (pairs',final'))
    (hQ' : Q ∉ final') (hne : pairs ≠ pairs' ∨ final ≠ final') :
    ∃ pair ∈ pairs, keep pair.1 = false ∨ keep pair.2 = false := by
  by_contra hn
  have hkeep : ∀ pair ∈ pairs, keep pair.1 = true ∧ keep pair.2 = true := by
    intro p hp
    have hf : ¬(keep p.1 = false ∨ keep p.2 = false) := fun h => hn ⟨p,hp,h⟩
    exact ⟨by cases h : keep p.1 <;> simp_all,by cases h : keep p.2 <;> simp_all⟩
  have heq := local_edit_agrees values parent cells cells' jobs removed final final' pairs pairs'
    Q keep keep' hoff hlocal hexec hexec' hQ' hkeep
  exact hne.elim (fun h => h heq.1) (fun h => h heq.2)

end EnvyFreeResearch.Full.RefinedUpperPeeling
