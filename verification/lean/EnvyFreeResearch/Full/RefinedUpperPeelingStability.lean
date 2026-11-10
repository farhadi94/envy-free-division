import EnvyFreeResearch.Full.RefinedUpperPeeling

/-! Deterministic deletion consistency of the actual peeling implementation. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperRepresentativeSupply
open scoped Classical
variable {Cell Parent Row : Type*} [DecidableEq Parent]

lemma run_removed_subset (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells : List Cell) (jobs : List (Row × Row)) (removed final : Finset Parent)
    (pairs : List (Cell × Cell))
    (hexec : run values parent cells jobs removed = some (pairs,final)) : removed ⊆ final := by
  induction jobs generalizing removed pairs final with
  | nil =>
    have heq : ([],removed) = (pairs,final) := by simpa only [run,Option.some.injEq] using hexec
    cases heq
    exact Finset.Subset.refl _
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
        exact (removed_subset_addParents parent pair removed).trans (ih _ _ _ ht)

lemma available_filter (parent : Cell → Parent) (removed : Finset Parent)
    (cells : List Cell) (keep : Cell → Bool) :
    available parent removed (cells.filter keep) = (available parent removed cells).filter keep := by
  simp only [available,List.filter_filter]
  congr 1
  funext c
  exact Bool.and_comm _ _

/-- Any deterministic deletion of cells not chosen by the actual run leaves
its complete transcript unchanged. No rank or positivity premise is needed. -/
theorem run_filter_unchosen (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells : List Cell) (jobs : List (Row × Row)) (removed final : Finset Parent)
    (pairs : List (Cell × Cell)) (keep : Cell → Bool)
    (hexec : run values parent cells jobs removed = some (pairs,final))
    (hkeep : ∀ pair ∈ pairs, keep pair.1 = true ∧ keep pair.2 = true) :
    run values parent (cells.filter keep) jobs removed = some (pairs,final) := by
  induction jobs generalizing removed pairs final with
  | nil => simpa [run] using hexec
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
        have hp := hkeep pair (by simp)
        have hs' : select (values job.1) (values job.2)
            (available parent removed (cells.filter keep)) = some pair := by
          rw [available_filter]
          exact RefinedUpperWitnessSelector.select_filter
            (fun c => (values job.1 c,values job.2 c)) (available parent removed cells)
            keep pair.1 pair.2 hs hp.1 hp.2
        have ht' := ih _ _ _ ht (fun p hp => hkeep p (by simp [hp]))
        simp only [run,hs',Option.bind_some,ht',Option.map_some]

/-- Removing an entire coarse parent that the actual run never selects
preserves every chosen cell, its tie-breaking order, and the final removed set. -/
theorem run_delete_unused_parent (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells : List Cell) (jobs : List (Row × Row)) (removed final : Finset Parent)
    (pairs : List (Cell × Cell)) (Q : Parent)
    (hexec : run values parent cells jobs removed = some (pairs,final))
    (hQ : Q ∉ final) :
    run values parent (cells.filter (fun c => parent c ≠ Q)) jobs removed = some (pairs,final) := by
  induction jobs generalizing removed pairs final with
  | nil => simpa [run] using hexec
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
        have hleft : parent pair.1 ≠ Q := by
          intro he
          apply hQ
          apply hsub
          simp [addParents,← he]
        have hright : parent pair.2 ≠ Q := by
          intro he
          apply hQ
          apply hsub
          simp [addParents,← he]
        have hs' : select (values job.1) (values job.2)
            (available parent removed (cells.filter (fun c => parent c ≠ Q))) = some pair := by
          rw [available_filter]
          exact RefinedUpperWitnessSelector.select_filter
            (fun c => (values job.1 c,values job.2 c)) (available parent removed cells)
            (fun c => decide (parent c ≠ Q)) pair.1 pair.2 hs (by simpa using hleft) (by simpa using hright)
        have ht' := ih _ _ _ ht hQ
        simp only [run,hs',Option.bind_some,ht',Option.map_some]

/-- Two grids differing only inside a coarse parent have identical runs
whenever that parent survives both. This includes deleting a grid endpoint:
its two adjacent cells and their merged cell have the same coarse parent. -/
theorem run_agree_off_unused_parent (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells cells' : List Cell) (jobs : List (Row × Row)) (removed final final' : Finset Parent)
    (pairs pairs' : List (Cell × Cell)) (Q : Parent)
    (hoff : cells.filter (fun c => parent c ≠ Q) = cells'.filter (fun c => parent c ≠ Q))
    (hexec : run values parent cells jobs removed = some (pairs,final))
    (hexec' : run values parent cells' jobs removed = some (pairs',final'))
    (hQ : Q ∉ final) (hQ' : Q ∉ final') : pairs = pairs' ∧ final = final' := by
  have h := run_delete_unused_parent values parent cells jobs removed final pairs Q hexec hQ
  have h' := run_delete_unused_parent values parent cells' jobs removed final' pairs' Q hexec' hQ'
  rw [hoff,h'] at h
  exact Prod.mk.inj (Option.some.inj h.symm)

end EnvyFreeResearch.Full.RefinedUpperPeeling
