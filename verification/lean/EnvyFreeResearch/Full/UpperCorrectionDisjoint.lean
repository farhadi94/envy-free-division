import EnvyFreeResearch.Full.UpperCorrectionOutcome

/-! Literal disjointness of the actual completed finite correction outputs. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperCorrectionDisjoint

open UpperRecordedDomain UpperDomainDifference UpperGridCells UpperLogicalCells
  UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply UpperRawPayments
  UpperCorrectionSetup UpperCircularStage UpperCorrectionAccepted UpperCorrectionPieces
  UpperCorrectionTrace UpperCorrectionOutcome UpperWholePaymentsPhysical

variable {n k m : ℕ}

theorem getD_mem {α : Type*} (xs : List α) (fallback : α) (j : ℕ) (hj : j < xs.length) :
    xs[j]?.getD fallback ∈ xs := by
  rw [List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem getD_disjoint (xs : List (List Component))
    (hxs : xs.Pairwise (fun a b => Disjoint (domain a) (domain b)))
    (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length) (hne : i ≠ j) :
    Disjoint (domain (xs[i]?.getD [])) (domain (xs[j]?.getD [])) := by
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rcases lt_or_gt_of_ne hne with h | h
  · exact List.Pairwise.rel_getElem_of_lt hi hj hxs h
  · exact (List.Pairwise.rel_getElem_of_lt hj hi hxs h).symm

variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (active : Fin k → Fin n) (reserve : State n) (hreserve : WellFormed μ reserve)
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
  (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells))
  (t : Fin k → ℝ) (eta lam : ℝ) (heta : 0 ≤ eta)
  (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
  (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j < 1 / 16)

include hreserve hzero hone hmono hsep hpositive heta hsmall ht hsum

/-- The actual finalized payments remain pairwise disjoint as literal sets,
including all null endpoint fragments. -/
theorem output_disjoint (policy : Policy n) (tape : Fin k → UpperCircular.Circle)
    (hrun : (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false) :
    Pairwise (fun i j => Disjoint (domain (output policy active reserve cuts t eta lam tape i))
      (domain (output policy active reserve cuts t eta lam tape j))) := by
  have hwhole := (UpperPayments.allocation_spec (table active reserve cuts) t eta heta
    (table_nonneg μ active reserve hreserve cuts hzero hmono hsep hpositive) hsmall
    (table_normalized μ active reserve hreserve cuts hzero hone hmono hsep hpositive) ht (by linarith)).1
  have hwp := pieces_disjoint (cell (domain reserve.cells) cuts) (cells_disjoint _ _ hmono)
    (whole active reserve cuts t eta) hwhole
  have hresult := successful_outputs policy (tasks active reserve cuts t eta lam)
    (startState active reserve cuts t eta).current tape hrun
  have hlength : (corrections policy active reserve cuts t eta lam tape).length = k := hresult.1
  have hpair : (corrections policy active reserve cuts t eta lam tape).Pairwise
      (fun a b => Disjoint (domain a) (domain b)) := payments_disjoint _ _
  have hcorr (j : Fin k) : domain ((corrections policy active reserve cuts t eta lam tape)[j.val]?.getD []) ⊆
      domain (startState active reserve cuts t eta).current.cells :=
    payments_domain_subset _ _ _ (getD_mem _ [] j.val (by
      change j.val < (corrections policy active reserve cuts t eta lam tape).length
      rw [hlength]
      exact j.isLt))
  have hbetween (i j : Fin k) :
      Disjoint (domain (wholeAtoms active reserve cuts t eta i))
        (domain ((corrections policy active reserve cuts t eta lam tape)[j.val]?.getD [])) := by
    rw [wholeAtoms_domain active reserve cuts hzero hmono hsep]
    exact (pending_disjoint_current μ active reserve hreserve cuts hzero hmono hsep t eta
      (startState active reserve cuts t eta).current Subset.rfl i).mono_right (hcorr j)
  intro i j hij
  rw [UpperCorrectionOutcome.output, UpperCorrectionOutcome.output, domain_append, domain_append]
  apply disjoint_union_left.mpr
  constructor
  · apply disjoint_union_right.mpr
    refine ⟨?_, hbetween i j⟩
    rw [wholeAtoms_domain active reserve cuts hzero hmono hsep,
      wholeAtoms_domain active reserve cuts hzero hmono hsep]
    exact hwp hij
  · apply disjoint_union_right.mpr
    refine ⟨(hbetween j i).symm, ?_⟩
    exact getD_disjoint _ hpair i.val j.val (by rw [hlength]; exact i.isLt)
      (by rw [hlength]; exact j.isLt) (fun h => hij (Fin.ext h))

end EnvyFreeResearch.Full.UpperCorrectionDisjoint
