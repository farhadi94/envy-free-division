import EnvyFreeResearch.Full.RefinedUpperPreparationLocal
import EnvyFreeResearch.Full.RefinedUpperCorrectionSetup

/-! The bound used in the deletion argument is the actual retained-table
cell gap, with the realized normalizers and the original-buffer cumulatives. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperStability
open RefinedUpperPeeling RefinedUpperPreparation UpperRecordedDomain UpperCorrectionExecution
  UpperLogicalCells UpperDomainDifference RefinedUpperCorrectionSetup
variable {n k a m : ℕ}

theorem retained_cell_value (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (origin reserve : State n)
    (hreserve : WellFormed μ reserve)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (coarse : Fin (a+2) → ℝ) (removed : Finset (Fin (a+1)))
    (hT : domain reserve.cells = ⋃ p, if p ∉ removed then cell (domain origin.cells) coarse p else ∅)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
    (e : Fin (m+1)) (p : Fin (a+1))
    (hfit : intervalFits coarse (intervalLabel cuts e) p) (hp : p ∉ removed) (i : Fin k) :
    ((μ (active i)).real (domain origin.cells)/(μ (active i)).real (domain reserve.cells)) *
      intervalValues (physicalCumulative μ active origin) i (intervalLabel cuts e) =
        table active reserve cuts i e := by
  letI : Nonempty (Fin k) := ⟨i⟩
  rw [table_correct μ active reserve hreserve cuts hzero hmono hsep,
    measureReal_congr (cell_ae_eq (μ (active i)) (domain reserve.cells) cuts e)]
  rw [retained_interval_eq _ _ coarse removed hT _ _ p hfit hp]
  exact intervalValues_renormalized μ active origin i (hpositive i) _ _
    (hmono (by simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)) _

theorem retained_cell_gap (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (origin reserve : State n)
    (hreserve : WellFormed μ reserve)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (coarse : Fin (a+2) → ℝ) (removed : Finset (Fin (a+1)))
    (hT : domain reserve.cells = ⋃ p, if p ∉ removed then cell (domain origin.cells) coarse p else ∅)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
    (e : Fin (m+1)) (p : Fin (a+1))
    (hfit : intervalFits coarse (intervalLabel cuts e) p) (hp : p ∉ removed) (i j : Fin k) :
    |((μ (active i)).real (domain origin.cells)/(μ (active i)).real (domain reserve.cells)) *
        intervalValues (physicalCumulative μ active origin) i (intervalLabel cuts e) -
      ((μ (active j)).real (domain origin.cells)/(μ (active j)).real (domain reserve.cells)) *
        intervalValues (physicalCumulative μ active origin) j (intervalLabel cuts e)| ≤
      UpperPayments.cellGap (table active reserve cuts) i j := by
  rw [retained_cell_value μ active origin reserve hreserve hpositive coarse removed hT cuts hzero hmono hsep e p hfit hp i,
    retained_cell_value μ active origin reserve hreserve hpositive coarse removed hT cuts hzero hmono hsep e p hfit hp j]
  exact UpperPayments.difference_le_cellGap _ i j e

end EnvyFreeResearch.Full.RefinedUpperStability
