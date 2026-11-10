import EnvyFreeResearch.Full.RefinedUpperPreparationWitnesses
import EnvyFreeResearch.Full.RefinedUpperPreparationRetained

/-! Physical logical witnesses from the actual maximum-determinant loop. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
open UpperRepresentatives UpperWitnessExtraction UpperLogicalPreparation RefinedUpperPeeling
variable {Index Row Cell Parent : Type*} [Fintype Index] [DecidableEq Parent]

theorem picked_controls_reserve (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (jobs : Index → Row × Row) (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (fallback : Cell) (reserve : Finset Cell)
    (hreserve : ∀ c ∈ reserve, c ∈ cells ∧ parent c ∉ final) (i : Index) :
    reserveGap values normalizer reserve (jobs i).1 (jobs i).2 / 2 ≤
      |scaledDifference values normalizer (jobs i).1 (jobs i).2 (picked values normalizer jobs pairs fallback i)| := by
  rw [picked_eq_selected values normalizer jobs pairs fallback hlength]
  exact selected_controls_reserve values hnonneg normalizer parent cells jobs removed pairs final hexec hlength reserve hreserve i

theorem picked_parent_mem_final (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (jobs : Index → Row × Row) (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (fallback : Cell) (i : Index) :
    parent (picked values normalizer jobs pairs fallback i) ∈ final := by
  rw [picked_eq_selected values normalizer jobs pairs fallback hlength]
  have hr := indexed_represents values hnonneg parent cells jobs removed pairs final hexec hlength i
  rcases selected_mem_pair values normalizer jobs pairs hlength i with h | h
  · rw [h]
    exact hr.2.2.1
  · rw [h]
    exact hr.2.2.2.1

/-- Actual logical witness cells from different rounds have distinct parents
and are physically disjoint, even when a cell crosses old joins. -/
theorem picked_cells_disjoint (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (fine : Cell → Set ℝ) (coarse : Parent → Set ℝ)
    (hcontain : ∀ c, fine c ⊆ coarse (parent c))
    (hcoarse : Pairwise (fun p q => Disjoint (coarse p) (coarse q)))
    (jobs : Index → Row × Row) (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (fallback : Cell) :
    Pairwise (fun i j => Disjoint (fine (picked values normalizer jobs pairs fallback i))
      (fine (picked values normalizer jobs pairs fallback j))) := by
  simp_rw [picked_eq_selected values normalizer jobs pairs fallback hlength]
  intro i j hij
  have hinj := selected_parents_injective values hnonneg normalizer parent cells jobs removed pairs final hexec hlength
  exact (hcoarse (fun h => hij (hinj h))).mono (hcontain _) (hcontain _)


end EnvyFreeResearch.Full.RefinedUpperPreparation
