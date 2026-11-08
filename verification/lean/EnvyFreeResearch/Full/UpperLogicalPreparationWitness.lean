import EnvyFreeResearch.Full.UpperLogicalPreparationSupply
import EnvyFreeResearch.Full.UpperLogicalPreparationState

/-!
# Computed logical witnesses and their separation from the labelled reserve

The actual representative list is read by a total finite indexing rule. On a
completed run it equals the certified indexed extraction, with the same gap
bound and distinct selected parents. Physical cells may be finite unions.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRepresentatives UpperRepresentativeSupply UpperWitnessExtraction

variable {Index Row Cell Parent : Type*} [Fintype Index]

def pairAt (pairs : List (Cell × Cell)) (fallback : Cell) (i : Index) : Cell × Cell :=
  pairs.getD (Fintype.equivFin Index i).val (fallback, fallback)

def picked (values : Row → Cell → ℝ) (normalizer : Row → ℝ) (jobs : Index → Row × Row)
    (pairs : List (Cell × Cell)) (fallback : Cell) (i : Index) : Cell :=
  witness (scaledDifference values normalizer (jobs i).1 (jobs i).2) (pairAt pairs fallback i)

theorem picked_eq_selected (values : Row → Cell → ℝ) (normalizer : Row → ℝ) (jobs : Index → Row × Row)
    (pairs : List (Cell × Cell)) (fallback : Cell) (hlength : pairs.length = Fintype.card Index) (i : Index) :
    picked values normalizer jobs pairs fallback i = selected values normalizer jobs pairs hlength i := by
  unfold picked selected
  congr 1
  exact (List.getElem_eq_getD (l := pairs) (i := (Fintype.equivFin Index i).val)
    (h := by rw [hlength]; exact (Fintype.equivFin Index i).isLt) (fallback, fallback)).symm

theorem pairAt_measurable [MeasurableSpace Cell] {X : Type*} [MeasurableSpace X]
    (pairs : X → List (Cell × Cell)) (hpairs : Measurable pairs) (fallback : Cell) (i : Index) :
    Measurable (fun z => pairAt (pairs z) fallback i) := by
  have h := ProtocolMeasurable.measurable_option_cases
    (present := fun (_ : X) (pair : Cell × Cell) => pair)
    (absent := fun _ => (fallback, fallback))
    ((ProtocolMeasurable.measurable_list_getElem (Fintype.equivFin Index i).val).comp hpairs)
    measurable_snd measurable_const
  convert h using 1
  funext z
  unfold pairAt
  rw [List.getD_eq_getElem?_getD]
  dsimp only [Function.comp_def]
  cases (pairs z)[(Fintype.equivFin Index i).val]? <;> rfl

theorem picked_measurable [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    {X : Type*} [MeasurableSpace X] (values : X → Row → Cell → ℝ) (normalizer : X → Row → ℝ)
    (jobs : Index → Row × Row) (pairs : X → List (Cell × Cell)) (fallback : Cell)
    (hvalues : ∀ r c, Measurable (fun z => values z r c))
    (hnormalizer : ∀ r, Measurable (fun z => normalizer z r)) (hpairs : Measurable pairs) (i : Index) :
    Measurable (fun z => picked (values z) (normalizer z) jobs (pairs z) fallback i) := by
  exact witness_measurable _ (fun c =>
    ((hnormalizer _).mul (hvalues _ c)).sub ((hnormalizer _).mul (hvalues _ c))) _
    (pairAt_measurable pairs hpairs fallback i)

variable [DecidableEq Parent]

theorem picked_controls_reserve (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (jobs : Index → Row × Row) (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (fallback : Cell) (reserve : Finset Cell)
    (hreserve : ∀ c ∈ reserve, c ∈ cells ∧ parent c ∉ final) (i : Index) :
    reserveGap values normalizer reserve (jobs i).1 (jobs i).2 / 3 ≤
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

omit [Fintype Index] [DecidableEq Parent] in
theorem parent_disjoint_labelled (coarse : Parent → Set ℝ)
    (hcoarse : Pairwise (fun p q => Disjoint (coarse p) (coarse q)))
    (theta : I) (labels : Parent → I) (p : Parent) (hp : ¬labels p ≤ theta) :
    Disjoint (coarse p) (labelledUnion coarse theta labels) := by
  apply disjoint_iUnion_right.mpr
  intro q
  by_cases hq : labels q ≤ theta
  · simp only [hq, ite_true]
    exact hcoarse (fun h => hp (h ▸ hq))
  · simp only [hq, ite_false]
    exact disjoint_bot_right

/-- Passing the separate selected-parent label check makes every extracted
witness disjoint from the frozen reserve. -/
theorem picked_disjoint_reserve (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (fine : Cell → Set ℝ) (coarse : Parent → Set ℝ)
    (hcontain : ∀ c, fine c ⊆ coarse (parent c))
    (hcoarse : Pairwise (fun p q => Disjoint (coarse p) (coarse q)))
    (jobs : Index → Row × Row) (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (fallback : Cell)
    (theta : I) (labels : Parent → I) (hpass : ∀ p ∈ final, ¬labels p ≤ theta) (i : Index) :
    Disjoint (fine (picked values normalizer jobs pairs fallback i)) (labelledUnion coarse theta labels) :=
  (parent_disjoint_labelled coarse hcoarse theta labels _
    (hpass _ (picked_parent_mem_final values hnonneg normalizer parent cells jobs removed pairs final hexec hlength fallback i))).mono_left
      (hcontain _)

omit [Fintype Index] in
theorem selected_parent_failure [Fintype Parent] (final : Finset Parent) (theta : I) (rounds : ℕ)
    (hcard : final.card ≤ 2 * rounds) :
    UpperReserve.labelLaw {labels | ∃ p ∈ final, labels p ≤ theta} ≤
      ENNReal.ofReal (2 * rounds * (theta : ℝ)) := by
  have heq : {labels : Parent → I | ∃ p ∈ final, labels p ≤ theta} =
      ⋃ p ∈ final, {labels | labels p ≤ theta} := by ext labels; simp
  rw [heq]
  apply (UpperReserve.selected_parent_probability final theta).trans
  apply ENNReal.ofReal_le_ofReal
  have hc : (final.card : ℝ) ≤ 2 * rounds := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hc theta.property.1

end EnvyFreeResearch.Full.UpperLogicalPreparation
