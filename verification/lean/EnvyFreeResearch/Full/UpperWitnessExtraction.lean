import EnvyFreeResearch.Full.UpperRepresentativeSupply
import EnvyFreeResearch.Full.UpperRepairJobs
import EnvyFreeResearch.Full.UpperPhysicalSeeds

/-!
# Indexed witness extraction from the actual representative loop

The finite loop is run in a fixed enumeration of job/repetition indices.
Its actual result list is read at those indices and the larger normalized
pair difference is selected. The reserve discrepancy is a computed finite
maximum, and both its witness gap and physical disjointness follow from the
proved loop invariant.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperWitnessExtraction

open UpperRepresentatives UpperRepresentativeSupply UpperRecordedDomain

variable {Index Row Cell Parent : Type*} [Fintype Index] [DecidableEq Parent]

def roundJobs (jobs : Index → Row × Row) : List (Row × Row) :=
  List.ofFn (fun i : Fin (Fintype.card Index) => jobs ((Fintype.equivFin Index).symm i))

def indexPair (pairs : List (Cell × Cell)) (hlength : pairs.length = Fintype.card Index)
    (i : Index) : Cell × Cell :=
  pairs.get ⟨(Fintype.equivFin Index i).val, by rw [hlength]; exact (Fintype.equivFin Index i).isLt⟩

def scaledDifference (values : Row → Cell → ℝ) (normalizer : Row → ℝ)
    (i h : Row) (c : Cell) : ℝ := normalizer i * values i c - normalizer h * values h c

def selected (values : Row → Cell → ℝ) (normalizer : Row → ℝ) (jobs : Index → Row × Row)
    (pairs : List (Cell × Cell)) (hlength : pairs.length = Fintype.card Index) (i : Index) : Cell :=
  witness (scaledDifference values normalizer (jobs i).1 (jobs i).2) (indexPair pairs hlength i)

def reserveGap (values : Row → Cell → ℝ) (normalizer : Row → ℝ) (reserve : Finset Cell)
    (i h : Row) : ℝ :=
  if hr : reserve.Nonempty then reserve.sup' hr (fun c => |scaledDifference values normalizer i h c|)
  else 0

omit [Fintype Index] [DecidableEq Parent] in
theorem reserveGap_nonnegative (values : Row → Cell → ℝ) (normalizer : Row → ℝ)
    (reserve : Finset Cell) (i h : Row) : 0 ≤ reserveGap values normalizer reserve i h := by
  by_cases hr : reserve.Nonempty
  · rw [reserveGap, dite_eq_left hr]
    obtain ⟨c, hc⟩ := hr
    exact (abs_nonneg (scaledDifference values normalizer i h c)).trans
      (Finset.le_sup' (fun c => |scaledDifference values normalizer i h c|) hc)
  · simp [reserveGap, hr]

omit [Fintype Index] [DecidableEq Parent] in
theorem reserveGap_symmetric (values : Row → Cell → ℝ) (normalizer : Row → ℝ)
    (reserve : Finset Cell) (i h : Row) :
    reserveGap values normalizer reserve i h = reserveGap values normalizer reserve h i := by
  have heq : (fun c => |scaledDifference values normalizer i h c|) =
      fun c => |scaledDifference values normalizer h i c| := by
    funext c
    exact abs_sub_comm _ _
  simp only [reserveGap, heq]

/-- This is an indexed read of the actual returned list; the representation
certificate is obtained from `run_spec`, not supplied for the array. -/
theorem indexed_represents (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (parent : Cell → Parent) (cells : List Cell) (jobs : Index → Row × Row)
    (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (i : Index) :
    Represents values parent cells final (jobs i) (indexPair pairs hlength i) := by
  have hrep := (run_spec values hnonneg parent cells (roundJobs jobs) removed pairs final hexec).2.2.2
  have hjobs : (Fintype.equivFin Index i).val < (roundJobs jobs).length := by
    simp [roundJobs]
  have hpairs : (Fintype.equivFin Index i).val < pairs.length := by
    simp [hlength]
  have h := hrep.get hjobs hpairs
  simpa [roundJobs, indexPair, List.get_ofFn] using h

theorem selected_mem_pair (values : Row → Cell → ℝ) (normalizer : Row → ℝ)
    (jobs : Index → Row × Row) (pairs : List (Cell × Cell))
    (hlength : pairs.length = Fintype.card Index) (i : Index) :
    selected values normalizer jobs pairs hlength i = (indexPair pairs hlength i).1 ∨
      selected values normalizer jobs pairs hlength i = (indexPair pairs hlength i).2 :=
  witness_mem _ _

theorem selected_parent_mem (values : Row → Cell → ℝ) (normalizer : Row → ℝ)
    (parent : Cell → Parent) (jobs : Index → Row × Row) (pairs : List (Cell × Cell))
    (hlength : pairs.length = Fintype.card Index) (i : Index) :
    parent (selected values normalizer jobs pairs hlength i) ∈
      pairParents parent (indexPair pairs hlength i) := by
  rcases selected_mem_pair values normalizer jobs pairs hlength i with h | h <;>
    simp [h, pairParents]

/-- Every surviving reserve cell is controlled by the extracted witness
after arbitrary row normalization. -/
theorem selected_controls_reserve (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (jobs : Index → Row × Row) (removed : Finset Parent)
    (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (reserve : Finset Cell)
    (hreserve : ∀ c ∈ reserve, c ∈ cells ∧ parent c ∉ final) (i : Index) :
    reserveGap values normalizer reserve (jobs i).1 (jobs i).2 / 3 ≤
      |scaledDifference values normalizer (jobs i).1 (jobs i).2
        (selected values normalizer jobs pairs hlength i)| := by
  have hrep := indexed_represents values hnonneg parent cells jobs removed pairs final hexec hlength i
  have heach (c : Cell) (hc : c ∈ reserve) :
      |scaledDifference values normalizer (jobs i).1 (jobs i).2 c| ≤
        3 * |scaledDifference values normalizer (jobs i).1 (jobs i).2
          (selected values normalizer jobs pairs hlength i)| := by
    rw [selected, witness_abs]
    exact hrep.2.2.2.2 c (hreserve c hc).1 (hreserve c hc).2 _ _
  have hbound : reserveGap values normalizer reserve (jobs i).1 (jobs i).2 ≤
      3 * |scaledDifference values normalizer (jobs i).1 (jobs i).2
        (selected values normalizer jobs pairs hlength i)| := by
    by_cases hr : reserve.Nonempty
    · rw [reserveGap, dite_eq_left hr]
      exact Finset.sup'_le hr _ heach
    · simp only [reserveGap, hr, dite_eq_right, not_false_eq_true]
      positivity
  linarith

theorem indexed_parents_disjoint (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (parent : Cell → Parent) (cells : List Cell) (jobs : Index → Row × Row)
    (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) :
    Pairwise (fun i j => Disjoint (pairParents parent (indexPair pairs hlength i))
      (pairParents parent (indexPair pairs hlength j))) := by
  have hp := (run_spec values hnonneg parent cells (roundJobs jobs) removed pairs final hexec).2.2.1
  intro i j hij
  have hne : Fintype.equivFin Index i ≠ Fintype.equivFin Index j :=
    fun h => hij ((Fintype.equivFin Index).injective h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hp.rel_get_of_lt (a := ⟨_, by rw [hlength]; exact (Fintype.equivFin Index i).isLt⟩)
      (b := ⟨_, by rw [hlength]; exact (Fintype.equivFin Index j).isLt⟩) hlt
  · exact (hp.rel_get_of_lt (a := ⟨_, by rw [hlength]; exact (Fintype.equivFin Index j).isLt⟩)
      (b := ⟨_, by rw [hlength]; exact (Fintype.equivFin Index i).isLt⟩) hgt).symm

/-- Extracted witnesses from distinct rounds have distinct coarse parents. -/
theorem selected_parents_injective (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (jobs : Index → Row × Row) (removed : Finset Parent)
    (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) :
    Function.Injective (fun i => parent (selected values normalizer jobs pairs hlength i)) := by
  intro i j heq
  by_contra hne
  have hd := indexed_parents_disjoint values hnonneg parent cells jobs removed pairs final hexec hlength hne
  have hi := selected_parent_mem values normalizer parent jobs pairs hlength i
  have hj := selected_parent_mem values normalizer parent jobs pairs hlength j
  apply Finset.disjoint_left.mp hd hi
  change parent (selected values normalizer jobs pairs hlength i) =
    parent (selected values normalizer jobs pairs hlength j) at heq
  rw [heq]
  exact hj

/-- Physical disjointness follows from the actual selected parents and the
recorded fine-cell containment invariant. -/
theorem selected_cells_disjoint (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Row → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (fine : Cell → Component) (coarse : Parent → Component)
    (hcontain : ∀ c, (fine c).carrier ⊆ (coarse (parent c)).carrier)
    (hcoarse : Pairwise (fun p q => Disjoint (coarse p).carrier (coarse q).carrier))
    (jobs : Index → Row × Row) (removed : Finset Parent)
    (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs jobs) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) :
    Pairwise (fun i j => Disjoint (fine (selected values normalizer jobs pairs hlength i)).carrier
      (fine (selected values normalizer jobs pairs hlength j)).carrier) := by
  intro i j hij
  have hinj := selected_parents_injective values hnonneg normalizer parent cells jobs removed pairs final hexec hlength
  exact (hcoarse (fun h => hij (hinj h))).mono (hcontain _) (hcontain _)

/-- The actual finite loop succeeds for the complete indexed list under
the physical parent-mass budget. -/
theorem indexed_run_completes [Fintype Cell] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (fine : Cell → Component) (coarse : Parent → Component) (parent : Cell → Parent)
    (hparent : ∀ c, (fine c).carrier ⊆ (coarse (parent c)).carrier)
    (eta : ℝ) (heta : 0 ≤ eta) (cells : List Cell) (hlisted : ∀ c, c ∈ cells)
    (hnormalized : μ.real (⋃ c, (fine c).carrier) = 1)
    (hsmall : ∀ p, μ.real (coarse p).carrier ≤ eta)
    (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (jobs : Index → Row × Row) (removed : Finset Parent)
    (hbudget : ((removed.card + 2 * Fintype.card Index : ℕ) : ℝ) * eta < 1) :
    ∃ pairs final, run values parent cells (roundJobs jobs) removed = some (pairs, final) ∧
      pairs.length = Fintype.card Index ∧ removed ⊆ final ∧
        final.card ≤ removed.card + 2 * Fintype.card Index := by
  simpa [roundJobs] using run_completes μ fine coarse parent hparent eta heta cells hlisted
    hnormalized hsmall values hnonneg (roundJobs jobs) removed (by simpa [roundJobs] using hbudget)

end EnvyFreeResearch.Full.UpperWitnessExtraction
