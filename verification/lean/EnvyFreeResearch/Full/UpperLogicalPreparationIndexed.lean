import EnvyFreeResearch.Full.UpperLogicalPreparationWitness
import EnvyFreeResearch.Full.UpperLogicalPreparationSeedState
import EnvyFreeResearch.Full.UpperSeedMatrix

/-!
# Indexed repeated jobs produce the actual seed-system cache

The seed system reads the actual representative loop result. Its signed
weights have the proved witness gap on every surviving reserve cell. The
whole construction is finite and Borel in cached values and normalizers.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRepresentativeSupply UpperWitnessExtraction UpperSeedMatrix UpperRepresentatives

variable {Agent Cell Parent : Type*} [Fintype Agent] {M L : ℕ}

def repeatedJobs (jobs : Fin (M + 1) → Agent × Agent) : (Fin (M + 1) × Fin L) → Agent × Agent :=
  fun index => jobs index.1

def witnessSystem (values : Agent → Cell → ℝ) (normalizer : Agent → ℝ)
    (jobs : Fin (M + 1) → Agent × Agent) (column : Fin (M + 1) → Agent)
    (pairs : List (Cell × Cell)) (fallback : Cell) : SeedSystem Agent M L where
  left := fun j => (jobs j).1
  right := fun j => (jobs j).2
  column := column
  weight := fun j a row => normalizer row * values row
    (picked values normalizer (repeatedJobs (L := L) jobs) pairs fallback (j, a))

def witnessCells (fine : Cell → Set ℝ) (values : Agent → Cell → ℝ) (normalizer : Agent → ℝ)
    (jobs : Fin (M + 1) → Agent × Agent) (pairs : List (Cell × Cell)) (fallback : Cell) :
    Fin (M + 1) → Fin L → Set ℝ :=
  fun j a => fine (picked values normalizer (repeatedJobs (L := L) jobs) pairs fallback (j, a))

theorem witnessSystem_difference (values : Agent → Cell → ℝ) (normalizer : Agent → ℝ)
    (jobs : Fin (M + 1) → Agent × Agent) (column : Fin (M + 1) → Agent)
    (pairs : List (Cell × Cell)) (fallback : Cell) (j : Fin (M + 1)) (a : Fin L) :
    difference (witnessSystem values normalizer jobs column pairs fallback) j a =
      scaledDifference values normalizer (jobs j).1 (jobs j).2
        (picked values normalizer (repeatedJobs (L := L) jobs) pairs fallback (j, a)) := rfl

theorem witnessSystem_weight_measurable [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    {X : Type*} [MeasurableSpace X] (values : X → Agent → Cell → ℝ) (normalizer : X → Agent → ℝ)
    (jobs : Fin (M + 1) → Agent × Agent) (column : Fin (M + 1) → Agent)
    (pairs : X → List (Cell × Cell)) (fallback : Cell)
    (hvalues : ∀ r c, Measurable (fun z => values z r c))
    (hnormalizer : ∀ r, Measurable (fun z => normalizer z r)) (hpairs : Measurable pairs)
    (j : Fin (M + 1)) (a : Fin L) (row : Agent) :
    Measurable (fun z => (witnessSystem (values z) (normalizer z) jobs column (pairs z) fallback).weight j a row) :=
  (hnormalizer row).mul ((score_eval_measurable (fun z => values z row) (hvalues row)).comp
    (measurable_id.prodMk (picked_measurable values normalizer (repeatedJobs (L := L) jobs) pairs fallback hvalues hnormalizer hpairs (j, a))))

variable [Fintype Cell] [DecidableEq Parent]

/-- The actual repeated representative loop completes with the exact number
of indexed witnesses and the required removed-parent bound. -/
theorem repeated_run_completes (weights : Cell → ℝ) (parent : Cell → Parent) (eta : ℝ) (heta : 0 ≤ eta)
    (cells : List Cell) (hlisted : ∀ c, c ∈ cells) (hnormalized : ∑ c, weights c = 1)
    (hsmall : ∀ p, (∑ c, if parent c = p then weights c else 0) ≤ eta)
    (values : Agent → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (jobs : Fin (M + 1) → Agent × Agent) (removed : Finset Parent)
    (hbudget : ((removed.card + 2 * ((M + 1) * L) : ℕ) : ℝ) * eta < 1) :
    ∃ pairs final, run values parent cells (roundJobs (repeatedJobs (L := L) jobs)) removed = some (pairs, final) ∧
      pairs.length = (M + 1) * L ∧ removed ⊆ final ∧ final.card ≤ removed.card + 2 * ((M + 1) * L) := by
  simpa only [roundJobs, List.length_ofFn, Fintype.card_prod, Fintype.card_fin] using
    table_run_completes weights parent eta heta cells hlisted hnormalized hsmall values hnonneg
      (roundJobs (repeatedJobs (L := L) jobs)) removed (by simpa only [roundJobs, List.length_ofFn, Fintype.card_prod, Fintype.card_fin] using hbudget)

/-- All reserve cells survive the representative loop when none of its
selected parents is marked. The witness gap then follows from `run_spec`. -/
theorem witnessSystem_gap (values : Agent → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Agent → ℝ) (parent : Cell → Parent) (cells : List Cell) (hlisted : ∀ c, c ∈ cells)
    (jobs : Fin (M + 1) → Agent × Agent) (column : Fin (M + 1) → Agent)
    (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs (repeatedJobs (L := L) jobs)) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card (Fin (M + 1) × Fin L)) (fallback : Cell)
    (theta : I) (labels : Parent → I) (hpass : ∀ p ∈ final, ¬labels p ≤ theta)
    (j : Fin (M + 1)) (a : Fin L) :
    reserveGap values normalizer (reserveCells parent theta labels) (jobs j).1 (jobs j).2 / 3 ≤
      |difference (witnessSystem values normalizer jobs column pairs fallback) j a| := by
  rw [witnessSystem_difference]
  exact picked_controls_reserve values hnonneg normalizer parent cells (repeatedJobs (L := L) jobs) removed pairs final hexec hlength
    fallback (reserveCells parent theta labels) (fun c hc => ⟨hlisted c, fun hp => hpass _ hp (Finset.mem_filter.mp hc).2⟩) (j, a)

theorem witnessCells_disjoint (fine : Cell → Set ℝ) (coarse : Parent → Set ℝ)
    (values : Agent → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c) (normalizer : Agent → ℝ)
    (parent : Cell → Parent) (cells : List Cell)
    (hcontain : ∀ c, fine c ⊆ coarse (parent c))
    (hcoarse : Pairwise (fun p q => Disjoint (coarse p) (coarse q)))
    (jobs : Fin (M + 1) → Agent × Agent) (removed : Finset Parent)
    (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs (repeatedJobs (L := L) jobs)) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card (Fin (M + 1) × Fin L)) (fallback : Cell) :
    Pairwise (fun p q : Fin (M + 1) × Fin L =>
      Disjoint (witnessCells fine values normalizer jobs pairs fallback p.1 p.2)
        (witnessCells fine values normalizer jobs pairs fallback q.1 q.2)) :=
  picked_cells_disjoint values hnonneg normalizer parent cells fine coarse hcontain hcoarse
    (repeatedJobs (L := L) jobs) removed pairs final hexec hlength fallback

/-- The cached seed weights are the actual raw witness masses divided by the
reserve totals, when the source cache is normalized by the old buffer. -/
theorem witnessSystem_weight_physical (cost : Agent → Measure ℝ) (fine : Cell → Set ℝ)
    (buffer reserve : Agent → ℝ) (hbuffer : ∀ r, buffer r ≠ 0)
    (values : Agent → Cell → ℝ) (hvalues : ∀ r c, values r c = (cost r).real (fine c) / buffer r)
    (jobs : Fin (M + 1) → Agent × Agent) (column : Fin (M + 1) → Agent)
    (pairs : List (Cell × Cell)) (fallback : Cell) (j : Fin (M + 1)) (a : Fin L) (row : Agent) :
    (witnessSystem values (fun r => buffer r / reserve r) jobs column pairs fallback).weight j a row =
      (cost row).real (witnessCells fine values (fun r => buffer r / reserve r) jobs pairs fallback j a) / reserve row := by
  simp only [witnessSystem, hvalues, witnessCells]
  field_simp [hbuffer row]

end EnvyFreeResearch.Full.UpperLogicalPreparation
