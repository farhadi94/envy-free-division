import EnvyFreeResearch.Full.UpperWitnessExtraction
import EnvyFreeResearch.Full.UpperChoreIsolation

/-!
# Prepared Repair isolation from the actual representative execution

The full job/repetition list is explicit. Witnesses, normalized cached rows,
and reserve discrepancy maxima are computed from the returned list, and the
cake/chore isolation conclusions no longer assume a witness-gap certificate.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperPreparedIsolation

open UpperRepresentatives UpperRepresentativeSupply UpperRecordedDomain
  UpperWitnessExtraction UpperRepairJobs UpperSeedMatrix UpperAssignmentIsolation
  UpperThresholdProduct UpperChoreIsolation UpperPhysicalSeeds

variable {Cell Parent : Type*} [DecidableEq Parent] {k L : ℕ}

abbrev Round (k L : ℕ) := Job k × Fin L

def rows : Round k L → Fin k × Fin k := fun r => r.1.1.1

def chosen (values : Fin k → Cell → ℝ) (normalizer : Fin k → ℝ)
    (pairs : List (Cell × Cell)) (hlength : pairs.length = Fintype.card (Round k L))
    (job : Job k) (a : Fin L) : Cell := selected values normalizer rows pairs hlength (job, a)

def weights (values : Fin k → Cell → ℝ) (normalizer : Fin k → ℝ)
    (pairs : List (Cell × Cell)) (hlength : pairs.length = Fintype.card (Round k L))
    (job : Job k) (a : Fin L) (row : Fin k) : ℝ :=
  normalizer row * values row (chosen values normalizer pairs hlength job a)

theorem witness_gaps (values : Fin k → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (normalizer : Fin k → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs (rows (k := k) (L := L))) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card (Round k L)) (reserve : Finset Cell)
    (hreserve : ∀ c ∈ reserve, c ∈ cells ∧ parent c ∉ final) (job : Job k) (a : Fin L) :
    reserveGap values normalizer reserve job.1.1.1 job.1.1.2 / 3 ≤
      |weights values normalizer pairs hlength job a job.1.1.1 -
        weights values normalizer pairs hlength job a job.1.1.2| :=
  selected_controls_reserve values hnonneg normalizer parent cells rows removed pairs final
    hexec hlength reserve hreserve (job, a)

/-- Both assignment-isolation inequalities follow from the actual
representative-loop result and successful reserve exclusion. -/
theorem cake_chore_isolation (hk : 2 ≤ k) (values : Fin k → Cell → ℝ)
    (hnonneg : ∀ r c, 0 ≤ values r c) (normalizer : Fin k → ℝ)
    (parent : Cell → Parent) (cells : List Cell) (removed : Finset Parent)
    (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs (rows (k := k) (L := L))) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card (Round k L)) (reserve : Finset Cell)
    (hreserve : ∀ c ∈ reserve, c ∈ cells ∧ parent c ∉ final)
    (old : Fin k → Fin k → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    let S := system hk (weights values normalizer pairs hlength)
    let A := reserveGap values normalizer reserve
    let bound := ENNReal.ofReal ((k : ℝ)^2 * (k - 1 : ℝ) *
      (12 * lam * Real.log (2 * k) + 1) / (L + 1 : ℕ))
    tapeLaw (jobCount k - 1 + 1) L {draw | ∃ transfer : Equiv.Perm (Fin k),
      0 < margin (UpperSeedMatrix.matrix S old draw) A lam transfer} ≤ bound ∧
    tapeLaw (jobCount k - 1 + 1) L {draw | ∃ transfer : Equiv.Perm (Fin k),
      0 < margin (fun i j => -UpperSeedMatrix.matrix S old draw i j) A lam transfer} ≤ bound := by
  dsimp only
  have hgap := witness_gaps values hnonneg normalizer parent cells removed pairs final hexec
    hlength reserve hreserve
  exact ⟨isolation_probability hk _ old _ (reserveGap_nonnegative values normalizer reserve)
      (reserveGap_symmetric values normalizer reserve) lam hlam hgap,
    chore_isolation_probability hk _ old _ (reserveGap_nonnegative values normalizer reserve)
      (reserveGap_symmetric values normalizer reserve) lam hlam hgap⟩

def witnessComponents (hk : 2 ≤ k) (values : Fin k → Cell → ℝ) (normalizer : Fin k → ℝ)
    (fine : Cell → Component) (pairs : List (Cell × Cell))
    (hlength : pairs.length = Fintype.card (Round k L)) :
    Fin (jobCount k - 1 + 1) → Fin L → Component :=
  fun job a => fine (chosen values normalizer pairs hlength (jobEquiv hk job) a)

theorem witnessComponents_disjoint (hk : 2 ≤ k) (values : Fin k → Cell → ℝ)
    (hnonneg : ∀ r c, 0 ≤ values r c) (normalizer : Fin k → ℝ)
    (parent : Cell → Parent) (cells : List Cell) (fine : Cell → Component)
    (coarse : Parent → Component) (hcontain : ∀ c, (fine c).carrier ⊆ (coarse (parent c)).carrier)
    (hcoarse : Pairwise (fun p q => Disjoint (coarse p).carrier (coarse q).carrier))
    (removed : Finset Parent) (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells (roundJobs (rows (k := k) (L := L))) removed = some (pairs, final))
    (hlength : pairs.length = Fintype.card (Round k L)) :
    DisjointCells (witnessComponents hk values normalizer fine pairs hlength) := by
  intro p q hpq
  have h := selected_cells_disjoint values hnonneg normalizer parent cells fine coarse hcontain
    hcoarse rows removed pairs final hexec hlength
  apply h (i := (jobEquiv hk p.1, p.2)) (j := (jobEquiv hk q.1, q.2))
  intro heq
  apply hpq
  apply Prod.ext
  · exact (jobEquiv hk).injective (congrArg Prod.fst heq)
  · exact congrArg (fun z : Job k × Fin L => z.2) heq

/-- The normalized cache is the actual measure obtained by scaling each
finite observer measure; no affine value identity is assumed here. -/
theorem normalized_witness_cache (cost : Fin k → Measure ℝ) (hk : 2 ≤ k)
    (values : Fin k → Cell → ℝ) (normalizer : Fin k → ℝ) (hnormalizer : ∀ i, 0 ≤ normalizer i)
    (fine : Cell → Component) (hvalues : ∀ i c, values i c = (cost i).real (fine c).carrier)
    (pairs : List (Cell × Cell)) (hlength : pairs.length = Fintype.card (Round k L))
    (job : Fin (jobCount k - 1 + 1)) (a : Fin L) (row : Fin k) :
    (system hk (weights values normalizer pairs hlength)).weight job a row =
      (ENNReal.ofReal (normalizer row) • cost row).real
        (witnessComponents hk values normalizer fine pairs hlength job a).carrier := by
  simp [system, weights, witnessComponents, hvalues, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (hnormalizer row)]

/-- End-to-end physical representative supply for the complete job list.
Together with `cake_chore_isolation`, this removes both loop termination and
witness-gap assumptions at the prepared-table boundary. -/
theorem physical_representatives_exist [Fintype Cell] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (fine : Cell → Component) (coarse : Parent → Component) (parent : Cell → Parent)
    (hparent : ∀ c, (fine c).carrier ⊆ (coarse (parent c)).carrier)
    (eta : ℝ) (heta : 0 ≤ eta) (cells : List Cell) (hlisted : ∀ c, c ∈ cells)
    (hnormalized : μ.real (⋃ c, (fine c).carrier) = 1)
    (hsmall : ∀ p, μ.real (coarse p).carrier ≤ eta)
    (values : Fin k → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (removed : Finset Parent)
    (hbudget : ((removed.card + 2 * (jobCount k * L) : ℕ) : ℝ) * eta < 1) :
    ∃ pairs final,
      run values parent cells (roundJobs (rows (k := k) (L := L))) removed = some (pairs, final) ∧
      pairs.length = Fintype.card (Round k L) ∧ removed ⊆ final ∧
        final.card ≤ removed.card + 2 * (jobCount k * L) := by
  have hcard : Fintype.card (Round k L) = jobCount k * L := by
    rw [Fintype.card_prod, job_card, Fintype.card_fin]
  have h := indexed_run_completes μ fine coarse parent hparent eta heta cells hlisted
    hnormalized hsmall values hnonneg (rows (k := k) (L := L)) removed (by simpa [hcard] using hbudget)
  simpa only [hcard] using h

end EnvyFreeResearch.Full.UpperPreparedIsolation
