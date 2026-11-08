import EnvyFreeResearch.Full.UpperLogicalPreparationGuard
import EnvyFreeResearch.Full.UpperBatchPermutation

/-! Pure finite cached seed computations and physical threshold unions. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperLogicalPreparation UpperSeedMatrix UpperRepairJobs UpperBatchPermutation

variable {Cell Parent : Type*} {k L M : ℕ}

def coreChosen (values : Fin k → Cell → ℝ) (normalizer : Fin k → ℝ)
    (pairs : List (Cell × Cell)) (fallback : Cell) (job : Job k) (a : Fin L) : Cell :=
  picked values normalizer UpperPreparedIsolation.rows pairs fallback (job, a)

def coreWeights (values : Fin k → Cell → ℝ) (normalizer : Fin k → ℝ)
    (pairs : List (Cell × Cell)) (fallback : Cell) (job : Job k) (a : Fin L) (i : Fin k) : ℝ :=
  normalizer i * values i (coreChosen values normalizer pairs fallback job a)

def permuteJob (pi : Equiv.Perm (Fin k)) (job : Job k) : Job k := (job.1, pi job.2)

theorem permuteJob_injective (pi : Equiv.Perm (Fin k)) : Function.Injective (permuteJob pi) := by
  rintro ⟨p, a⟩ ⟨r, b⟩ h
  simp only [permuteJob, Prod.mk.injEq] at h
  exact Prod.ext h.1 (pi.injective h.2)

def permutedCells (hk : 2 ≤ k) (witness : Job k → Fin L → Set ℝ) (pi : Equiv.Perm (Fin k)) :
    Fin (jobCount k - 1 + 1) → Fin L → Set ℝ :=
  fun j a => witness (permuteJob pi (jobEquiv hk j)) a

theorem permutedCells_disjoint (hk : 2 ≤ k) (witness : Job k → Fin L → Set ℝ)
    (hdisjoint : Pairwise (fun p q : Job k × Fin L => Disjoint (witness p.1 p.2) (witness q.1 q.2)))
    (pi : Equiv.Perm (Fin k)) : Seeds.DisjointCells (permutedCells hk witness pi) := by
  intro p q hpq
  apply hdisjoint (i := (permuteJob pi (jobEquiv hk p.1), p.2))
    (j := (permuteJob pi (jobEquiv hk q.1), q.2))
  intro he
  apply hpq
  exact Prod.ext ((jobEquiv hk).injective (permuteJob_injective pi (congrArg (fun z : Job k × Fin L => z.1) he)))
    (congrArg (fun z : Job k × Fin L => z.2) he)

def seedUnion (S : SeedSystem (Fin k) M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) : Set ℝ := ⋃ j, Seeds.seed S cells draw j

theorem seed_mass_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : SeedSystem (Fin k) M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (cap : ℝ) (hcap : ∀ j a, μ.real (cells j a) ≤ cap)
    (draw : Fin (M + 1) → Fin (L + 1)) (j : Fin (M + 1)) :
    μ.real (Seeds.seed S cells draw j) ≤ L * cap := by
  calc
    _ ≤ μ.real (⋃ a, cells j a) := measureReal_mono (Seeds.seed_subset S cells draw j)
    _ ≤ ∑ a, μ.real (cells j a) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : Fin L, cap := Finset.sum_le_sum (fun a _ => hcap j a)
    _ = L * cap := by simp

/-- Every threshold choice spends at most one cell per job/repetition. This
raw-mass estimate does not require a successful isolation or correction. -/
theorem seedUnion_mass_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : SeedSystem (Fin k) M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (cap : ℝ) (hcap : ∀ j a, μ.real (cells j a) ≤ cap)
    (draw : Fin (M + 1) → Fin (L + 1)) :
    μ.real (seedUnion S cells draw) ≤ (M + 1 : ℕ) * L * cap := by
  calc
    _ ≤ ∑ j, μ.real (Seeds.seed S cells draw j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin (M + 1), (L : ℝ) * cap :=
      Finset.sum_le_sum (fun j _ => seed_mass_le μ S cells cap hcap draw j)
    _ = (M + 1 : ℕ) * L * cap := by simp [mul_assoc]

theorem seedUnion_subset (S : SeedSystem (Fin k) M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (buffer : Set ℝ) (hsub : ∀ j a, cells j a ⊆ buffer)
    (draw : Fin (M + 1) → Fin (L + 1)) : seedUnion S cells draw ⊆ buffer := by
  exact iUnion_subset (fun j => (Seeds.seed_subset S cells draw j).trans (iUnion_subset (hsub j)))

theorem seedUnion_disjoint (S : SeedSystem (Fin k) M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (reserve : Set ℝ) (hdis : ∀ j a, Disjoint (cells j a) reserve)
    (draw : Fin (M + 1) → Fin (L + 1)) : Disjoint (seedUnion S cells draw) reserve := by
  exact disjoint_iUnion_left.mpr (fun j =>
    (disjoint_iUnion_left.mpr (hdis j)).mono_left (Seeds.seed_subset S cells draw j))

/-- The literal package realizes the normalized matrix, including its old
recorded endowment, by scaling finite observer measures. -/
theorem normalized_package_mass (cost : Fin k → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (reserve : Fin k → ℝ) (hreserve : ∀ i, 0 ≤ reserve i)
    (S : SeedSystem (Fin k) M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (hmeas : ∀ j a, MeasurableSet (cells j a)) (hdisjoint : Seeds.DisjointCells cells)
    (old : Fin k → Set ℝ) (hold : ∀ c j a, Disjoint (old c) (cells j a))
    (hcache : ∀ j a i, S.weight j a i = (cost i).real (cells j a) / reserve i)
    (draw : Fin (M + 1) → Fin (L + 1)) (i c : Fin k) :
    (cost i).real (Seeds.package S cells old draw c) / reserve i =
      matrix S (fun r d => (cost r).real (old d) / reserve r) draw i c := by
  let normalized := fun i => ENNReal.ofReal (1 / reserve i) • cost i
  let : ∀ i, IsFiniteMeasure (normalized i) := fun i => (cost i).smul_finite ENNReal.ofReal_ne_top
  have hscale (r : Fin k) (E : Set ℝ) : (normalized r).real E = (cost r).real E / reserve r := by
    simp only [normalized, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (one_div_nonneg.mpr (hreserve r))]
    ring
  have hc : ∀ j a r, S.weight j a r = (normalized r).real (cells j a) := by
    intro j a r
    rw [hscale]
    exact hcache j a r
  have h := Seeds.package_mass normalized S cells hmeas hdisjoint old hold hc draw i c
  simpa only [hscale] using h

end EnvyFreeResearch.Full.UpperLogicalIsolation
