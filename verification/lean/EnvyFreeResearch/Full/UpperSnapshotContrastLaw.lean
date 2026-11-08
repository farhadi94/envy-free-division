import EnvyFreeResearch.Full.UpperLogicalIsolation

/-! An actual measure-preserving relabeling of seed columns and threshold
coordinates. The independent fresh tape is not conditioned on success. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
open UpperLogicalIsolation UpperRepairJobs UpperBatchPermutation UpperThresholdProduct UpperSeedProbability
variable {k L : ℕ}

def columnPermutation (sigma : Equiv.Perm (Fin k)) : Equiv.Perm (Job k) where
  toFun := permuteJob sigma
  invFun := permuteJob sigma.symm
  left_inv j := by rcases j with ⟨p, c⟩; simp [permuteJob]
  right_inv j := by rcases j with ⟨p, c⟩; simp [permuteJob]

def coordinatePermutation (hk : 2 ≤ k) (sigma : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (jobCount k - 1 + 1)) :=
  (jobEquiv hk).trans ((columnPermutation sigma).trans (jobEquiv hk).symm)

theorem coordinate_job (hk : 2 ≤ k) (sigma : Equiv.Perm (Fin k)) (j : Fin (jobCount k - 1 + 1)) :
    jobEquiv hk (coordinatePermutation hk sigma j) = permuteJob sigma (jobEquiv hk j) := by
  simp only [coordinatePermutation, Equiv.trans_apply, Equiv.apply_symm_apply, columnPermutation]
  rfl

def reindexThresholds {J L : ℕ} (rho : Equiv.Perm (Fin J)) (t : Fin J → Fin (L + 1)) : Fin J → Fin (L + 1) :=
  fun j => t (rho j)

theorem reindexThresholds_preserves {J L : ℕ} (rho : Equiv.Perm (Fin J)) :
    MeasurePreserving (reindexThresholds (L := L) rho) (tapeLaw J L) (tapeLaw J L) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin J => (thresholdLaw : Measure (Fin (L + 1)))) rho.symm
  convert h using 1
  · funext t j
    simp [reindexThresholds, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  · rfl
  · rfl

def relabel (hk : 2 ≤ k) (sigma : Equiv.Perm (Fin k)) (t : IsolationDraw k L) : IsolationDraw k L :=
  (composeRight sigma t.1, reindexThresholds (coordinatePermutation hk sigma) t.2)

/-- The actual independent uniform column permutation and iid thresholds
remain unchanged in law under the explicit simultaneous relabeling. -/
theorem relabel_preserves (hk : 2 ≤ k) (sigma : Equiv.Perm (Fin k)) :
    MeasurePreserving (relabel (L := L) hk sigma) (isolationLaw k L) (isolationLaw k L) :=
  (uniform_equiv_preserves (composeRight sigma)).prod (reindexThresholds_preserves (coordinatePermutation hk sigma))

end EnvyFreeResearch.Full.UpperSnapshotContrast
