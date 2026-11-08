import EnvyFreeResearch.Full.UpperSnapshotContrastLaw

/-! Relabeling the actual cached seed matrix permutes its columns and
reverses every selected two-column seed contrast under a swap. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
open UpperLogicalIsolation UpperRepairJobs UpperBatchPermutation UpperSeedMatrix
variable {k L : ℕ}

def contrast (V : Fin k → Fin k → ℝ) (i h u v : Fin k) : ℝ := V i u - V h u - V i v + V h v

def seedEntry (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ) (t : IsolationDraw k L) : Fin k → Fin k → ℝ :=
  coreMatrix hk w (fun _ _ => 0) t.1 t.2

def seedContrast (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (i h u v : Fin k) (t : IsolationDraw k L) : ℝ := contrast (seedEntry hk w t) i h u v

theorem weight_relabel (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (sigma pi : Equiv.Perm (Fin k)) (j : Fin (jobCount k - 1 + 1)) (a : Fin L) (i : Fin k) :
    (system hk (permutedWeights w (composeRight sigma pi))).weight j a i =
      (system hk (permutedWeights w pi)).weight (coordinatePermutation hk sigma j) a i := by
  simp only [system, permutedWeights, coordinate_job, permuteJob, composeRight]
  rfl

theorem difference_relabel (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (sigma pi : Equiv.Perm (Fin k)) (j : Fin (jobCount k - 1 + 1)) (a : Fin L) :
    difference (system hk (permutedWeights w (composeRight sigma pi))) j a =
      difference (system hk (permutedWeights w pi)) (coordinatePermutation hk sigma j) a := by
  simp only [difference, system, permutedWeights, coordinate_job, permuteJob, composeRight]
  rfl

theorem rowSeed_relabel (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (sigma pi : Equiv.Perm (Fin k)) (j : Fin (jobCount k - 1 + 1)) (i : Fin k) (threshold : Fin (L + 1)) :
    rowSeed (system hk (permutedWeights w (composeRight sigma pi))) j i threshold =
      rowSeed (system hk (permutedWeights w pi)) (coordinatePermutation hk sigma j) i threshold := by
  have hd := funext (difference_relabel hk w sigma pi j)
  simp only [rowSeed, weight_relabel, hd]

theorem contribution_relabel (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (sigma pi : Equiv.Perm (Fin k)) (draw : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (i c : Fin k) (j : Fin (jobCount k - 1 + 1)) :
    contribution (system hk (permutedWeights w (composeRight sigma pi)))
      (reindexThresholds (coordinatePermutation hk sigma) draw) i c j =
      contribution (system hk (permutedWeights w pi)) draw i (sigma c) (coordinatePermutation hk sigma j) := by
  unfold contribution
  rw [rowSeed_relabel]
  have hc : sigma (jobEquiv hk j).2 = sigma c ↔ (jobEquiv hk j).2 = c := sigma.injective.eq_iff
  simp only [system, coordinate_job, permuteJob, hc, reindexThresholds]
  rfl

/-- This is a direct identity for the finite threshold-selected seed matrix,
not an assumed exchangeability property of its output law. -/
theorem seedEntry_relabel (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (sigma : Equiv.Perm (Fin k)) (t : IsolationDraw k L) (i c : Fin k) :
    seedEntry hk w (relabel hk sigma t) i c = seedEntry hk w t i (sigma c) := by
  unfold seedEntry coreMatrix UpperSeedMatrix.matrix
  simp only [zero_add, relabel, contribution_relabel]
  exact Equiv.sum_comp (coordinatePermutation hk sigma)
    (fun j => contribution (system hk (permutedWeights w t.1)) t.2 i (sigma c) j)

theorem seedContrast_swap (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (i h u v : Fin k) (t : IsolationDraw k L) :
    seedContrast hk w i h u v (relabel hk (Equiv.swap u v) t) = -seedContrast hk w i h u v t := by
  unfold seedContrast contrast
  simp only [seedEntry_relabel, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

theorem full_contrast (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ) (old : Fin k → Fin k → ℝ)
    (i h u v : Fin k) (t : IsolationDraw k L) :
    contrast (coreMatrix hk w old t.1 t.2) i h u v = contrast old i h u v + seedContrast hk w i h u v t := by
  simp only [contrast, seedContrast, seedEntry, coreMatrix, UpperSeedMatrix.matrix]
  ring

theorem contrast_preserved (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ) (old : Fin k → Fin k → ℝ)
    (i h u v : Fin k) (t : IsolationDraw k L) (hseed : 0 ≤ seedContrast hk w i h u v t) :
    contrast old i h u v ≤ contrast (coreMatrix hk w old t.1 t.2) i h u v := by
  rw [full_contrast]
  linarith

end EnvyFreeResearch.Full.UpperSnapshotContrast
