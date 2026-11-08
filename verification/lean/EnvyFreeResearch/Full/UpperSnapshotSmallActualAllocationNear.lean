import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationValues
import EnvyFreeResearch.Full.UpperSnapshotSmallSigned

/-! Deterministic consequences of the supported-interpolation event.
These lemmas do not assume or assert the probability of that event. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
variable {Cell : Type*} [Fintype Cell] {J : ℕ}

/-- Cell discrepancy plus the interpolation error controls actual normalized
foreign-vs-cutter mass on every measurable candidate piece. -/
theorem normalized_error_of_interpolation (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (hsum : ∑ e, score e = 0) (piece : Set ℝ) (hp : MeasurableSet piece)
    (foreign cutter eps : ℝ)
    (herror : |foreign-cutter-signedEstimate score cells piece| ≤ eps*(∑ e, |score e|)) :
    |foreign-cutter| ≤ (1/2+eps)*(∑ e, |score e|) := by
  have he := signedEstimate_bound score cells hsum piece hp
  have ht := abs_add_le (foreign-cutter-signedEstimate score cells piece) (signedEstimate score cells piece)
  have hid : foreign-cutter-signedEstimate score cells piece+signedEstimate score cells piece=foreign-cutter := by ring
  rw [hid] at ht
  linarith

/-- Equal cutter shares and a positive cutter buffer turn uniformly small
normalized row errors into the absolute near-EF checks for both cake/chores. -/
theorem near_checks_of_normalized_errors (shares : Fin J → ℝ) (buffer M t beta error tau : ℝ)
    (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 ≤ tau)
    (hsmall : error ≤ beta/2) (hbudget : 2*error ≤ tau*(beta/2))
    (hshares : ∀ j, |shares j/M-t| ≤ error) (hbuffer : |buffer/M-beta| ≤ error) :
    beta/2*M ≤ buffer ∧ 0 < buffer ∧ ∀ i j, |shares i-shares j| ≤ tau*buffer := by
  have hb : (beta-error)*M ≤ buffer := by
    apply (le_div_iff₀ hM).mp
    have h := (abs_le.mp hbuffer).1
    linarith
  have hhalf : beta/2*M ≤ buffer := by nlinarith
  refine ⟨hhalf, (mul_pos (half_pos hbeta) hM).trans_le hhalf, ?_⟩
  intro i j
  have hi := abs_le.mp (hshares i)
  have hj := abs_le.mp (hshares j)
  have his : (t-error)*M ≤ shares i := (le_div_iff₀ hM).mp (by linarith)
  have hib : shares i ≤ (t+error)*M := (div_le_iff₀ hM).mp (by linarith)
  have hjs : (t-error)*M ≤ shares j := (le_div_iff₀ hM).mp (by linarith)
  have hjb : shares j ≤ (t+error)*M := (div_le_iff₀ hM).mp (by linarith)
  have hg : |shares i-shares j| ≤ 2*error*M := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have hscale := mul_le_mul_of_nonneg_right hbudget hM.le
  have hbufscale := mul_le_mul_of_nonneg_left hhalf htau
  apply hg.trans
  nlinarith

end EnvyFreeResearch.Full.UpperSnapshotSmall
