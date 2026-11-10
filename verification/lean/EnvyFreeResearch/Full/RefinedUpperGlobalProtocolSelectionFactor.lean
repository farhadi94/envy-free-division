import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalBudgetAdapter
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionData

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows GlobalCompletion
open RefinedUpperGlobal.Transfer
variable {n : ℕ}

theorem transfer_tau_le_one (hn : 2≤n) : RefinedUpperRepair.nearError n ≤ 1 := by
  have ht := RefinedUpperShrink.nearError_positive n
  have hh := RefinedUpperShrink.population_nearError_le_two n n le_rfl
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  nlinarith

theorem transfer_theta_le_one (hn : 2≤n) : RefinedUpperShrinkPrecision.theta n ≤ 1 := by
  have ht := transfer_tau_le_one hn
  have hfn : 1≤RefinedUpperRepair.fine n :=
    RefinedUpperGlobalBudgetAdapter.fine_positive n
  have hf1 : (1:ℝ)≤RefinedUpperRepair.fine n := by exact_mod_cast hfn
  apply (div_le_one (show 0<(768:ℝ)*RefinedUpperRepair.fine n by positivity)).mpr
  nlinarith

theorem firstFactor_range (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hk : 2≤p.anchor.active.card) (direction : Direction) :
    1≤p.firstFactor direction ∧ p.firstFactor direction ≤
      (2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1) := by
  have hn : 2≤n := hk.trans (active_size_bound _)
  have htheta := RefinedUpperShrinkPrecision.theta_positive n
  have htau := RefinedUpperShrink.nearError_positive n
  have htau1 := transfer_tau_le_one hn
  have hbase : 1≤2/RefinedUpperShrinkPrecision.theta n := (le_div_iff₀ htheta).mpr (by linarith [transfer_theta_le_one hn])
  exact ⟨hbase.trans (factor_lower htheta htau htau1 _),factor_at_most_last _ htheta htau htau1⟩

theorem firstFactor_safe (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hk : 2≤p.anchor.active.card) (direction : Direction)
    (hpositive : ∀ i, 0<p.localBuffer i) (hEF : ∀ i j, 0≤p.localGap direction i j) :
    ∀ i, p.firstFactor direction*(p.localGap direction i (activeIndex p.anchor.active p.target)/p.localBuffer i)
      ≤ 3*RefinedUpperRepair.nearError n/8 ∨
      2≤p.firstFactor direction*(p.localGap direction i (activeIndex p.anchor.active p.target)/p.localBuffer i) := by
  exact factorIndex_safe _ _ _ _ (RefinedUpperShrinkPrecision.theta_positive n) (RefinedUpperShrink.nearError_positive n)
    (transfer_tau_le_one (hk.trans (active_size_bound _)))
    (fun i => div_nonneg (hEF i _) (hpositive i).le) (by rw [localGap_self,zero_div])

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
