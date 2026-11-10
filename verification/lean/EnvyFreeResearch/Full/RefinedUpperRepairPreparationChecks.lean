import EnvyFreeResearch.Full.RefinedUpperRepairTargets
import EnvyFreeResearch.Full.RefinedUpperRepairSeedIndices
import EnvyFreeResearch.Full.RefinedUpperPreparationBudget
import EnvyFreeResearch.Full.UpperRepairPreparationChecks

/-! Physical correction checks derived from actual deterministic preparation
and the original near-envy-free input, without a probabilistic mass guard. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairPreparationChecks
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperLogicalIsolation RefinedUpperPreparation UpperRepairJobs
  UpperIdealPayments UpperPreparedEnvelopeMean UpperRepairPreparationChecks
variable {n k : ℕ} [Nonempty (Fin k)]

def nearBudget (k q L : ℕ) (tau : ℝ) : ℝ := 2*tau+k.choose 2*L*(2/(q+1 : ℝ))
def targetBudget (k q L : ℕ) (tau eta lam : ℝ) : ℝ :=
  k*nearBudget k q L tau+(k-1 : ℕ)*(2*lam*eta)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

lemma data_wellFormed (q m L : ℕ) (draw : Fin m → Fin k × I) :
    WellFormed μ (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L) := by
  rw [dataRetained_execute]
  exact retainedState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw _

lemma data_positive (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 4*(jobCount k*L) ≤ q+1) (i : Fin k) :
    0 < (μ (active i)).real (domain
      (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L).cells) :=
  (div_pos (hpositive i) (by norm_num : (0 : ℝ) < 2)).trans_le
    (dataRetained_half μ policy hpolicy active origin hgood hpositive q m L draw hbudget i)

lemma data_small (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 4*(jobCount k*L) ≤ q+1) (i : Fin k)
    (e : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q+m+1)) :
    UpperCorrectionSetup.table active
      (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L)
      (UpperGridData.cuts (UpperGridMerge.prepare policy active origin q m draw)) i e ≤ 2/(q+1 : ℝ) := by
  have hb : 2*(jobCount k*L) < q+1 := by omega
  have hs := (dataResult_spec μ policy hpolicy active origin hgood hpositive q m L draw hb).2.2
  rw [dataRetained_execute]
  exact retainedState_table_cap μ policy hpolicy active origin hgood hpositive q m draw _ (by omega) i e

lemma data_disagreement_bound (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 4*(jobCount k*L) ≤ q+1) (eta : ℝ) (hcell : 2/(q+1 : ℝ) ≤ eta) (i j : Fin k) :
    dataDisagreement active origin (UpperGridMerge.prepare policy active origin q m draw) L i j ≤ eta := by
  apply UpperPayments.cellGap_le _ _ ((by positivity : (0 : ℝ) ≤ 2/(q+1 : ℝ)).trans hcell) _ _ i j
  · exact fun r e => UpperCorrectionSetup.table_nonneg μ active _
      (data_wellFormed μ policy hpolicy active origin hgood hpositive q m L draw) _
      (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
      (UpperCommonGrid.grid_monotone _)
      (reserveState_separated policy active origin q m draw 0 _)
      (data_positive μ policy hpolicy active origin hgood hpositive q m L draw hbudget) r e
  · intro r e
    exact (data_small μ policy hpolicy active origin hgood hpositive q m L draw hbudget r e).trans hcell

lemma normalized_old_near (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 4*(jobCount k*L) ≤ q+1)
    (tau : ℝ) (htau : 0 ≤ tau) (i j d : Fin k)
    (hnear : (μ (active i)).real (domain (old j).cells)-(μ (active i)).real (domain (old d).cells) ≤
      tau*(μ (active i)).real (domain origin.cells)) :
    oldMatrix active old (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L) i j-
      oldMatrix active old (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L) i d ≤ 2*tau := by
  unfold oldMatrix
  rw [total_correct μ (old j) (hold j),total_correct μ (old d) (hold d),
    total_correct μ _ (data_wellFormed μ policy hpolicy active origin hgood hpositive q m L draw),← sub_div]
  apply (div_le_iff₀ (data_positive μ policy hpolicy active origin hgood hpositive q m L draw hbudget i)).mpr
  have hh := dataRetained_half μ policy hpolicy active origin hgood hpositive q m L draw hbudget i
  have hm := mul_le_mul_of_nonneg_left (show (μ (active i)).real (domain origin.cells) ≤
    2*(μ (active i)).real (domain (dataRetained active origin
      (UpperGridMerge.prepare policy active origin q m draw) L).cells) by linarith) htau
  nlinarith

lemma actual_targets (hk : 2 ≤ k) (chores : Bool) (old : Fin k → State n)
    (hold : ∀ c, WellFormed μ (old c)) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hparent : 4*(jobCount k*L) ≤ q+1) (tau eta lam : ℝ)
    (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau) (hlam : 0 ≤ lam)
    (hcell : 2/(q+1 : ℝ) ≤ eta) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k-1+1) → Fin (L+1)) :
    let p := RefinedUpperPreparationProgram.finish hk chores active origin old
      (UpperGridMerge.prepare policy active origin q m draw) L pi threshold
    let t := RefinedUpperRepairTargets.targets chores active p eta lam
    (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ k*targetBudget k q L tau eta lam := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let V := dataMatrix hk active origin old data L pi threshold
  let A := dataDisagreement active origin data L
  have heta : 0 ≤ eta := (by positivity : (0 : ℝ) ≤ 2/(q+1 : ℝ)).trans hcell
  have hA : ∀ i j, A i j ≤ eta := data_disagreement_bound μ policy hpolicy active origin hgood hpositive q m L draw hparent eta hcell
  cases chores
  · have hn := dataMatrix_cake_near μ policy hpolicy active origin hgood hpositive hk old q m L draw hparent
      (2*tau) (fun i j => normalized_old_near μ policy hpolicy active origin hgood hpositive old hold
        q m L draw hparent tau htau i j i (hnear i j)) pi threshold
    have ha := allowance_le V (nearBudget k q L tau) (2*lam*eta) hn
    simp only [Fintype.card_fin] at ha
    have hb := cakeTargets_bound V A lam eta hlam heta hA
    change (∀ j, 0 ≤ cakeTargets V A lam j) ∧ ∑ j, cakeTargets V A lam j ≤ _
    refine ⟨fun j => (hb j).1,?_⟩
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hb j).2.trans ha)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,targetBudget] using hs
  · have hn := dataMatrix_chore_near μ policy hpolicy active origin hgood hpositive hk old q m L draw hparent
      (2*tau) (fun i j => normalized_old_near μ policy hpolicy active origin hgood hpositive old hold
        q m L draw hparent tau htau i i j (hnear i j)) pi threshold
    have ha := allowance_le (fun i j => -V i j) (nearBudget k q L tau) (2*lam*eta)
      (by simpa only [sub_neg_eq_add,nearBudget,V,data] using hn)
    simp only [Fintype.card_fin] at ha
    have hb := choreTargets_bound V A lam eta hlam heta hA
    change (∀ j, 0 ≤ choreTargets V A lam eta j) ∧ ∑ j, choreTargets V A lam eta j ≤ _
    refine ⟨fun j => (hb j).1,?_⟩
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hb j).2.trans ha)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,targetBudget] using hs

/-- Elementary Checks hold deterministically on every sample grid under the
parameter bounds; no successful oracle subroutine is assumed. -/
theorem actual_checks (hk : 2 ≤ k) (chores : Bool) (old : Fin k → State n)
    (hold : ∀ c, WellFormed μ (old c)) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hparent : 4*(jobCount k*L) ≤ q+1) (tau eta lam N : ℝ)
    (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau) (hlam : 0 ≤ lam)
    (hcell : 2/(q+1 : ℝ) ≤ eta) (hbudget : (k : ℝ)*targetBudget k q L tau eta lam < 1/16)
    (hcount : (UpperRecordedQuantiles.count (Agent := Fin k) q+m+1 : ℝ) ≤ N)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let p := RefinedUpperPreparationProgram.finish hk chores active origin old data L pi threshold
    Checks μ active p.2.1 (UpperGridData.cuts data)
      (RefinedUpperRepairTargets.targets chores active p eta lam) eta
      (RefinedUpperRepairSeedIndices.reserved active origin data L) N := by
  dsimp only
  have ht := actual_targets μ policy hpolicy active origin hgood hpositive hk chores old hold q m L draw
    hparent tau eta lam htau hnear hlam hcell pi threshold
  have he := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  refine ⟨data_wellFormed μ policy hpolicy active origin hgood hpositive q m L draw,
    he.1,he.2,UpperCommonGrid.grid_monotone _,reserveState_separated policy active origin q m draw 0 _,
    data_positive μ policy hpolicy active origin hgood hpositive q m L draw hparent,
    fun i e => (data_small μ policy hpolicy active origin hgood hpositive q m L draw hparent i e).trans hcell,
    ht.1,ht.2.trans_lt hbudget,?_,?_⟩
  · exact reserveState_cell_empty μ policy hpolicy active origin hgood hpositive q m draw 0 _
  · apply le_trans _ hcount
    have h := Finset.card_le_univ (RefinedUpperRepairSeedIndices.reserved active origin
      (UpperGridMerge.prepare policy active origin q m draw) L)
    simp only [Fintype.card_fin] at h
    exact_mod_cast h

end EnvyFreeResearch.Full.RefinedUpperRepairPreparationChecks
