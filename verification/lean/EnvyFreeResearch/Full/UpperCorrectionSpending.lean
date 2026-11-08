import EnvyFreeResearch.Full.UpperCorrectionDisjoint
import EnvyFreeResearch.Full.UpperPreparedEnvelopeMean

/-! Actual successful correction outputs spend less than one eighth of
the reserve, and their recorded remainder is its literal complement. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperCorrectionSpending

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCorrectionSetup UpperCorrectionOutcome UpperCorrectionAccepted UpperCorrectionTrace
  UpperCorrectionDisjoint UpperCorrectionPieces UpperPreparedEnvelopeMean UpperCircularStage
  UpperPayments UpperLogicalCells

theorem flatten_domain_eq_iUnion {k : ℕ} (pieces : List (List Component)) (hlength : pieces.length = k) :
    domain pieces.flatten = ⋃ j : Fin k, domain (pieces[j.val]?.getD []) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hcs
    apply mem_iUnion.mpr
    refine ⟨⟨j, by omega⟩, ?_⟩
    rw [List.getElem?_eq_getElem hj]
    simp only [Option.getD_some]
    rw [heq]
    exact mem_domain.mpr ⟨c, hc, hxc⟩
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hj
    apply mem_domain.mpr
    refine ⟨c, List.mem_flatten.mpr ⟨pieces[j.val]?.getD [], ?_, hc⟩, hxc⟩
    exact getD_mem pieces [] j.val (by rw [hlength]; exact j.isLt)

variable {n k m : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (hinj : Function.Injective active)
  (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam N : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : (k : ℝ)^2 ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
  (tape : Fin k → UpperCircular.Circle)
  (hrun : (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false)

include hpolicy hinj heta hlam hsize hmargin hc hrun in
theorem output_union_mass_le (i : Fin k) :
    (μ (active i)).real (⋃ j, domain (output policy active reserve cuts t eta lam tape j)) ≤
      ((∑ j, t j) + (k : ℝ) * lam * eta) * (μ (active i)).real (domain reserve.cells) := by
  have hwhole := table_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated hc.positive
  have heach (j : Fin k) : (μ (active i)).real (domain (output policy active reserve cuts t eta lam tape j)) ≤
      (t j + lam * eta) * (μ (active i)).real (domain reserve.cells) := by
    have h := (output_values μ active hinj reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated
      hc.positive t eta lam heta hc.small hc.targets hc.sum hsize hmargin policy hpolicy tape hrun j).2 i
    have hupper := (le_abs_self _).trans h
    have hgap := mul_le_mul_of_nonneg_left
      (cellGap_le (table active reserve cuts) eta heta hwhole hc.small i j) hlam
    apply (div_le_iff₀ (hc.positive i)).mp
    linarith
  calc
    _ ≤ ∑ j, (μ (active i)).real (domain (output policy active reserve cuts t eta lam tape j)) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ j, (t j + lam * eta) * (μ (active i)).real (domain reserve.cells) := Finset.sum_le_sum (fun j _ => heach j)
    _ = _ := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

include hpolicy hinj heta hlam hsize hmargin hc hrun in
theorem output_union_mass_lt_eighth (i : Fin k) :
    (μ (active i)).real (⋃ j, domain (output policy active reserve cuts t eta lam tape j)) <
      (μ (active i)).real (domain reserve.cells) / 8 := by
  have h := output_union_mass_le μ policy hpolicy active hinj reserve cuts t eta lam N
    heta hlam hsize hmargin selected hc tape hrun i
  have hb : (∑ j, t j) + (k : ℝ) * lam * eta < 1 / 8 := by linarith [hc.sum]
  have hmul := mul_lt_mul_of_pos_right hb (hc.positive i)
  linarith

include hpolicy hinj heta hlam hsize hmargin hc hrun in
theorem output_union_mass_lt_buffer_eighth (B : Set ℝ) (hsub : domain reserve.cells ⊆ B) (i : Fin k) :
    (μ (active i)).real (⋃ j, domain (output policy active reserve cuts t eta lam tape j)) <
      (μ (active i)).real B / 8 := by
  have h := output_union_mass_lt_eighth μ policy hpolicy active hinj reserve cuts t eta lam N
    heta hlam hsize hmargin selected hc tape hrun i
  have hm := measureReal_mono hsub (measure_ne_top (μ (active i)) B)
  linarith

include hc hrun in
/-- No null fragments disappear: the actual final state is exactly the
reserve after every whole and circular payment has been assigned. -/
theorem final_domain_complement :
    domain (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.current.cells =
      domain reserve.cells \ ⋃ j, domain (output policy active reserve cuts t eta lam tape j) := by
  have hs := successful_outputs policy (tasks active reserve cuts t eta lam)
    (startState active reserve cuts t eta).current tape hrun
  have hlength : (corrections policy active reserve cuts t eta lam tape).length = k := hs.1
  have hfinal : domain (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.current.cells =
      domain (startState active reserve cuts t eta).current.cells \
        domain (corrections policy active reserve cuts t eta lam tape).flatten := hs.2.2
  rw [hfinal, flatten_domain_eq_iUnion _ hlength]
  have hstart := UpperPendingExclusion.remove_domain reserve hc.wellFormed.2.1 cuts hc.zero hc.monotone hc.separated
    (whole active reserve cuts t eta)
  change domain (UpperPendingExclusion.remove reserve cuts (whole active reserve cuts t eta)).cells \ _ = _
  rw [hstart]
  simp_rw [UpperCorrectionOutcome.output, domain_append,
    wholeAtoms_domain active reserve cuts hc.zero hc.monotone hc.separated]
  dsimp only [UpperRawPayments.pending, whole]
  ext x
  simp only [mem_sdiff, mem_iUnion, mem_union]
  aesop

end EnvyFreeResearch.Full.UpperCorrectionSpending
