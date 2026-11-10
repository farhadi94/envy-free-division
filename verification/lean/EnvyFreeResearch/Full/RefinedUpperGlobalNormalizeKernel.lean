import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeCore

/-! Actual bounded sink recursion: every recursive step strictly decreases
the active population; the zero-row purge is performed only once beforehand. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows RefinedUpperGlobal.Sink
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem positiveCore_valid (fallback : Fin n) (chores : Bool) (fuel : ℕ)
    (whole : Set ℝ) (a : Anchor n) (ha : a.Committed μ (direction chores) whole)
    (hh : a.HistoryCompatible) (hn : a.active.Nonempty) (hpositive : positive a)
    (hbudget : a.active.card ≤ fuel) : (positiveCore fallback chores fuel a).Valid μ chores whole := by
  induction fuel generalizing a with
  | zero => have hc := Finset.card_pos.mpr hn; omega
  | succ fuel ih =>
    by_cases h1 : a.active.card ≤ 1
    · have hm := pick_mem fallback a.active hn
      have ht := singleton_terminal μ (direction chores) whole a ha hh _ hm (singleton_pick fallback a.active hn h1)
      simp only [positiveCore,h1,ite_true,Request.Valid]
      exact ⟨ht.1,terminal_history _ _ _,ht.2⟩
    · by_cases h2 : a.active.card ≤ 2
      · have hc : a.active.card=2 := by omega
        have ht := two_pick fallback a.active hc
        simp only [positiveCore,h1,ite_false,h2,ite_true,Request.Valid]
        exact ⟨ha,hh,ht.1,ht.2,hpositive _ (pick_mem fallback a.active hn)⟩
      · by_cases hs : sinkAvailable (direction chores) a = true
        · have hnot := (sinkAvailable_iff _ _).mp hs
          have hp := selectedFreeze_progress (direction chores) a hnot
          have hcomm := selectedFreeze_committed μ whole a (direction chores) hnot ha
          have hist : (selectedFreeze (direction chores) a).HistoryCompatible := hh
          have hpos : positive (selectedFreeze (direction chores) a) := fun i hi => hpositive i (hp.2.1 hi)
          have hfuel : (selectedFreeze (direction chores) a).active.card ≤ fuel := by omega
          simpa only [positiveCore,h1,h2,hs,ite_false,ite_true] using
            ih _ hcomm hist hp.1 hpos hfuel
        · have hfalse : sinkAvailable (direction chores) a = false := Bool.eq_false_iff.mpr hs
          simp only [positiveCore,h1,h2,hfalse,ite_false,Bool.false_eq_true,Request.Valid]
          exact ⟨ha,hh,by omega,hpositive,no_sink_strong _ _ hfalse⟩

theorem normalize_valid (fallback : Fin n) (chores : Bool) (fuel : ℕ)
    (whole : Set ℝ) (a : Anchor n) (ha : a.Committed μ (direction chores) whole)
    (hh : a.HistoryCompatible) (hn : a.active.Nonempty) (hbudget : a.active.card ≤ fuel) :
    (normalize fallback chores fuel a).Valid μ chores whole := by
  cases chores with
  | false =>
    by_cases hp : (positiveRows a.residue a.active).Nonempty
    · have hcomm := freezeZero_committed μ whole a ha
      have hpos := freezeZero_positive μ whole a ha.1
      have hc := Finset.card_le_card (positiveRows_subset a.residue a.active)
      simpa only [normalize,Bool.false_eq_true,ite_false,hp,ite_true] using
        positiveCore_valid μ fallback false fuel whole (freezeZero a) hcomm hh hp hpos (hc.trans hbudget)
    · have hm := pick_mem fallback a.active hn
      have ht := cake_all_zero_terminal μ whole a hh _ hm ha (positiveRows_empty_cached μ whole a ha.1 hp)
      simp only [normalize,Bool.false_eq_true,ite_false,hp,Request.Valid,direction]
      exact ⟨ht.1,terminal_history _ _ _,ht.2⟩
  | true =>
    by_cases hz : (zeroRows a.residue a.active).Nonempty
    · have hm := pick_mem fallback (zeroRows a.residue a.active) hz
      have ha' := (Finset.mem_filter.mp hm).1
      have hzero := (Finset.mem_filter.mp hm).2
      have ht := chore_zero_terminal μ whole a hh _ ha' ha hzero
      simp only [normalize,ite_true,hz,Request.Valid,direction]
      exact ⟨ht.1,terminal_history _ _ _,ht.2⟩
    · simpa only [normalize,ite_true,hz,ite_false] using
        positiveCore_valid μ fallback true fuel whole a ha hh hn (no_zero_positive μ whole a ha.1 hz) hbudget

end EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
