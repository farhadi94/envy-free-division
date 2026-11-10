import EnvyFreeResearch.Full.MoatCapped
import EnvyFreeResearch.Full.MoatLedger

/-! The lower bound is obtained from actual fixed-input correctness, with
no assumed replay, decoder, transcript, or averaging contract. -/
namespace EnvyFreeResearch.Full.MoatLower
open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeRandomOutput
open NonnegativeRetainedFailure NonnegativeHardFamily
open MoatRetention MoatCapped MoatLimits
open scoped Classical ENNReal

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

theorem one_row_window (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (w p : ℝ) (hw : 1/(n:ℝ) < w) (hw1 : w < 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hfinite : expectedCost μ next flag ≠ ∞)
    (hfixed : ∀ h : ℝ, 0 < h → h ≤ w → ∀ z : MoatSelection.Input n,
      ENNReal.ofReal p ≤ μ (eventualSuccess next (MoatExperiment.oracle false flag chores w h z) []
        {A | Fair chores (MoatExperiment.rows false chores w h z) A})) :
    p ≤ 1/(n:ℝ)+(2*w/n)*(expectedCost μ next flag).toReal+2*(w-1/n)/n := by
  have hn0 : 0 < n := by omega
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw0 : 0 < w := lt_trans (by positivity) hw
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨fuel,hcap⟩ := small_cap_loss μ hn0 next hnext flag hfinite (ε/2) (by linarith)
  obtain ⟨h,hh,hhw,hgeo⟩ := small_geometric_loss μ hn0 w hw0 next hnext flag fuel (ε/2) (by linarith)
  have hbound := capped_retention μ hn next hnext false flag chores fuel w h p hw0 hw1.le
    hh hhw hw hp0 hp1 hfinite (hfixed h hh hhw)
  have hbase := MoatLedger.one_row_eliminate (q := (expectedCost μ next flag).toReal)
    hnr (s := μ.real {t | Successful {A | UniformEF A} (baseline next flag fuel t)})
    measureReal_nonneg measureReal_le_one hw.le
  simp only [realFactor, realRate, Bool.false_eq_true, ite_false] at hbound
  ring_nf at hbound hbase ⊢
  linarith

theorem two_row_window (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (w p : ℝ) (hw : 1/(n:ℝ) < w) (hw1 : w < 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hfinite : expectedCost μ next flag ≠ ∞)
    (hfixed : ∀ h : ℝ, 0 < h → h ≤ w → ∀ z : MoatSelection.Input n,
      ENNReal.ofReal p ≤ μ (eventualSuccess next (MoatExperiment.oracle true flag chores w h z) []
        {A | Fair chores (MoatExperiment.rows true chores w h z) A})) :
    p ≤ (4*w/n)*((expectedCost μ next flag).toReal+1) := by
  have hn0 : 0 < n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hw0 : 0 < w := lt_trans (by positivity) hw
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨fuel,hcap⟩ := small_cap_loss μ hn0 next hnext flag hfinite (ε/2) (by linarith)
  obtain ⟨h,hh,hhw,hgeo⟩ := small_geometric_loss μ hn0 w hw0 next hnext flag fuel (ε/2) (by linarith)
  have hbound := capped_retention μ hn next hnext true flag chores fuel w h p hw0 hw1.le
    hh hhw hw hp0 hp1 hfinite (hfixed h hh hhw)
  simp only [realFactor, realRate, ite_true, sub_self, zero_mul, zero_add] at hbound
  have hs : 0 ≤ μ.real {t | Successful {A | UniformEF A} (baseline next flag fuel t)} := measureReal_nonneg
  have hr : 0 ≤ 4*w/n := by positivity
  nlinarith

/-- The simultaneous sharp moat bounds on the expected answered count.
Both hard distributions are realized by public finite-step densities. -/
theorem physical_family (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfixed : ∀ (two : Bool) (w h : ℝ), 1/(n:ℝ) < w → w < 1 → 0 < h → h ≤ w →
      ∀ z : MoatSelection.Input n,
      ENNReal.ofReal p ≤ μ (eventualSuccess next (MoatExperiment.oracle two flag chores w h z) []
        {A | Fair chores (MoatExperiment.rows two chores w h z) A})) :
    ENNReal.ofReal (max ((n:ℝ)*((n:ℝ)*p-1)/2) ((n:ℝ)^2*p/4-1)) ≤ expectedCost μ next flag := by
  by_cases hfinite : expectedCost μ next flag ≠ ∞
  · have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    have h1 := MoatLedger.one_row_variable_success_limit hnR (by
      intro w hw hw1
      exact one_row_window μ hn next hnext flag chores w p hw hw1 hp0 hp1 hfinite
        (fun h hh hhw => hfixed false w h hw hw1 hh hhw))
    have h2lim := MoatLedger.two_row_limit (n := (n:ℝ)) (j := 1) hnR (by
      intro w hw hw1
      exact two_row_window μ hn next hnext flag chores w p hw hw1 hp0 hp1 hfinite
        (fun h hh hhw => hfixed true w h hw hw1 hh hhw))
    have h2 := MoatLedger.two_row_answered_bound (by linarith : (0:ℝ)<n) (le_refl (1:ℝ)) h2lim
    have hboth := max_le h1 h2
    exact (ENNReal.ofReal_le_ofReal hboth).trans_eq (ENNReal.ofReal_toReal hfinite)
  · simp [not_ne_iff.mp hfinite]

end EnvyFreeResearch.Full.MoatLower
