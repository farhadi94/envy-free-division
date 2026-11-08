import EnvyFreeResearch.Full.RightmostViews
import EnvyFreeResearch.Full.RightmostAmplification

/-! Actual success events, unconditional query cost, and the finite-cap
identity for measurable signed-allocation protocols. -/

noncomputable section
namespace EnvyFreeResearch.Full.RightmostSuccess
open Set MeasureTheory OracleProtocol RightmostOracle
open IntervalOracle (Profile Query)
open MixedFrontier RightmostExecution
open RightmostFailure MixedObstruction MixedDensity IntervalAllocation IntervalValues
open RightmostViews RightmostAmplification NonnegativeOutputMeasurable ProtocolMeasurable
open scoped BigOperators Classical ENNReal

variable {Agent Ω : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [MeasurableSpace Ω] {α : ℝ}

theorem capSuccess_measurable_of_run
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (fuel : ℕ) (ε : ℝ)
    (hrun : Measurable (fun ω => run next (oracle (profile S)) ω fuel [])) :
    MeasurableSet (capSuccess next S fuel ε) := by
  have hstop := (comap_measurable (stopCode (α := Query Agent) (β := Allocation Agent))).comp
    (measurable_execution_stop.comp hrun)
  have heq : capSuccess next S fuel ε =
      (fun ω => stopCode (run next (oracle (profile S)) ω fuel []).stop) ⁻¹'
        (Sum.inl '' {A : Allocation Agent | ApproximateEF S A ε}) := by
    ext ω
    cases hs : (run next (oracle (profile S)) ω fuel []).stop <;>
      simp [capSuccess, hs, stopCode]
  rw [heq]
  exact (approximateEF_measurable S ε).inl_image.preimage hstop

theorem capSuccess_measurable
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2))
    (S : State Agent α) (fuel : ℕ) (ε : ℝ) : MeasurableSet (capSuccess next S fuel ε) :=
  capSuccess_measurable_of_run next S fuel ε (measurable_runs_of_next next hnext S fuel)

def success (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (ε : ℝ) : Set Ω := ⋃ fuel, capSuccess next S fuel ε

theorem success_measurable_of_runs
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (ε : ℝ)
    (hruns : ∀ fuel, Measurable (fun ω => run next (oracle (profile S)) ω fuel [])) :
    MeasurableSet (success next S ε) :=
  MeasurableSet.iUnion (fun fuel => capSuccess_measurable_of_run next S fuel ε (hruns fuel))

theorem success_measurable
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2))
    (S : State Agent α) (ε : ℝ) : MeasurableSet (success next S ε) :=
  MeasurableSet.iUnion (fun fuel => capSuccess_measurable next hnext S fuel ε)

theorem actual_cost_measurable_of_runs
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α)
    (hruns : ∀ fuel, Measurable (fun ω => run next (oracle (profile S)) ω fuel [])) :
    Measurable (fun ω => queryCost next (oracle (profile S)) ω []) := by
  have hlen (fuel : ℕ) : Measurable (fun ω =>
      (run next (oracle (profile S)) ω fuel []).answered.length) :=
    measurable_list_length.comp (measurable_execution_answered.comp (hruns fuel))
  have hle (n : ℕ) : MeasurableSet
      {ω | queryCost next (oracle (profile S)) ω [] ≤ (n : ℕ∞)} := by
    have heq : {ω | queryCost next (oracle (profile S)) ω [] ≤ (n : ℕ∞)} =
        ⋂ fuel, {ω | (run next (oracle (profile S)) ω fuel []).answered.length ≤ n} := by
      ext ω
      simp [queryCost, iSup_le_iff]
    rw [heq]
    exact MeasurableSet.iInter (fun fuel => measurableSet_le (hlen fuel) measurable_const)
  apply ENat.measurable_iff.mpr
  intro n
  cases n with
  | zero =>
    change MeasurableSet {ω | queryCost next (oracle (profile S)) ω [] = (0 : ℕ∞)}
    simpa only [Nat.cast_zero, le_zero_iff] using hle 0
  | succ n =>
    have heq : (fun ω => queryCost next (oracle (profile S)) ω []) ⁻¹' {(↑(n + 1) : ℕ∞)} =
        {ω | queryCost next (oracle (profile S)) ω [] ≤ ((n + 1 : ℕ) : ℕ∞)} ∩
          {ω | queryCost next (oracle (profile S)) ω [] ≤ (n : ℕ∞)}ᶜ := by
      ext ω
      change queryCost next (oracle (profile S)) ω [] = (↑(n + 1) : ℕ∞) ↔
        queryCost next (oracle (profile S)) ω [] ≤ (↑(n + 1) : ℕ∞) ∧
          ¬ queryCost next (oracle (profile S)) ω [] ≤ (↑n : ℕ∞)
      generalize queryCost next (oracle (profile S)) ω [] = v
      induction v using ENat.recTopCoe with
      | top => simp only [ENat.top_ne_natCast, top_le_iff, ENat.natCast_ne_top, false_and]
      | coe k => simp only [ENat.natCast_inj, ENat.natCast_le_natCast]; omega
    rw [heq]
    exact (hle (n + 1)).inter (hle n).compl

theorem actual_cost_measurable
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2))
    (S : State Agent α) : Measurable (fun ω => queryCost next (oracle (profile S)) ω []) :=
  actual_cost_measurable_of_runs next S (measurable_runs_of_next next hnext S)

omit [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
  [MeasurableSingletonClass Agent] [MeasurableSpace Ω] in
/-- Successful executions below the query budget are exactly the successful
cap-q executions, including output after the final allowed answer. -/
theorem success_below_cap
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (fuel : ℕ) (ε : ℝ) :
    success next S ε ∩ {ω | queryCost next (oracle (profile S)) ω [] ≤ (fuel : ℕ∞)} =
      capSuccess next S fuel ε := by
  ext ω
  constructor
  · rintro ⟨hs, hc⟩
    obtain ⟨k, A, hret, hef⟩ := mem_iUnion.mp hs
    have ht : Terminal (run next (oracle (profile S)) ω k []).stop := by
      intro q
      simp [hret]
    have hcost := queryCost_of_terminal next (oracle (profile S)) ω k [] ht
    change queryCost next (oracle (profile S)) ω [] ≤ (fuel : ℕ∞) at hc
    rw [hcost] at hc
    have hlen : (run next (oracle (profile S)) ω k []).answered.length ≤ fuel := by exact_mod_cast hc
    have hshort := run_answered_length_of_returned next (oracle (profile S)) ω k [] A hret
    have hshortterm : Terminal
        (run next (oracle (profile S)) ω (run next (oracle (profile S)) ω k []).answered.length []).stop := by
      rw [hshort]
      exact ht
    have hlarge := run_eq_of_terminal_of_le next (oracle (profile S)) ω
      (run next (oracle (profile S)) ω k []).answered.length fuel [] hlen hshortterm
    exact ⟨A, by rw [hlarge, hshort]; exact hret, hef⟩
  · rintro ⟨A, hret, hef⟩
    refine ⟨mem_iUnion.mpr ⟨fuel, A, hret, hef⟩, ?_⟩
    have ht : Terminal (run next (oracle (profile S)) ω fuel []).stop := by
      intro q
      simp [hret]
    change queryCost next (oracle (profile S)) ω [] ≤ (fuel : ℕ∞)
    rw [queryCost_of_terminal next (oracle (profile S)) ω fuel [] ht]
    exact_mod_cast answered_length_le next (oracle (profile S)) ω fuel []

end EnvyFreeResearch.Full.RightmostSuccess
