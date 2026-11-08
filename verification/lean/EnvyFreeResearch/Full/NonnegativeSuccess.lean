import EnvyFreeResearch.Full.ProtocolMeasurable
import EnvyFreeResearch.Full.NonnegativeProbability

namespace EnvyFreeResearch.Full.NonnegativeSuccess

open Set MeasureTheory OracleProtocol ProtocolMeasurable Filter
open scoped ENNReal Topology

variable {Tape Query Reply Output : Type*}

def Successful (good : Set Output) (e : Execution Query Reply Output) : Prop :=
  ∃ output, e.stop = .returned output ∧ output ∈ good

def eventualSuccess (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (history : History Query Reply) (good : Set Output) : Set Tape :=
  {tape | ∃ fuel, Successful good (run next oracle tape fuel history)}

theorem successful_terminal {good : Set Output} {e : Execution Query Reply Output}
    (h : Successful good e) : Terminal e.stop := by
  obtain ⟨output, ho, _⟩ := h
  intro query hq
  rw [ho] at hq
  cases hq

theorem terminal_executions_agree (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply)
    (k l : ℕ) (hk : Terminal (run next oracle tape k history).stop)
    (hl : Terminal (run next oracle tape l history).stop) :
    run next oracle tape k history = run next oracle tape l history := by
  have hkm := run_eq_of_terminal_of_le next oracle tape k (max k l) history (le_max_left _ _) hk
  have hlm := run_eq_of_terminal_of_le next oracle tape l (max k l) history (le_max_right _ _) hl
  exact hkm.symm.trans hlm

theorem terminal_failure_no_eventual_success (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply)
    (good : Set Output) (fuel : ℕ) (ht : Terminal (run next oracle tape fuel history).stop)
    (hbad : ¬ Successful good (run next oracle tape fuel history)) :
    tape ∉ eventualSuccess next oracle history good := by
  rintro ⟨k, hk⟩
  apply hbad
  rw [terminal_executions_agree next oracle tape history fuel k ht (successful_terminal hk)]
  exact hk

theorem cap_success_mono (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (history : History Query Reply) (good : Set Output) :
    Monotone (fun fuel => {tape | Successful good (run next oracle tape fuel history)}) := by
  intro k l hkl tape ht
  change Successful good (run next oracle tape l history)
  rw [run_eq_of_terminal_of_le next oracle tape k l history hkl (successful_terminal ht)]
  exact ht

theorem measurable_successful [MeasurableSpace Query] [MeasurableSpace Reply]
    [MeasurableSpace Output] (good : Set Output) (hgood : MeasurableSet good) :
    MeasurableSet {e : Execution Query Reply Output | Successful good e} := by
  have heq : {e : Execution Query Reply Output | Successful good e} =
      (fun e => stopCode e.stop) ⁻¹' (Sum.inl '' good) := by
    ext e
    cases he : e.stop <;> simp [Successful, he, stopCode]
  rw [heq]
  exact hgood.inl_image.preimage ((comap_measurable stopCode).comp measurable_execution_stop)

theorem measurable_cap_success [MeasurableSpace Tape] [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Output]
    (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable oracle) (history : History Query Reply)
    (good : Set Output) (hgood : MeasurableSet good) (fuel : ℕ) :
    MeasurableSet {tape | Successful good (run next oracle tape fuel history)} :=
  (measurable_successful good hgood).preimage
    (measurable_run_at_history next oracle hnext horacle fuel history)

theorem measurable_eventualSuccess [MeasurableSpace Tape] [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Output]
    (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable oracle) (history : History Query Reply)
    (good : Set Output) (hgood : MeasurableSet good) :
    MeasurableSet (eventualSuccess next oracle history good) := by
  have heq : eventualSuccess next oracle history good =
      ⋃ fuel : ℕ, {tape | Successful good (run next oracle tape fuel history)} := by
    ext tape
    simp [eventualSuccess]
  rw [heq]
  exact MeasurableSet.iUnion fun fuel =>
    measurable_cap_success next oracle hnext horacle history good hgood fuel

theorem measurable_queryCost [MeasurableSpace Tape] [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Output]
    (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable oracle) (history : History Query Reply) :
    Measurable (fun tape => queryCost next oracle tape history) := by
  have hlen (fuel : ℕ) : Measurable (fun tape =>
      (run next oracle tape fuel history).answered.length) :=
    measurable_list_length.comp (measurable_execution_answered.comp
      (measurable_run_at_history next oracle hnext horacle fuel history))
  have hle (n : ℕ) : MeasurableSet
      {tape | queryCost next oracle tape history ≤ (n : ℕ∞)} := by
    have heq : {tape | queryCost next oracle tape history ≤ (n : ℕ∞)} =
        ⋂ fuel, {tape | (run next oracle tape fuel history).answered.length ≤ n} := by
      ext tape
      simp [queryCost, iSup_le_iff]
    rw [heq]
    exact MeasurableSet.iInter (fun fuel => measurableSet_le (hlen fuel) measurable_const)
  apply ENat.measurable_iff.mpr
  intro n
  cases n with
  | zero =>
    change MeasurableSet {tape | queryCost next oracle tape history = (0 : ℕ∞)}
    simpa only [Nat.cast_zero, le_zero_iff] using hle 0
  | succ n =>
    have heq : (fun tape => queryCost next oracle tape history) ⁻¹' {(↑(n + 1) : ℕ∞)} =
        {tape | queryCost next oracle tape history ≤ ((n + 1 : ℕ) : ℕ∞)} ∩
          {tape | queryCost next oracle tape history ≤ (n : ℕ∞)}ᶜ := by
      ext tape
      change queryCost next oracle tape history = (↑(n + 1) : ℕ∞) ↔
        queryCost next oracle tape history ≤ (↑(n + 1) : ℕ∞) ∧
          ¬ queryCost next oracle tape history ≤ (↑n : ℕ∞)
      generalize queryCost next oracle tape history = v
      induction v using ENat.recTopCoe with
      | top => simp only [ENat.top_ne_natCast, top_le_iff, ENat.natCast_ne_top, false_and]
      | coe k => simp only [ENat.natCast_inj, ENat.natCast_le_natCast]; omega
    rw [heq]
    exact (hle (n + 1)).inter (hle n).compl

/-- Finite unconditional expected answered cost excludes infinitely many
calls almost surely, while permitting wrong outputs and finite-call divergence. -/
theorem ae_queryCost_finite [MeasurableSpace Tape] [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Output]
    (μ : Measure Tape) (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable oracle) (history : History Query Reply)
    (hfinite : (∫⁻ tape, (queryCost next oracle tape history : ℝ≥0∞) ∂μ) ≠ ∞) :
    ∀ᵐ tape ∂μ, queryCost next oracle tape history ≠ ⊤ := by
  have hQ := (measurable_of_countable (fun k : ℕ∞ => (k : ℝ≥0∞))).comp
    (measurable_queryCost next oracle hnext horacle history)
  filter_upwards [ae_lt_top hQ hfinite] with tape ht
  intro he
  simp [he] at ht

def Exhausted (e : Execution Query Reply Output) : Prop :=
  ∃ query, e.stop = .exhausted query

theorem measurable_exhausted [MeasurableSpace Query] [MeasurableSpace Reply]
    [MeasurableSpace Output] :
    MeasurableSet {e : Execution Query Reply Output | Exhausted e} := by
  let target : Set (Output ⊕ (Unit ⊕ (Query ⊕ Query))) :=
    Sum.inr '' (Sum.inr '' (Sum.inr '' (Set.univ : Set Query)))
  have heq : {e : Execution Query Reply Output | Exhausted e} =
      (fun e => stopCode e.stop) ⁻¹' target := by
    ext e
    cases he : e.stop <;> simp [Exhausted, he, stopCode, target]
  rw [heq]
  exact (((MeasurableSet.univ.inr_image).inr_image).inr_image).preimage
    ((comap_measurable stopCode).comp measurable_execution_stop)

theorem exhaustion_antitone (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (history : History Query Reply) :
    Antitone (fun fuel => {tape | Exhausted (run next oracle tape fuel history)}) := by
  intro k l hkl tape hl
  change Exhausted (run next oracle tape k history)
  by_contra hk
  have ht : Terminal (run next oracle tape k history).stop := by
    simpa only [Exhausted, not_exists, Terminal] using hk
  have heq := run_eq_of_terminal_of_le next oracle tape k l history hkl ht
  obtain ⟨query, hquery⟩ := hl
  rw [heq] at hquery
  exact ht query hquery

/-- Finite unconditional expected cost makes the actual cap-exhaustion
probability vanish. There is no almost-sure termination or correctness premise:
explicit finite-call divergence is already a stable terminal outcome. -/
theorem exhaustion_tendsto_zero [MeasurableSpace Tape] [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Output]
    (μ : Measure Tape) [IsFiniteMeasure μ]
    (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable oracle) (history : History Query Reply)
    (hfinite : (∫⁻ tape, (queryCost next oracle tape history : ℝ≥0∞) ∂μ) ≠ ∞) :
    Tendsto (fun fuel => μ {tape | Exhausted (run next oracle tape fuel history)})
      atTop (𝓝 0) := by
  let events := fun fuel => {tape | Exhausted (run next oracle tape fuel history)}
  have hmeas (fuel : ℕ) : MeasurableSet (events fuel) := measurable_exhausted.preimage
    (measurable_run_at_history next oracle hnext horacle fuel history)
  have hnull : μ (⋂ fuel, events fuel) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_queryCost_finite μ next oracle hnext horacle history hfinite]
      with tape ht
    intro hall
    obtain ⟨fuel, hterminal⟩ := exists_terminal_of_queryCost_ne_top next oracle tape history ht
    obtain ⟨query, hquery⟩ := Set.mem_iInter.mp hall fuel
    exact hterminal query hquery
  have hlim := tendsto_measure_iInter_atTop (fun fuel => (hmeas fuel).nullMeasurableSet)
    (exhaustion_antitone next oracle history)
    (show ∃ fuel, μ (events fuel) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  simpa only [Function.comp_def, hnull] using hlim

/-- Capped successful-return probability increases to the actual eventual
success probability on any tape space. -/
theorem cap_success_tendsto [MeasurableSpace Tape]
    (μ : Measure Tape) (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (history : History Query Reply) (good : Set Output) :
    Tendsto (fun fuel => μ {tape | Successful good (run next oracle tape fuel history)})
      atTop (𝓝 (μ (eventualSuccess next oracle history good))) := by
  have heq : eventualSuccess next oracle history good =
      ⋃ fuel : ℕ, {tape | Successful good (run next oracle tape fuel history)} := by
    ext tape
    simp [eventualSuccess]
  rw [heq]
  exact tendsto_measure_iUnion_atTop (cap_success_mono next oracle history good)

section JointSuccess

variable {Parameter : Type*} [MeasurableSpace Parameter] [MeasurableSpace Tape]
  [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output]

/-- A parameter-dependent physical correctness condition can be read from
the actual returned output using the standard disjoint-union stop code. -/
theorem measurable_joint_successful (good : Set (Parameter × Output))
    (hgood : MeasurableSet good) :
    MeasurableSet {z : Parameter × Execution Query Reply Output |
      Successful {output | (z.1, output) ∈ good} z.2} := by
  let distribute := MeasurableEquiv.prodSumDistrib Parameter Output (Unit ⊕ (Query ⊕ Query))
  have hcode : Measurable (fun z : Parameter × Execution Query Reply Output =>
      (z.1, stopCode z.2.stop)) := measurable_fst.prodMk
    ((comap_measurable stopCode).comp (measurable_execution_stop.comp measurable_snd))
  have hinl (parameter : Parameter) (output : Output) :
      distribute (parameter, Sum.inl output) = Sum.inl (parameter, output) := rfl
  have hinr (parameter : Parameter) (other : Unit ⊕ (Query ⊕ Query)) :
      distribute (parameter, Sum.inr other) = Sum.inr (parameter, other) := rfl
  have heq : {z : Parameter × Execution Query Reply Output |
      Successful {output | (z.1, output) ∈ good} z.2} =
      (fun z => distribute (z.1, stopCode z.2.stop)) ⁻¹' (Sum.inl '' good) := by
    ext z
    rcases z with ⟨parameter, e⟩
    cases he : e.stop <;> simp [Successful, he, stopCode, hinl, hinr]
  rw [heq]
  exact hgood.inl_image.preimage (distribute.measurable.comp hcode)

def jointSuccess (next : Protocol Tape Query Reply Output) (oracle : Parameter → Query → Option Reply)
    (history : History Query Reply) (good : Set (Parameter × Output)) : Set (Parameter × Tape) :=
  {z | z.2 ∈ eventualSuccess next (oracle z.1) history {output | (z.1, output) ∈ good}}

theorem measurable_jointSuccess (next : Protocol Tape Query Reply Output)
    (oracle : Parameter → Query → Option Reply)
    (hnext : Measurable (fun z : Tape × History Query Reply => next z.1 z.2))
    (horacle : Measurable (fun z : Parameter × Query => oracle z.1 z.2))
    (history : History Query Reply) (good : Set (Parameter × Output)) (hgood : MeasurableSet good) :
    MeasurableSet (jointSuccess next oracle history good) := by
  have heq : jointSuccess next oracle history good = ⋃ fuel : ℕ,
      {z : Parameter × Tape | Successful {output | (z.1, output) ∈ good}
        (run next (oracle z.1) z.2 fuel history)} := by
    ext z
    simp [jointSuccess, eventualSuccess]
  rw [heq]
  apply MeasurableSet.iUnion
  intro fuel
  exact (measurable_joint_successful good hgood).preimage
    (measurable_fst.prodMk
      (measurable_run_parameterized_at_history next oracle hnext horacle fuel history))

/-- Fixed-input success guarantees are averaged for the actual eventual
success/failure event of the parameterized adaptive executor. The input is
sampled independently of the tape; no conditional law is needed. -/
theorem fixed_input_failure_bound (μ : Measure Tape) [IsProbabilityMeasure μ]
    (ν : Measure Parameter) [IsProbabilityMeasure ν]
    (next : Protocol Tape Query Reply Output) (oracle : Parameter → Query → Option Reply)
    (hnext : Measurable (fun z : Tape × History Query Reply => next z.1 z.2))
    (horacle : Measurable (fun z : Parameter × Query => oracle z.1 z.2))
    (history : History Query Reply) (good : Set (Parameter × Output)) (hgood : MeasurableSet good)
    (p : ℝ≥0∞)
    (hfixed : ∀ parameter, p ≤ μ (eventualSuccess next (oracle parameter) history
      {output | (parameter, output) ∈ good})) :
    (ν.prod μ) (jointSuccess next oracle history good)ᶜ ≤ 1 - p := by
  have hsuccess := measurable_jointSuccess next oracle hnext horacle history good hgood
  apply NonnegativeProbability.fixed_input_average hsuccess.compl
  intro parameter
  have hsection : MeasurableSet (eventualSuccess next (oracle parameter) history
      {output | (parameter, output) ∈ good}) :=
    hsuccess.preimage (measurable_const.prodMk measurable_id)
  have heq : {tape | (parameter, tape) ∈ (jointSuccess next oracle history good)ᶜ} =
      (eventualSuccess next (oracle parameter) history {output | (parameter, output) ∈ good})ᶜ := rfl
  rw [heq, measure_compl hsection (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left (hfixed parameter) 1

end JointSuccess

end EnvyFreeResearch.Full.NonnegativeSuccess

#print axioms EnvyFreeResearch.Full.NonnegativeSuccess.terminal_failure_no_eventual_success
#print axioms EnvyFreeResearch.Full.NonnegativeSuccess.measurable_eventualSuccess
#print axioms EnvyFreeResearch.Full.NonnegativeSuccess.ae_queryCost_finite
#print axioms EnvyFreeResearch.Full.NonnegativeSuccess.exhaustion_tendsto_zero
#print axioms EnvyFreeResearch.Full.NonnegativeSuccess.cap_success_tendsto
#print axioms EnvyFreeResearch.Full.NonnegativeSuccess.fixed_input_failure_bound
