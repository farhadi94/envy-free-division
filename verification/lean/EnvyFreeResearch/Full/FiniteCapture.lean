import EnvyFreeResearch.QueryProbability

/-!
Measure-theoretic selection primitives for actual finite-horizon query traces.
No atomlessness, countable tape space, or bound on the number of output
coordinates is assumed. These lemmas do not themselves supply an adversarial
profile update; that concrete construction must instantiate the capture step.
-/

namespace EnvyFreeResearch.Full.FiniteCapture

open MeasureTheory Set
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A monotone countable cover contains at least half the covered mass at
some finite stage, including when the covered set has zero measure. -/
theorem exists_half_mass_of_monotone_cover (S : Set Ω) (A : ℕ → Set Ω)
    (hmono : Monotone A) (hcover : (⋃ k, A k) = S) :
    ∃ k, μ.real S / 2 ≤ μ.real (A k) := by
  by_cases hzero : μ.real S = 0
  · exact ⟨0, by simp [hzero]⟩
  have hpos : 0 < μ.real S := lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero)
  by_contra h
  push Not at h
  have hbound : μ S ≤ ENNReal.ofReal (μ.real S / 2) := by
    calc
      μ S = μ (⋃ k, A k) := congrArg μ hcover.symm
      _ = ⨆ k, μ (A k) := hmono.measure_iUnion
      _ ≤ ENNReal.ofReal (μ.real S / 2) := by
        apply iSup_le
        intro k
        rw [← ofReal_measureReal (μ := μ) (s := A k)]
        exact ENNReal.ofReal_le_ofReal (le_of_lt (h k))
  have hr := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  change μ.real S ≤ μ.real S / 2 at hr
  linarith

/-- Finite coordinates strictly below the endpoint can be bounded on a set
containing at least half the tape mass. The maximum may encode a variable,
unbounded finite output list. -/
theorem exists_coordinate_quantile (S : Set Ω) (c : Ω → ℝ) (l : ℝ)
    (hl : l < 1) (hc : ∀ ω ∈ S, c ω < 1) :
    ∃ r : ℝ, l < r ∧ r < 1 ∧
      μ.real S / 2 ≤ μ.real (S ∩ {ω | c ω ≤ r}) := by
  let A : ℕ → Set Ω := fun k => S ∩ {ω | c ω ≤ 1 - 1 / (k + 1 : ℝ)}
  have hmono : Monotone A := by
    intro k m hkm ω hω
    change ω ∈ S ∧ c ω ≤ 1 - 1 / (m + 1 : ℝ)
    change ω ∈ S ∧ c ω ≤ 1 - 1 / (k + 1 : ℝ) at hω
    refine ⟨hω.1, le_trans hω.2 ?_⟩
    have hd : (k + 1 : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hkm 1
    have hv := one_div_le_one_div_of_le (by positivity : 0 < (k + 1 : ℝ)) hd
    linarith
  have hcover : (⋃ k, A k) = S := by
    ext ω
    constructor
    · intro hω
      obtain ⟨k, hk⟩ := mem_iUnion.mp hω
      exact hk.1
    · intro hω
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith [hc ω hω] : 0 < 1 - c ω)
      refine mem_iUnion.mpr ⟨k, ?_⟩
      change ω ∈ S ∧ c ω ≤ 1 - 1 / (k + 1 : ℝ)
      exact ⟨hω, by linarith⟩
  obtain ⟨k, hk⟩ := exists_half_mass_of_monotone_cover (μ := μ) S A hmono hcover
  let r : ℝ := max ((l + 1) / 2) (1 - 1 / (k + 1 : ℝ))
  have hhalf : l < (l + 1) / 2 := by linarith
  have hrlo : l < r := hhalf.trans_le (le_max_left _ _)
  have hrhi : r < 1 := by
    apply max_lt
    · linarith
    · have : 0 < 1 / (k + 1 : ℝ) := by positivity
      linarith
  refine ⟨r, hrlo, hrhi, hk.trans ?_⟩
  refine measureReal_mono ?_ (by finiteness)
  intro ω hω
  change ω ∈ S ∧ c ω ≤ r
  change ω ∈ S ∧ c ω ≤ 1 - 1 / (k + 1 : ℝ) at hω
  exact ⟨hω.1, hω.2.trans (le_max_right _ _)⟩

omit [IsFiniteMeasure μ] in
/-- A finite row class contains at least its share of an arbitrary tape set.
This is a measure-theoretic pigeonhole principle, not a finite-tape argument. -/
theorem exists_large_row {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (S : Set Ω) (row : Ω → Agent) :
    ∃ j, μ.real S / Fintype.card Agent ≤ μ.real (S ∩ {ω | row ω = j}) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Agent := by exact_mod_cast Fintype.card_pos
  have hcover : (⋃ j, S ∩ {ω | row ω = j}) = S := by
    ext ω
    simp
  have hsum : μ.real S ≤ ∑ j, μ.real (S ∩ {ω | row ω = j}) := by
    calc
      μ.real S = μ.real (⋃ j, S ∩ {ω | row ω = j}) := congrArg μ.real hcover.symm
      _ ≤ ∑ j, μ.real (S ∩ {ω | row ω = j}) :=
        measureReal_iUnion_fintype_le (fun j : Agent => S ∩ {ω | row ω = j})
  by_contra h
  push Not at h
  have hstrict :
      (∑ j, μ.real (S ∩ {ω | row ω = j})) <
      ∑ _j : Agent, μ.real S / Fintype.card Agent := by
    apply Finset.sum_lt_sum
    · intro j _
      exact (h j).le
    · exact ⟨Classical.choice inferInstance, Finset.mem_univ _, h _⟩
  have hconstant : (∑ _j : Agent, μ.real S / Fintype.card Agent) = μ.real S := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [hconstant] at hstrict
  exact (not_lt_of_ge hsum) hstrict

/-- Row selection followed by a coordinate quantile loses at most a factor
twice the number of agents. Measurability is supplied for the selected set. -/
theorem exists_row_coordinate_capture {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    (S : Set Ω) (row : Ω → Agent) (c : Ω → ℝ) (l : ℝ)
    (hS : MeasurableSet S) (hrow : Measurable row) (hcoord : Measurable c)
    (hl : l < 1) (hc : ∀ ω ∈ S, c ω < 1) :
    ∃ j r, l < r ∧ r < 1 ∧
      MeasurableSet (S ∩ {ω | row ω = j} ∩ {ω | c ω ≤ r}) ∧
      μ.real S / (2 * Fintype.card Agent) ≤
        μ.real (S ∩ {ω | row ω = j} ∩ {ω | c ω ≤ r}) := by
  obtain ⟨j, hj⟩ := exists_large_row (μ := μ) S row
  obtain ⟨r, hlr, hr, hmass⟩ :=
    exists_coordinate_quantile (μ := μ) (S ∩ {ω | row ω = j}) c l hl
      (fun ω hω => hc ω hω.1)
  refine ⟨j, r, hlr, hr, ?_, ?_⟩
  · exact (hS.inter (hrow (measurableSet_singleton j))).inter
      (measurableSet_le hcoord measurable_const)
  · have hhalf := div_le_div_of_nonneg_right hj (by norm_num : (0 : ℝ) ≤ 2)
    calc
      μ.real S / (2 * Fintype.card Agent) =
          (μ.real S / Fintype.card Agent) / 2 := by ring
      _ ≤ μ.real (S ∩ {ω | row ω = j}) / 2 := hhalf
      _ ≤ μ.real (S ∩ {ω | row ω = j} ∩ {ω | c ω ≤ r}) := hmass

end EnvyFreeResearch.Full.FiniteCapture
