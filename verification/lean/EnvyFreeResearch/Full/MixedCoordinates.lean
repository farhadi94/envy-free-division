import EnvyFreeResearch.Full.FiniteCapture
import EnvyFreeResearch.TranscriptAdversary

/-! Measurable protection of arbitrary finite output endpoint lists.
The list length is allowed to depend on the tape and need not have a finite
expectation or any uniform bound. -/

namespace EnvyFreeResearch.Full.MixedCoordinates
open Set MeasureTheory TranscriptAdversary

noncomputable def properMaximum : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, c => max (properMaximum k c) (if c k < 1 then c k else 0)

theorem properMaximum_lt_one (k : ℕ) (c : ℕ → ℝ) : properMaximum k c < 1 := by
  induction k with
  | zero => norm_num [properMaximum]
  | succ k ih =>
    simp only [properMaximum, max_lt_iff]
    refine ⟨ih, ?_⟩
    split_ifs with h
    · exact h
    · norm_num

theorem coordinate_le_properMaximum (k : ℕ) (c : ℕ → ℝ)
    (j : ℕ) (hj : j < k) (hc : c j < 1) : c j ≤ properMaximum k c := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases heq : j = k
    · subst j
      simp only [properMaximum, ite_eq_left hc]
      exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_properMaximum (k : ℕ) (c : Ω → ℕ → ℝ)
    (hc : ∀ j, Measurable (fun ω => c ω j)) :
    Measurable (fun ω => properMaximum k (c ω)) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact ih.max ((hc k).ite (measurableSet_lt (hc k) measurable_const) measurable_const)

theorem measurable_variableMaximum (count : Ω → ℕ) (c : Ω → ℕ → ℝ)
    (hcount : Measurable count) (hc : ∀ j, Measurable (fun ω => c ω j)) :
    Measurable (fun ω => properMaximum (count ω) (c ω)) := by
  have hm : Measurable (fun p : Ω × ℕ => properMaximum p.2 (c p.1)) :=
    measurable_from_prod_countable_left (fun k => measurable_properMaximum k c hc)
  exact hm.comp (measurable_id.prodMk hcount)

/-- A single deterministic frontier protects every endpoint for at least half
of a measurable tape set, even with unbounded finite output fragmentation. -/
theorem exists_frozen_coordinates {μ : Measure Ω} [IsFiniteMeasure μ]
    (S : Set Ω) (count : Ω → ℕ) (c : Ω → ℕ → ℝ) (l : ℝ)
    (hS : MeasurableSet S) (hcount : Measurable count)
    (hc : ∀ j, Measurable (fun ω => c ω j)) (hl : l < 1)
    (hunit : ∀ ω ∈ S, ∀ j < count ω, c ω j ≤ 1) :
    ∃ r, l < r ∧ r < 1 ∧
      MeasurableSet (S ∩ {ω | properMaximum (count ω) (c ω) ≤ r}) ∧
      μ.real S / 2 ≤ μ.real (S ∩ {ω | properMaximum (count ω) (c ω) ≤ r}) ∧
      ∀ ω ∈ S ∩ {ω | properMaximum (count ω) (c ω) ≤ r},
        ∀ j < count ω, FrozenCoordinate r (c ω j) := by
  obtain ⟨r, hlr, hr, hmass⟩ := FiniteCapture.exists_coordinate_quantile
    (μ := μ) S (fun ω => properMaximum (count ω) (c ω)) l hl
    (fun ω _ => properMaximum_lt_one _ _)
  refine ⟨r, hlr, hr, hS.inter (measurableSet_le
    (measurable_variableMaximum count c hcount hc) measurable_const), hmass, ?_⟩
  intro ω hω j hj
  by_cases heq : c ω j = 1
  · exact Or.inr heq
  · exact Or.inl ((coordinate_le_properMaximum (count ω) (c ω) j hj
      (lt_of_le_of_ne (hunit ω hω.1 j hj) heq)).trans hω.2)

end EnvyFreeResearch.Full.MixedCoordinates
