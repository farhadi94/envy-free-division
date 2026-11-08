import EnvyFreeResearch.Full.NonnegativeLower

/-!
The public nonnegative input class consists of actual integrable density
rows, normalized on [0,1], bounded almost everywhere between 1/2 and 3/2,
and constant on the cells cut out by finitely many real coordinates.
The cells include singleton boundary points; these are null for volume, so
their values have no effect on the usual finite-step valuation semantics.
-/

namespace EnvyFreeResearch.Full.NonnegativeInputClass

open Set MeasureTheory Metric IntervalOracle IntervalAllocation MixedDensity OracleProtocol
open NonnegativeOracle NonnegativeProfile NonnegativePulse NonnegativeEndpointLaw
open NonnegativeExperiment NonnegativeSuccess NonnegativeRetainedFailure NonnegativeHardFamily
open scoped Classical ENNReal

abbrev Circle := NonnegativeCircle.Circle

def SameCell (endpoints : Finset ℝ) (x y : ℝ) : Prop :=
  ∀ e ∈ endpoints, (e ≤ x ↔ e ≤ y) ∧ (x ≤ e ↔ y ≤ e)

def FiniteStepOnUnit (f : ℝ → ℝ) : Prop :=
  ∃ endpoints : Finset ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    SameCell endpoints x y → f x = f y

structure AdmissibleRow (R : Row) : Prop where
  normalized : R.cumulative 1 = 1
  bounded : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1), 1 / 2 ≤ R.density x ∧ R.density x ≤ 3 / 2
  finite_step : FiniteStepOnUnit R.density

def Admissible {Agent : Type*} (rows : Agent → Row) : Prop := ∀ i, AdmissibleRow (rows i)

theorem cell_finite_step (a b v : ℝ) : FiniteStepOnUnit (Row.cell a b v).density := by
  refine ⟨{a, b}, ?_⟩
  intro x _ y _ hcell
  have ha := hcell a (by simp)
  have hb := hcell b (by simp)
  have hl : a < x ↔ a < y := by simpa only [not_le] using not_congr ha.2
  have hm : x ∈ Ioc a b ↔ y ∈ Ioc a b := and_congr hl hb.2
  change (Ioc a b).indicator (fun _ => v) x = (Ioc a b).indicator (fun _ => v) y
  by_cases hx : x ∈ Ioc a b
  · rw [indicator_of_mem hx, indicator_of_mem (hm.mp hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun hy => hx (hm.mpr hy))]

noncomputable def pulseEndpoints (c r : ℝ) : Finset ℝ :=
  (({-1, 0, 1} : Finset ℤ).image (fun (k : ℤ) => c + (k : ℝ) - r)) ∪
    (({-1, 0, 1} : Finset ℤ).image (fun (k : ℤ) => c + (k : ℝ) + r))

theorem pulse_membership_constant (c r : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (hr : r < 1)
    (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hcell : SameCell (pulseEndpoints c r) x y) :
    (x : Circle) ∈ closedBall (c : Circle) r ↔ (y : Circle) ∈ closedBall (c : Circle) r := by
  have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (t : Circle) ∈ closedBall (c : Circle) r ↔
        ∃ k : ℤ, k ∈ ({-1, 0, 1} : Finset ℤ) ∧ t ∈ Icc (c + (k : ℝ) - r) (c + (k : ℝ) + r) := by
    have hsupport := Set.ext_iff.mp (pulse_support_three_intervals c r hc hr) t
    simpa [ht] using hsupport
  have hleft (k : ℤ) (hk : k ∈ ({-1, 0, 1} : Finset ℤ)) : c + (k : ℝ) - r ∈ pulseEndpoints c r :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  have hright (k : ℤ) (hk : k ∈ ({-1, 0, 1} : Finset ℤ)) : c + (k : ℝ) + r ∈ pulseEndpoints c r :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  rw [hm x hx, hm y hy]
  constructor
  · rintro ⟨k, hk, hkl, hkr⟩
    exact ⟨k, hk, (hcell _ (hleft k hk)).1.mp hkl, (hcell _ (hright k hk)).2.mp hkr⟩
  · rintro ⟨k, hk, hkl, hkr⟩
    exact ⟨k, hk, (hcell _ (hleft k hk)).1.mpr hkl, (hcell _ (hright k hk)).2.mpr hkr⟩

theorem pulse_row_finite_step_real (h c d : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1) (hh : h < 1) :
    FiniteStepOnUnit (row h (c : Circle) (d : Circle)).density := by
  refine ⟨pulseEndpoints c (h / 2) ∪ pulseEndpoints d (h / 2), ?_⟩
  intro x hx y hy hcell
  have hP := pulse_membership_constant c (h / 2) hc (by linarith) x y hx hy
    (fun e he => hcell e (Finset.mem_union_left _ he))
  have hN := pulse_membership_constant d (h / 2) hd (by linarith) x y hx hy
    (fun e he => hcell e (Finset.mem_union_right _ he))
  have hPvalue : (closedBall (c : Circle) (h / 2)).indicator (fun _ => (1 / 2 : ℝ)) (x : Circle) =
      (closedBall (c : Circle) (h / 2)).indicator (fun _ => (1 / 2 : ℝ)) (y : Circle) := by
    by_cases hp : (x : Circle) ∈ closedBall (c : Circle) (h / 2)
    · rw [indicator_of_mem hp, indicator_of_mem (hP.mp hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (fun hy => hp (hP.mpr hy))]
  have hNvalue : (closedBall (d : Circle) (h / 2)).indicator (fun _ => (1 / 2 : ℝ)) (x : Circle) =
      (closedBall (d : Circle) (h / 2)).indicator (fun _ => (1 / 2 : ℝ)) (y : Circle) := by
    by_cases hp : (x : Circle) ∈ closedBall (d : Circle) (h / 2)
    · rw [indicator_of_mem hp, indicator_of_mem (hN.mp hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (fun hy => hp (hN.mpr hy))]
  change (Icc (0 : ℝ) 1).indicator (fun t => circleDensity h (c : Circle) (d : Circle) (t : Circle)) x =
    (Icc (0 : ℝ) 1).indicator (fun t => circleDensity h (c : Circle) (d : Circle) (t : Circle)) y
  rw [indicator_of_mem hx, indicator_of_mem hy]
  simp only [circleDensity, hPvalue, hNvalue]

theorem pulse_row_finite_step (h : ℝ) (c d : Circle) (hh : h < 1) :
    FiniteStepOnUnit (row h c d).density := by
  have hc := representative_range c
  have hd := representative_range d
  have hstep := pulse_row_finite_step_real h (representative c) (representative d)
    ⟨hc.1.le, hc.2⟩ ⟨hd.1.le, hd.2⟩ hh
  simpa only [representative_coe] using hstep

theorem pulse_admissible (h : ℝ) (c d : Circle) (hh : h < 1) : AdmissibleRow (row h c d) := by
  refine ⟨row_total h c d, ?_, pulse_row_finite_step h c d hh⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact row_bounds h c d x hx

theorem uniform_admissible : AdmissibleRow uniformRow := by
  refine ⟨uniform_cumulative 1 (by norm_num), ?_, cell_finite_step 0 1 1⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0)] with x hx hne
  have hxIoc : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hne), hx.2⟩
  simp only [uniformRow, Row.cell, indicator_of_mem hxIoc]
  norm_num

theorem inputRows_admissible {n : ℕ} (h : ℝ) (input : Input n) (hh : h < 1) :
    Admissible (inputRows h input) := by
  intro i
  by_cases hi : i = input.1
  · simpa only [inputRows, perturbedRows, ite_eq_left hi] using pulse_admissible h _ _ hh
  · simpa only [inputRows, perturbedRows, ite_eq_right hi] using uniform_admissible

end EnvyFreeResearch.Full.NonnegativeInputClass

#print axioms EnvyFreeResearch.Full.NonnegativeInputClass.pulse_row_finite_step
#print axioms EnvyFreeResearch.Full.NonnegativeInputClass.inputRows_admissible
