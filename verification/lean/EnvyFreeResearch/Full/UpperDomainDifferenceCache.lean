import EnvyFreeResearch.Full.UpperDomainDifference

/-!
# Exact caches from recorded all-observer prefixes

Every refined component mass is a difference of the already recorded prefix
values at its two bounds. The identity is a measure theorem; component
carriers themselves remain literal sets throughout refinement/subtraction.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain Chores

variable {Observer : Type*}

def cached (values : Observer → ℝ → ℝ) (i : Observer) (c : Component) : ℝ :=
  values i c.right - values i c.left

def PrefixCorrect (μ : Observer → Measure ℝ) (values : Observer → ℝ → ℝ)
    (cs : List Component) : Prop :=
  ∀ i p, Recorded cs p → values i p = (μ i).real (Ioc 0 p)

variable (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem prefix_Ioc_eq_prefixCost (p : ℝ) : μ.real (Ioc 0 p) = prefixCost μ 0 p := by
  apply measureReal_congr
  filter_upwards [μ.ae_ne 0] with x hx
  apply propext
  constructor
  · intro h
    exact ⟨h.1.le, h.2⟩
  · intro h
    exact ⟨lt_of_le_of_ne h.1 hx.symm, h.2⟩

theorem mass_eq_prefix_difference (c : Component) :
    mass μ c = μ.real (Ioc 0 c.right) - μ.real (Ioc 0 c.left) := by
  rw [prefix_Ioc_eq_prefixCost μ, prefix_Ioc_eq_prefixCost μ,
    prefix_difference_eq_interval μ c.left_nonneg c.left_le_right,
    component_mass_eq_interval μ]

variable {μ}

theorem cached_exact {μs : Observer → Measure ℝ}
    [∀ i, IsFiniteMeasure (μs i)] [∀ i, NullSingletonClass (μs i)]
    (values : Observer → ℝ → ℝ) (cs : List Component) (hvalues : PrefixCorrect μs values cs)
    (i : Observer) (c : Component) (hc : c ∈ cs) : cached values i c = mass (μs i) c := by
  rw [mass_eq_prefix_difference]
  exact congrArg₂ (· - ·) (hvalues i c.right ⟨c, hc, Or.inr rfl⟩)
    (hvalues i c.left ⟨c, hc, Or.inl rfl⟩)

theorem cached_left (values : Observer → ℝ → ℝ) (i : Observer)
    (c : Component) (p : ℝ) (hp : c.left ≤ p ∧ p ≤ c.right) :
    cached values i (leftPart c p hp) = values i p - values i c.left := rfl

theorem cached_right_sub (values : Observer → ℝ → ℝ) (i : Observer)
    (c : Component) (p : ℝ) (hp : c.left ≤ p ∧ p ≤ c.right) :
    cached values i (rightPart c p hp) = cached values i c - cached values i (leftPart c p hp) := by
  unfold cached leftPart rightPart
  ring

theorem cached_split_sum (values : Observer → ℝ → ℝ) (i : Observer)
    (c : Component) (p : ℝ) (hp : c.left ≤ p ∧ p ≤ c.right) :
    cached values i (leftPart c p hp) + cached values i (rightPart c p hp) = cached values i c := by
  rw [cached_right_sub]
  ring

theorem prefixCorrect_refineAt {μs : Observer → Measure ℝ}
    (values : Observer → ℝ → ℝ) (cs : List Component) (hvalues : PrefixCorrect μs values cs)
    (p : ℝ) (hp : ∀ i, values i p = (μs i).real (Ioc 0 p)) :
    PrefixCorrect μs values (refineAt p cs) := by
  intro i q hq
  rcases refineAt_recorded p cs hq with rfl | hq
  · exact hp i
  · exact hvalues i q hq

theorem prefixCorrect_filter {μs : Observer → Measure ℝ}
    (values : Observer → ℝ → ℝ) (cs : List Component) (hvalues : PrefixCorrect μs values cs)
    (keep : Component → Bool) : PrefixCorrect μs values (cs.filter keep) :=
  fun i p hp => hvalues i p (filter_recorded cs keep hp)

theorem prefixCorrect_removeCorrection {μs : Observer → Measure ℝ}
    (values : Observer → ℝ → ℝ) (cs : List Component) (hvalues : PrefixCorrect μs values cs)
    (amount : unitInterval) (start : UpperCircular.Circle) (first last : ℝ)
    (hfirst : ∀ i, values i first = (μs i).real (Ioc 0 first))
    (hlast : ∀ i, values i last = (μs i).real (Ioc 0 last)) :
    PrefixCorrect μs values (removeCorrection cs amount start first last) := by
  intro i p hp
  rcases removeCorrection_recorded cs amount start first last hp with rfl | rfl | hp
  · exact hfirst i
  · exact hlast i
  · exact hvalues i p hp

/-- All observers' exact component caches after removing an actual physical
correction use only old recorded prefixes and the two newly recorded ones. -/
theorem removeCorrection_cached_exact {μs : Observer → Measure ℝ}
    [∀ i, IsFiniteMeasure (μs i)] [∀ i, NullSingletonClass (μs i)]
    (values : Observer → ℝ → ℝ) (cs : List Component) (hvalues : PrefixCorrect μs values cs)
    (amount : unitInterval) (start : UpperCircular.Circle) (first last : ℝ)
    (hfirst : ∀ i, values i first = (μs i).real (Ioc 0 first))
    (hlast : ∀ i, values i last = (μs i).real (Ioc 0 last))
    (i : Observer) (c : Component) (hc : c ∈ removeCorrection cs amount start first last) :
    cached values i c = mass (μs i) c :=
  cached_exact values _
    (prefixCorrect_removeCorrection values cs hvalues amount start first last hfirst hlast) i c hc

end EnvyFreeResearch.Full.UpperDomainDifference
