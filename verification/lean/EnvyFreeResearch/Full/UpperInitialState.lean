import EnvyFreeResearch.Full.UpperCorrectionExecution

/-!
# Initial recorded resource from ordinary Eval calls

The literal resource is the closed interval, retaining both endpoints. The
initial all-observer prefix cache is built by the actual query executor;
truthful values and cache presence are proved from the legal reply policy.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperInitialState

open UpperRecordedDomain UpperDomainDifference UpperCircularStage UpperEndpointCache
  UpperCorrectionExecution IntervalOracle Chores

def unitComponent : Component where
  left := 0
  right := 1
  left_nonneg := le_rfl
  left_le_right := zero_le_one
  right_le_one := le_rfl
  carrier := Icc 0 1
  measurable_carrier := measurableSet_Icc
  interior_subset := Ioo_subset_Icc_self
  subset_closed := subset_rfl

def queries (n : ℕ) : List (UpperCircularStage.Query n) := recordings n 0 ++ recordings n 1

def boot {n : ℕ} (policy : Policy n) : State n :=
  ⟨[unitComponent], executeQueries policy (queries n) []⟩

theorem initial_domain {n : ℕ} (policy : Policy n) :
    domain (boot policy).cells = Icc (0 : ℝ) 1 := by simp [boot, domain, unitComponent]

theorem query_count {n : ℕ} (policy : Policy n) :
    (boot policy).history.length = 2 * n := by
  simp [boot, queries, executeQueries_length, recordings, two_mul]

theorem cut_count {n : ℕ} (policy : Policy n) :
    ((boot policy).history.map Prod.fst).countP isCut = 0 := by
  simp [boot, queries, executeQueries_projection, recordings_no_cuts]

theorem queries_legal {n : ℕ} (P : Profile (Fin n)) : ∀ q ∈ queries n, Legal P q := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact recordings_legal P 0 ⟨le_rfl, zero_le_one⟩ q hq
  · exact recordings_legal P 1 ⟨zero_le_one, le_rfl⟩ q hq

/-- Initial well-formedness is obtained from actual ordinary Eval replies;
there is no assumed cache, initial partition, or measure-normalization oracle. -/
theorem boot_wellFormed {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) :
    WellFormed μ (boot policy) := by
  obtain ⟨fresh, hrun, hproj, hvalid⟩ := executeQueries_newReplies (measureProfile μ) policy hpolicy
    (queries n) [] (queries_legal (measureProfile μ))
  have hh : (boot policy).history = fresh := by
    simpa only [boot, List.nil_append] using hrun
  refine ⟨by simp [boot, Ordered], by simp [boot, DisjointComponents], ?_, ?_⟩
  · simpa only [hh, Truthful] using hvalid
  · intro i p hp
    obtain ⟨c, hc, hp⟩ := hp
    have hc' : c = unitComponent := by simpa [boot] using hc
    subst c
    have hp' : p = 0 ∨ p = 1 := hp
    have hq : IntervalOracle.Query.eval i 0 p ∈ fresh.map Prod.fst := by
      rw [hproj]
      rcases hp' with rfl | rfl
      · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨entry, hentry, he⟩ := List.mem_map.mp hq
    refine ⟨entry.2, ?_⟩
    rw [hh]
    have heq : (IntervalOracle.Query.eval i 0 p, entry.2) = entry := Prod.ext he.symm rfl
    rwa [heq]

theorem initial_total {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (i : Fin n) :
    total (boot policy) i = (μ i).real (Icc 0 1) := by
  rw [total_correct μ _ (boot_wellFormed μ policy hpolicy) i, initial_domain]

end EnvyFreeResearch.Full.UpperInitialState
