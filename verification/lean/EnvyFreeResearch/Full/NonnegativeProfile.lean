import EnvyFreeResearch.Full.NonnegativeOracle
import EnvyFreeResearch.Full.NonnegativePulseGeometry
import EnvyFreeResearch.Full.NonnegativeDetection

namespace EnvyFreeResearch.Full.NonnegativeProfile

open Set MeasureTheory IntervalOracle OracleProtocol MixedDensity NonnegativeOracle
open NonnegativePulse NonnegativePulseGeometry NonnegativeDetection
open scoped Classical

variable {Agent : Type*}
abbrev Circle := NonnegativeCircle.Circle

noncomputable def uniformRow : Row := Row.cell 0 1 1

theorem uniform_cumulative (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : uniformRow.cumulative x = x := by
  rw [uniformRow, Row.cumulative_cell 0 1 1 x (by norm_num) hx.1,
    min_eq_left hx.2, sub_zero, max_eq_left hx.1, one_mul]

noncomputable def uniform : Profile Agent := toProfile (fun _ => uniformRow)

noncomputable def perturbedRows (observer : Agent) (h : ℝ) (c d : Circle) : Agent → Row :=
  fun i => if i = observer then row h c d else uniformRow

noncomputable def perturbed (observer : Agent) (h : ℝ) (c d : Circle) : Profile Agent :=
  toProfile (perturbedRows observer h c d)

theorem perturbed_strictlyPositive (observer : Agent) (h : ℝ) (c d : Circle) :
    StrictlyPositive (perturbed observer h c d) := by
  intro i
  by_cases hi : i = observer
  · simpa only [perturbed, toProfile, perturbedRows, ite_eq_left hi] using
      row_cumulative_strictMonoOn h c d
  · intro a ha b hb hab
    simpa only [perturbed, toProfile, perturbedRows, ite_eq_right hi,
      uniform_cumulative a ha, uniform_cumulative b hb] using hab

theorem perturbed_normalized (observer : Agent) (h : ℝ) (c d : Circle) (i : Agent) :
    (perturbed observer h c d).cumulative i 1 = 1 := by
  by_cases hi : i = observer
  · simpa only [perturbed, toProfile, perturbedRows, ite_eq_left hi] using row_total h c d
  · simpa only [perturbed, toProfile, perturbedRows, ite_eq_right hi] using
      uniform_cumulative 1 (by norm_num)

theorem determiningRight_bounds (P : Profile Agent) (q : Query Agent) (hs : Syntax q) :
    q.left ≤ determiningRight P q ∧ determiningRight P q ≤ q.right := by
  cases q with
  | eval i a b => exact ⟨hs.2.1, le_rfl⟩
  | cut i a b t =>
    cases ho : IntervalOracle.oracle P (.cut i a b t) with
    | none => simpa only [determiningRight, ho, Query.left, Query.right] using ⟨hs.2.1, le_rfl⟩
    | some r =>
      simpa only [determiningRight, ho, Query.left, Query.right, Set.mem_Icc] using
        (oracle_some_valid P (.cut i a b t) r ho).2.1

noncomputable def determiningRequest {n : ℕ} (P : Profile (Fin n)) (q : Query (Fin n)) : Request n :=
  ⟨q.agent, q.left, determiningRight P q⟩

/-- Concrete one-row perturbation preserves the selected determining
integral whenever the chosen row's interval does not separate the centers. -/
theorem determined_by_nondetection (observer : Agent) (h c d : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (q : Query Agent)
    (havoid : q.agent = observer →
      h / 2 < |c - q.left| ∧ h / 2 < |c - determiningRight uniform q| ∧
      h / 2 < |d - q.left| ∧ h / 2 < |d - determiningRight uniform q|)
    (hnoDetect : q.agent = observer →
      (c ∈ Ioc q.left (determiningRight uniform q) ↔
       d ∈ Ioc q.left (determiningRight uniform q))) :
    Determined uniform (perturbed observer h (c : Circle) (d : Circle)) q := by
  intro hs
  have hb := determiningRight_bounds (uniform (Agent := Agent)) q hs
  have haunit : q.left ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.1.trans hs.2.2⟩
  have hbunit : determiningRight uniform q ∈ Icc (0 : ℝ) 1 :=
    ⟨hs.1.trans hb.1, hb.2.trans hs.2.2⟩
  by_cases hi : q.agent = observer
  · obtain ⟨hca, hcb, hda, hdb⟩ := havoid hi
    have hinterval := interval_preserved h c d q.left (determiningRight uniform q) hh
      hc0 hc1 hd0 hd1 hs.1 hb.1 (hb.2.trans hs.2.2) hca hcb hda hdb (hnoDetect hi)
    change (perturbedRows observer h (c : Circle) (d : Circle) q.agent).cumulative
        (determiningRight uniform q) -
      (perturbedRows observer h (c : Circle) (d : Circle) q.agent).cumulative q.left =
      uniformRow.cumulative (determiningRight uniform q) - uniformRow.cumulative q.left
    simp only [perturbedRows, ite_eq_left hi]
    rw [uniform_cumulative _ hbunit, uniform_cumulative _ haunit]
    exact hinterval
  · simp only [perturbed, perturbedRows, uniform, toProfile, ite_eq_right hi]

/-- The determining list is constructed from the actual baseline adaptive
execution. Its length is exactly the answered count plus the single possible
uncounted illegal request. -/
noncomputable def baselineRequests {n : ℕ} {Output : Type*}
    (P : Profile (Fin n)) (execution : Execution (Query (Fin n)) Reply Output) : List (Request n) :=
  (determiningRequests execution).map (determiningRequest P)

theorem baselineRequests_length {n : ℕ} {Output : Type*}
    (P : Profile (Fin n)) (execution : Execution (Query (Fin n)) Reply Output) :
    (baselineRequests P execution).length = execution.answered.length + illegalIndicator execution := by
  rw [baselineRequests, List.length_map, determiningRequests_length]

end EnvyFreeResearch.Full.NonnegativeProfile

#print axioms EnvyFreeResearch.Full.NonnegativeProfile.perturbed_normalized
#print axioms EnvyFreeResearch.Full.NonnegativeProfile.determined_by_nondetection
#print axioms EnvyFreeResearch.Full.NonnegativeProfile.baselineRequests_length
