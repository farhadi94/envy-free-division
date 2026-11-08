import EnvyFreeResearch.Full.UpperShrinkProtocol
import EnvyFreeResearch.Full.UpperShrinkCarveFinal

/-! Physical correctness of the prescribed Shrink executor. All carving
premises are discharged by the actual median/floating loop at the chosen
precision, followed by the physical Repair proof. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperShrink
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable UpperRepairProgram

variable {n k : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (policy : Policy n)
  (hp : Admissible (Chores.measureProfile μ) policy) (hk : 3 ≤ k)
  (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (ho : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (G : ℝ) (hG : 1 ≤ G)
  (hmax : G ≤ (2/UpperShrinkPrecision.theta n)*(8/UpperRepair.nearError n)^(k-1))

include hp hk hinj ho hpositive hG hmax in
theorem carving_valid : (carvingExecute policy active origin G).Valid μ active origin G (UpperRepair.nearError n) := by
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective active hinj
  have hf := UpperShrinkPrecision.fraction_range (by omega : 0 < k) hG
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcap : (k:ℝ)*fraction k G ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hf.2 hkR.le
    simpa [ne_of_gt hkR] using h
  have hnorm : (fun i => total origin (active i)) =
      (fun i => (μ (active i)).real (domain origin.cells)) := by
    funext i
    exact total_correct μ origin ho (active i)
  unfold carvingExecute carvingMesh
  rw [hnorm]
  exact UpperShrinkCarve.initialized_valid μ policy hp active origin ho G (UpperRepair.nearError n)
    (UpperShrinkPrecision.depth n k) hpositive hf.1 hcap
    (UpperShrinkPrecision.actual_precision n k hk hkn G (lt_of_lt_of_le zero_lt_one hG) hmax)

variable [Nonempty (Fin k)] (chores : Bool)

include hp hk hinj ho hpositive hG hmax in
theorem success_facts (p : UpperRepair.Tape n k)
    (haccept : (execute policy (by omega) chores active origin G p).2.2=false) :
    SuccessFacts μ chores active (carvingExecute policy active origin G).buffer
      (carvingExecute policy active origin G).old (execute policy (by omega) chores active origin G p) ∧
    ((⋃ j, domain ((execute policy (by omega) chores active origin G p).1 j).cells) ∪
      domain (execute policy (by omega) chores active origin G p).2.1.cells = domain origin.cells) ∧
    (∀ i, 3*(μ (active i)).real (domain origin.cells)/(8*G) ≤
      (μ (active i)).real (domain (execute policy (by omega) chores active origin G p).2.1.cells) ∧
      (μ (active i)).real (domain (execute policy (by omega) chores active origin G p).2.1.cells) ≤
        (μ (active i)).real (domain origin.cells)/G) := by
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective active hinj
  exact repaired_facts μ policy hp (by omega) chores active hinj origin hpositive G
    (lt_of_lt_of_le zero_lt_one hG) (carvingExecute policy active origin G)
    (carving_valid μ policy hp hk active hinj origin ho hpositive G hG hmax)
    (nearError_positive n).le (population_nearError_le_two n k hkn) p haccept

include hp hk hinj ho hpositive hG hmax in
theorem failure_lt (hmeas : MeasurablePolicy policy) :
    UpperRepair.law n k {p | (execute policy (by omega) chores active origin G p).2.2=true} < 1/64 := by
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective active hinj
  exact repair_failure_lt μ policy hp (by omega) chores active hinj origin hpositive G
    (lt_of_lt_of_le zero_lt_one hG) (carvingExecute policy active origin G)
    (carving_valid μ policy hp hk active hinj origin ho hpositive G hG hmax)
    (nearError_positive n).le (population_nearError_le_two n k hkn) hmeas

end EnvyFreeResearch.Full.UpperShrink
