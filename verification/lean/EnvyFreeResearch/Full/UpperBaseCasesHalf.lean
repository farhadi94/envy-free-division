import EnvyFreeResearch.Full.UpperBaseCasesSplit
import EnvyFreeResearch.Full.UpperRecordedGridProgram

/-! The actual one-Cut half-domain program, with every original observer's
endpoint record and literal refinement. No normalized Cut oracle is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperBaseCases
open UpperRecordedDomain UpperCorrectionExecution UpperDomainDifference UpperGridCells
open UpperGridRecords UpperCircularStage UpperQueryPrograms Chores.QueryProgram
variable {n : ℕ}

def half : I := ⟨1/2,by norm_num,by norm_num⟩
def halfRun (policy : Policy n) (origin : State n) (cutter : Fin n) :=
  UpperRecordedGrid.execute policy (fun (_ : Unit) => cutter) origin 1 (fun _ => ((),half))
def halfProgram (origin : State n) (cutter : Fin n) :=
  UpperRecordedGridProgram.grid (fun (_ : Unit) => cutter) origin 1 (fun _ => ((),half))

theorem half_executes (policy : Policy n) (origin : State n) (cutter : Fin n) :
    ∃ trace, Executes (totalPolicy policy) (halfProgram origin cutter) origin.history
      (halfRun policy origin cutter) trace ∧
      (halfRun policy origin cutter).2.history = origin.history ++ trace ∧
      trace.length ≤ n+1 ∧ (trace.map Prod.fst).countP isCut ≤ 1 := by
  obtain ⟨trace,hrun,heq⟩ := UpperRecordedGridProgram.grid_executes policy
    (fun (_ : Unit) => cutter) origin 1 (fun _ => ((),half))
  have hq := UpperRecordedGrid.query_bound policy (fun (_ : Unit) => cutter) origin 1
    (fun _ => ((),half))
  have hc := UpperRecordedGrid.cut_bound policy (fun (_ : Unit) => cutter) origin 1
    (fun _ => ((),half))
  rw [heq,List.length_append] at hq
  rw [heq,List.map_append,List.countP_append] at hc
  exact ⟨trace,hrun,heq,by omega,by omega⟩

theorem half_domain (policy : Policy n) (origin : State n) (cutter : Fin n) :
    domain (halfRun policy origin cutter).2.cells = domain origin.cells :=
  UpperRecordedGrid.execute_domain policy _ origin 1 _

theorem half_separated (policy : Policy n) (origin : State n) (cutter : Fin n) :
    SeparatedAt ((halfRun policy origin cutter).1 0) (halfRun policy origin cutter).2.cells := by
  apply refineEndpoints_separated
  exact List.mem_ofFn.mpr ⟨0,rfl⟩

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpos : 0 < (μ cutter).real (domain origin.cells))
include hpolicy hgood hpos

theorem half_wellFormed : WellFormed μ (halfRun policy origin cutter).2 :=
  UpperRecordedGrid.execute_wellFormed μ policy hpolicy (fun (_ : Unit) => cutter)
    origin hgood (fun _ => hpos) 1 _

theorem half_prefix_mass :
    (μ cutter).real (domain (leftState (halfRun policy origin cutter).2
      ((halfRun policy origin cutter).1 0)).cells) = (μ cutter).real (domain origin.cells)/2 := by
  rw [prefix_domain _ _ (half_separated policy origin cutter),half_domain]
  have hs := UpperUnionSampling.sampleExecution_spec μ policy hpolicy origin.history cutter
    (values origin cutter) origin.cells hgood.1 hgood.2.1
    (values_correct μ origin hgood cutter) hpos half (by norm_num [half])
  have hpoint : (halfRun policy origin cutter).1 0 =
      (UpperUnionSampling.sampleExecution policy origin.history cutter (values origin cutter)
        ((μ cutter).real (domain origin.cells)) origin.cells half).1 := by
    simp [halfRun,UpperRecordedGrid.execute,UpperRecordedGrid.samples,UpperFreshSamples.run,
      UpperRecordedGrid.step,total_correct μ origin hgood]
  rw [hpoint]
  have hv := hs.2.1
  rw [UpperUnionSampling.normalized_cdf (μ cutter) (domain origin.cells) hpos] at hv
  change _ / (μ cutter).real (domain origin.cells) = (1/2 : ℝ) at hv
  exact (div_eq_iff hpos.ne').mp hv |>.trans (by ring)

end EnvyFreeResearch.Full.UpperBaseCases
