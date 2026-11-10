import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyMesh
import EnvyFreeResearch.Full.UpperShrinkCarveInitial
import EnvyFreeResearch.Full.RefinedUpperShrinkDepthBudget

/-! The prescribed deterministic carving call, including its complete actual
ordinary-query trace. Its iteration count is fixed from the population size. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperShrink
open UpperShrink
open UpperCorrectionExecution UpperCircularStage UpperQueryPrograms UpperShrinkCarve
  Chores.QueryProgram
variable {n k : ℕ}

def carvingMesh (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (G : ℝ) : Mesh n k :=
  roundsExecute policy active (fun i => total origin (active i)) (RefinedUpperShrinkPrecision.depth n k)
    (initial origin (fraction k G))

def carvingProgram (active : Fin k → Fin n) (origin : State n) (G : ℝ) : QProgram n (Carved n k) :=
  (rounds active (fun i => total origin (active i)) (RefinedUpperShrinkPrecision.depth n k)
    (initial origin (fraction k G))).bind (fun mesh => .returned (meshCarve mesh))

def carvingExecute (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (G : ℝ) :=
  meshCarve (carvingMesh policy active origin G)

theorem carving_executes (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (G : ℝ) :
    ∃ trace, Executes (totalPolicy policy) (carvingProgram active origin G) origin.history
      (carvingExecute policy active origin G) trace ∧
      (carvingExecute policy active origin G).buffer.history=origin.history++trace := by
  obtain ⟨tr,he,hh⟩ := rounds_executes policy active (fun i => total origin (active i))
    (RefinedUpperShrinkPrecision.depth n k) (initial origin (fraction k G))
  refine ⟨tr,?_,hh⟩
  simpa [carvingProgram,carvingExecute,carvingMesh,initial] using he.bind (fun mesh => .returned (meshCarve mesh)) (Executes.returned _ _)

theorem carving_cost (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (hk : 0 < k) (hkn : k ≤ n) (G : ℝ) (hG : 1 ≤ G) :
    ∃ trace, Executes (totalPolicy policy) (carvingProgram active origin G) origin.history
      (carvingExecute policy active origin G) trace ∧
      (carvingExecute policy active origin G).buffer.history=origin.history++trace ∧
      trace.length ≤ (n+1)*RefinedUpperRepair.fine n ∧
      (trace.map Prod.fst).countP isCut ≤ RefinedUpperRepair.fine n := by
  obtain ⟨tr,he,hh⟩ := carving_executes policy active origin G
  have hf := RefinedUpperShrinkPrecision.fraction_range hk hG
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcap : (k : ℝ)*fraction k G ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hf.2 hkR.le
    simpa [ne_of_gt hkR] using hh
  have hq := initialized_query_bound policy active (fun i => total origin (active i))
    (RefinedUpperShrinkPrecision.depth n k) origin (fraction k G) hf.1 hcap
  have hc := initialized_cut_bound policy active (fun i => total origin (active i))
    (RefinedUpperShrinkPrecision.depth n k) origin (fraction k G) hf.1 hcap
  have hm := RefinedUpperShrinkPrecision.actual_cut_budget n k hkn
  have hq' : (carvingExecute policy active origin G).buffer.history.length ≤
      origin.history.length+(n+1)*RefinedUpperRepair.fine n := by
    change (carvingMesh policy active origin G).history.length ≤ _
    have hb : RefinedUpperShrinkPrecision.depth n k*k^3*(n+1) ≤ (n+1)*RefinedUpperRepair.fine n := by
      nlinarith
    exact hq.trans (Nat.add_le_add_left hb _)
  have hc' : cuts (carvingExecute policy active origin G).buffer.history ≤
      cuts origin.history+RefinedUpperRepair.fine n := by
    change cuts (carvingMesh policy active origin G).history ≤ _
    have hb : RefinedUpperShrinkPrecision.depth n k*k^3 ≤ RefinedUpperRepair.fine n := by nlinarith
    exact hc.trans (Nat.add_le_add_left hb _)
  rw [hh,List.length_append] at hq'
  rw [hh] at hc'
  simp only [cuts,List.map_append,List.countP_append] at hc'
  exact ⟨tr,he,hh,by omega,by omega⟩

end EnvyFreeResearch.Full.RefinedUpperShrink
