import EnvyFreeResearch.Full.UpperGlobalNormalizeSaved
import EnvyFreeResearch.Full.UpperGlobalNormalizeProgram

noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalNormalize
open UpperGlobalPhysical UpperCircularStage
variable {n : ℕ}

theorem execute_snapshot_saved (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (a b : Anchor n) (heq : execute policy fallback chores a = .snapshot b) : Saved a b := by
  have hs := normalize_saved fallback chores n a
  cases hr : normalize fallback chores n a with
  | done c => simp only [execute,hr,requestExecute] at heq; cases heq
  | two c i j => simp only [execute,hr,requestExecute] at heq; cases heq
  | snapshot c =>
    simp only [execute,hr,requestExecute,Phase.snapshot.injEq] at heq
    rw [hr] at hs
    exact heq ▸ hs

end EnvyFreeResearch.Full.UpperGlobalNormalize
