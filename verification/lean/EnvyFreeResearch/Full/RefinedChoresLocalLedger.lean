import EnvyFreeResearch.Full.RefinedChoresChildLedger

/-! Actual preprocessing and paid-prefix calls fit the native local
allowance before recursive child recording is added. -/
namespace EnvyFreeResearch.Full.RefinedChoresParameters
open Chores

theorem local_query_ledger {n : ℕ} (hn : 3 ≤ n) :
    snapshots n*Snapshot.queryBudget n+selected n*ComponentRecording.budget n n+
      ComponentRecording.budget n n+19*n*2^n+childQueries n ≤ (totalCapacity n).queries := by
  have hlocal := local_queries_envelope hn
  have hcap := local_child_queries (by omega : 0 < n)
  unfold localQueries at hlocal
  rw [Nat.add_mul,one_mul] at hlocal
  omega

theorem local_cut_ledger {n : ℕ} (hn : 3 ≤ n) :
    snapshots n*Snapshot.queryBudget n+selected n*ComponentRecording.budget n n+
      ComponentRecording.budget n n+19*2^n+childCuts n ≤ (totalCapacity n).cuts := by
  have hlocal := local_queries_envelope hn
  have hcap := local_child_cuts (by omega : 0 < n)
  have hfinish : 19*2^n ≤ 19*n*2^n := by
    exact Nat.mul_le_mul_right _ (by omega : 19 ≤ 19*n)
  unfold localQueries at hlocal
  rw [Nat.add_mul,one_mul] at hlocal
  omega

theorem preprocessing_capacity {n : ℕ} (hn : 3 ≤ n) :
    snapshots n*Snapshot.queryBudget n ≤ (totalCapacity n).queries ∧
      snapshots n*Snapshot.queryBudget n ≤ (totalCapacity n).cuts := by
  have hq := local_query_ledger hn
  have hc := local_cut_ledger hn
  omega

end EnvyFreeResearch.Full.RefinedChoresParameters
