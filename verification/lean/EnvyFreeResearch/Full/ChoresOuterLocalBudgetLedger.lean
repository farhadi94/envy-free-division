import EnvyFreeResearch.Full.ChoresOuterLocalBudget
import EnvyFreeResearch.Full.ChoresOuterDriverBudget

/-! The actual preprocessing, outer scheduler, terminal compensation and
recursive completion ledger, in ordinary queries and Cuts separately. -/
namespace EnvyFreeResearch.Full.Chores.Outer
open Parameters Population

theorem selected_terminal_charge {n size unit : ℕ} (hn : 2 ≤ n)
    (hpos : 0 < size) (hsize : size ≤ selected n) :
    (selected n-size)*unit+unit ≤ roots n*unit := by
  have hsr := selected_le_roots hn
  have hs : selected n-size+1 ≤ roots n := by omega
  simpa only [Nat.add_mul,one_mul] using Nat.mul_le_mul_right unit hs

theorem local_query_ledger {n size : ℕ} (hn : 3 ≤ n)
    (hpos : 0 < size) (hsize : size ≤ selected n) :
    snapshots n*Snapshot.queryBudget n+
      (selected n-size)*ComponentRecording.budget n n+ComponentRecording.budget n n+
      19*n*2^n+childQueries n ≤ (totalCapacity n).queries := by
  have hcharge := selected_terminal_charge (unit := ComponentRecording.budget n n) (by omega) hpos hsize
  have he := local_child_queries (show 0 < n by omega)
  rw [nativeLocalQueries,if_neg (by omega)] at he
  unfold localQueries at he
  omega

theorem local_cut_ledger {n size : ℕ} (hn : 3 ≤ n)
    (hpos : 0 < size) (hsize : size ≤ selected n) :
    snapshots n*Snapshot.cutBudget n+
      (selected n-size)*SubCore.sourceBudget n+SubCore.sourceBudget n+
      19*2^n+childCuts n ≤ (totalCapacity n).cuts := by
  have hcharge := selected_terminal_charge (unit := SubCore.sourceBudget n) (by omega) hpos hsize
  have he := local_child_cuts (show 0 < n by omega)
  rw [nativeLocalCuts,if_neg (by omega)] at he
  unfold localCuts at he
  omega

theorem local_query_ledger_of_bounds {n size prepare driver terminal finish : ℕ}
    (hn : 3 ≤ n) (hpos : 0 < size) (hsize : size ≤ selected n)
    (hprep : prepare ≤ snapshots n*Snapshot.queryBudget n)
    (hdriver : driver ≤ (selected n-size)*ComponentRecording.budget n n)
    (hterminal : terminal ≤ ComponentRecording.budget n n)
    (hfinish : finish ≤ 19*n*2^n+childQueries n) :
    prepare+driver+terminal+finish ≤ (totalCapacity n).queries := by
  have h := local_query_ledger hn hpos hsize
  omega

theorem local_cut_ledger_of_bounds {n size prepare driver terminal finish : ℕ}
    (hn : 3 ≤ n) (hpos : 0 < size) (hsize : size ≤ selected n)
    (hprep : prepare ≤ snapshots n*Snapshot.cutBudget n)
    (hdriver : driver ≤ (selected n-size)*SubCore.sourceBudget n)
    (hterminal : terminal ≤ SubCore.sourceBudget n)
    (hfinish : finish ≤ 19*2^n+childCuts n) :
    prepare+driver+terminal+finish ≤ (totalCapacity n).cuts := by
  have h := local_cut_ledger hn hpos hsize
  omega

theorem preprocessing_queries_capacity {n : ℕ} (hn : 3 ≤ n) :
    snapshots n*Snapshot.queryBudget n ≤ (totalCapacity n).queries := by
  have he := local_child_queries (show 0 < n by omega)
  rw [nativeLocalQueries,if_neg (by omega)] at he
  unfold localQueries at he
  omega

theorem preprocessing_cuts_capacity {n : ℕ} (hn : 3 ≤ n) :
    snapshots n*Snapshot.cutBudget n ≤ (totalCapacity n).cuts := by
  have he := local_child_cuts (show 0 < n by omega)
  rw [nativeLocalCuts,if_neg (by omega)] at he
  unfold localCuts at he
  omega

end EnvyFreeResearch.Full.Chores.Outer
