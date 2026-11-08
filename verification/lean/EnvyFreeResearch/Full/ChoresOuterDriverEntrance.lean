import EnvyFreeResearch.Full.ChoresOuterDriverReserve
import EnvyFreeResearch.Full.ChoresOuterEntrance

/-! Driver fuel, protected-label invariant and population reserve at the
actual finite cached entrance selection, including all closed old roots. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler
variable {n J : ℕ} (original : Fin J → Snapshot.Output n)
    (a : EntranceChoice n J) (c : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (ha : a.Admissible original c r H (Parameters.selected n))
include ha

theorem entrance_protected : Protected (a.data original) original c a.pivot r H := by
  constructor
  · rfl
  · intro s
    exact ha.2.2 (a.roots.toList.get s) (Finset.mem_toList.mp (List.get_mem _ s))

theorem entrance_pool_floor [NeZero n] : PoolFloor (a.data original) := by
  apply initial_filtered_pool_floor original a.roots.toList
  simpa only [Finset.length_toList] using ha.2.1.ge

omit ha in
theorem entrance_rank [NeZero n] : (a.data original).pending.rank=3*n := by
  change ((PendingState.initial : PendingState (Fin J) (Fin n)).restrict a.roots.toList.get).rank=_
  rw [restrict_rank,initial_rank,Fintype.card_fin]

omit ha in
theorem entrance_driver_fuel [NeZero n] :
    (a.data original).pending.rank ≤ Parameters.exponent n+2 := by
  rw [entrance_rank]
  unfold Parameters.exponent
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

end EnvyFreeResearch.Full.Chores.Outer
