import EnvyFreeResearch.Full.ChoresOuterDriverChoice
import EnvyFreeResearch.Full.ChoresComponentParameters
import EnvyFreeResearch.R5ChoreSchedule

/-! The population floor is tied to the actual pending-state rank. A
revelation and an entire old-pool batch each consume one rank unit; the
exact floor divisions retain the required reserve under arbitrary order. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler Components EnvyFreeResearch.R5ChoreSchedule
open scoped Classical
variable {n J : ℕ} {RootId : Type*}

def PoolFloor (data : Data n RootId) : Prop :=
  reserve n (Parameters.classes n) (data.pending.rank-2) ≤ data.size

theorem reserve_mono (n B : ℕ) : Monotone (reserve n B) := by
  intro s t h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h)

theorem reserve_base (n B t : ℕ) : B+n*n+1 ≤ reserve n B t := by
  have hp : 1 ≤ (n+1)^t := Nat.one_le_pow _ _ (by omega)
  unfold reserve
  nlinarith

theorem initial_pool_floor [NeZero n] (original : Fin J → Snapshot.Output n)
    (hJ : Parameters.selected n ≤ J) : PoolFloor (initialData original) := by
  unfold PoolFloor
  change reserve n (Parameters.classes n) ((PendingState.initial : PendingState (Fin J) (Fin n)).rank-2) ≤ J
  rw [initial_rank,Fintype.card_fin]
  simpa only [reserve,Parameters.selected,Parameters.exponent,pow_two] using hJ

theorem initial_filtered_pool_floor [NeZero n] (original : Fin J → Snapshot.Output n)
    (roots : List (Fin J)) (hsize : Parameters.selected n ≤ roots.length) :
    PoolFloor ((initialData original).filter roots) := by
  unfold PoolFloor
  change reserve n (Parameters.classes n)
    (((PendingState.initial : PendingState (Fin J) (Fin n)).restrict roots.get).rank-2) ≤ roots.length
  rw [restrict_rank,initial_rank,Fintype.card_fin]
  simpa only [reserve,Parameters.selected,Parameters.exponent,pow_two] using hsize

theorem pool_floor_threshold {data : Data n RootId} (h : PoolFloor data) :
    Parameters.classes n+n ≤ data.size := by
  have hb := reserve_base n (Parameters.classes n) (data.pending.rank-2)
  have hn : n ≤ n*n+1 := by
    by_cases hz : n=0
    · subst n; omega
    · have hm := Nat.mul_le_mul_left n (show 1 ≤ n by omega)
      omega
  unfold PoolFloor at h
  omega

theorem pool_floor_positive {data : Data n RootId} (h : PoolFloor data) : 0 < data.size := by
  have hb := reserve_base n (Parameters.classes n) (data.pending.rank-2)
  unfold PoolFloor at h
  omega

theorem reserve_before_decrease [NeZero n] {data next : Data n RootId}
    (h : PoolFloor data) (hd : next.pending.rank < data.pending.rank) :
    reserve n (Parameters.classes n) (next.pending.rank-2+1) ≤ data.size := by
  have hm := scheduler_rank_min next.pending
  have he : next.pending.rank-2+1 ≤ data.pending.rank-2 := by omega
  exact (reserve_mono n (Parameters.classes n) he).trans h

theorem pool_floor_filter [NeZero n] {data next : Data n RootId}
    (h : PoolFloor data) (hd : next.pending.rank < data.pending.rank)
    (hsize : (data.size-Parameters.classes n)/n ≤ next.size) : PoolFloor next := by
  exact (reserve_filter_step n (Parameters.classes n) (next.pending.rank-2) data.size
    (Nat.pos_of_ne_zero (NeZero.ne n)) (reserve_before_decrease h hd)).trans hsize

theorem pool_floor_batch [NeZero n] {data next : Data n RootId}
    (h : PoolFloor data) (hd : next.pending.rank < data.pending.rank)
    (group : ℕ) (hg : 0 < group) (hle : group ≤ n+1)
    (hsize : data.size/group ≤ next.size) : PoolFloor next := by
  apply le_trans _ hsize
  apply (Nat.le_div_iff_mul_le hg).mpr
  have hb := reserve_before_decrease h hd
  calc
    reserve n (Parameters.classes n) (next.pending.rank-2)*group ≤
        reserve n (Parameters.classes n) (next.pending.rank-2)*(n+1) := Nat.mul_le_mul_left _ hle
    _ = reserve n (Parameters.classes n) (next.pending.rank-2+1) := by
      simp only [reserve,pow_succ,Nat.mul_assoc]
    _ ≤ data.size := hb

end EnvyFreeResearch.Full.Chores.Outer
