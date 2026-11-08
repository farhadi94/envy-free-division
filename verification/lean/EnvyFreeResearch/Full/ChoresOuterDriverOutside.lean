import EnvyFreeResearch.Full.ChoresOuterDriverTransitions

/-! The actual continuing revelation preserves the driver entrance
invariants, including the whole population reserve and protected label. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory Scheduler Components
open scoped Classical
variable {n : ℕ} [NeZero n] {RootId : Type*} [Fintype RootId]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c pivot : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (data : Data n RootId)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hpool : PoolFloor data)
  (hprotected : Protected data (fun root => xs.get (index root)) c pivot (fun i => (cost i).real R) H)
  (p : Fin n) (hp : p ∈ data.pending.partition.labels) (hnew : p ∉ data.pending.pending)
  (roots : List (Fin data.size)) (target : Fin n)
  (hchoice : revelationChoice data (fun root => xs.get (index root)) p
    (fun i => (cost i).real R) H=.outside target roots)
include hsound hsep hr hH hscale good hpool hprotected hp hnew hchoice

theorem driver_outside_step : ∃ updated : Data n RootId,
    outsideCommit data (fun root => xs.get (index root)) p hp (fun i => (cost i).real R) H roots target=some updated ∧
    updated.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H ∧
    PoolFloor updated ∧
    Protected updated (fun root => xs.get (index root)) c pivot (fun i => (cost i).real R) H ∧
    updated.pending.rank < data.pending.rank ∧ updated.size ≤ data.size ∧ updated.cache=data.cache := by
  have ht : n*(4^n+2^n)+n ≤ data.size := pool_floor_threshold hpool
  obtain ⟨updated,hcommit,hgood,hsize,hfloor,hcache,hpartition,hpending,halloc⟩ :=
    outside_commit_correct cost xs index c hsound R H hsep hr hH hscale data good p hp roots target hchoice ht
  have hd := outside_commit_rank data _ p hp hnew _ H roots target updated hcommit
  have hp' := outside_commit_protected data _ p hp c pivot _ H hprotected roots target updated hcommit
  have hc := revelation_choice_correct data (fun root => xs.get (index root)) p (fun i => (cost i).real R) H
  rw [hchoice] at hc
  have hnd : roots.Nodup := hc.1
  have hcard := Finset.card_le_univ roots.toFinset
  rw [List.toFinset_card_of_nodup hnd,Fintype.card_fin] at hcard
  exact ⟨updated,hcommit,hgood,pool_floor_filter hpool hd hfloor,hp',hd,hsize ▸ hcard,hcache⟩

end EnvyFreeResearch.Full.Chores.Outer
