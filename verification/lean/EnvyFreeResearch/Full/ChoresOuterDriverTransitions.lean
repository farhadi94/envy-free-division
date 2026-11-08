import EnvyFreeResearch.Full.ChoresOuterDriverReserve
import EnvyFreeResearch.Full.ChoresOuterBatchCommit

/-! Rank, pool survival and group charging for literal continuing updates. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler Components
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem outside_commit_rank (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (p : Fin n) (hp : p ∈ data.pending.partition.labels) (hnew : p ∉ data.pending.pending)
    (r : Fin n → ℝ) (H : ℝ) (roots : List (Fin data.size)) (target : Fin n)
    (updated : Data n RootId)
    (hcommit : outsideCommit data original p hp r H roots target=some updated) :
    updated.pending.rank < data.pending.rank := by
  letI : Nonempty (Fin n) := ⟨p⟩
  unfold outsideCommit at hcommit
  dsimp only at hcommit
  split at hcommit
  next h =>
    have he := Option.some.inj hcommit
    subst updated
    have hfresh : p ∉ (data.filter roots).pending.pending := by
      change p ∉ (data.pending.restrict roots.get).pending
      rw [PendingState.restrict_pending]
      exact hnew
    have hd := (data.filter roots).pending.reveal_rank p hp hfresh _ h
    exact hd.trans_eq (restrict_rank data.pending roots.get)
  next h => cases hcommit

theorem outside_commit_protected (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (c pivot : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (hprotected : Protected data original c pivot r H)
    (roots : List (Fin data.size)) (target : Fin n) (updated : Data n RootId)
    (hcommit : outsideCommit data original p hp r H roots target=some updated) :
    Protected updated original c pivot r H := by
  unfold outsideCommit at hcommit
  dsimp only at hcommit
  split at hcommit
  next h =>
    have he := Option.some.inj hcommit
    subst updated
    exact (hprotected.filter roots).reveal p hp _ h
  next h => cases hcommit

variable (data : Data n RootId) (hall : data.pending.partition.labels ⊆ data.pending.pending)
    (cycle : ProposalCycle (data.pending.outgoing hall))
    (original : RootId → Snapshot.Output n) (outputs : List (GroupResult data hall cycle))
    (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)

theorem commit_rank :
    (commitBatch data hall cycle original outputs keep hk).pending.rank < data.pending.rank := by
  letI : Nonempty (Fin n) := ⟨keep⟩
  change ((data.pending.merge _ keep _ hk).restrict (batchSurvivor data hall cycle outputs)).rank < _
  rw [restrict_rank]
  exact data.pending.merge_rank _ keep (data.pending.selected_subset hall cycle) hk
    (fun a ha => hall (data.pending.selected_subset hall cycle ha)) (data.pending.selected_two hall cycle)

theorem commit_pool_floor [NeZero n] (hf : PoolFloor data)
    (hgroups : outputs.map GroupResult.group=cohorts data hall cycle) :
    PoolFloor (commitBatch data hall cycle original outputs keep hk) := by
  apply pool_floor_batch hf (commit_rank data hall cycle original outputs keep hk)
    (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1) (by omega)
  · have hcard := data.pending.partition.tasks_card_le (data.pending.selected hall cycle)
    simpa only [ComponentBatch.Task,Fintype.card_coe,Fintype.card_fin] using Nat.add_le_add_right hcard 1
  · exact (commit_batch_size data hall cycle original outputs keep hk hgroups).ge

/-- Each completed group uses a distinct donor in addition to its survivor.
Thus its one call can be charged to the exact decrease of the old pool. -/
theorem commit_group_charge
    (hgroups : outputs.map GroupResult.group=cohorts data hall cycle) :
    outputs.length+(commitBatch data hall cycle original outputs keep hk).size ≤ data.size := by
  have ht : 0 < Fintype.card (ComponentBatch.Task data.pending hall cycle) :=
    Fintype.card_pos_iff.mpr ⟨⟨(data.pending.partition.tasks_nonempty _
      (data.pending.selected_subset hall cycle)
      (Finset.card_pos.mp (by have := data.pending.selected_two hall cycle; omega))).choose,
      (data.pending.partition.tasks_nonempty _ (data.pending.selected_subset hall cycle)
      (Finset.card_pos.mp (by have := data.pending.selected_two hall cycle; omega))).choose_spec⟩⟩
  have hs := commit_batch_size data hall cycle original outputs keep hk hgroups
  have hlen : outputs.length=data.size/(Fintype.card (ComponentBatch.Task data.pending hall cycle)+1) := hs
  have hm := Nat.div_mul_le_self data.size (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1)
  rw [← hlen] at hm
  change outputs.length+outputs.length ≤ data.size
  nlinarith

end EnvyFreeResearch.Full.Chores.Outer
