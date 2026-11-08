import EnvyFreeResearch.Full.ChoresSchedulerCounts
import EnvyFreeResearch.R5ChoreSchedule

/-! Actual disjoint old-pool batches and the one-unit integer reserve inequalities. -/

namespace EnvyFreeResearch.Full.Chores.Scheduler

variable {Root : Type*}

def groups (pool : List Root) (size : ℕ) : List (List Root) :=
  (List.replicate (pool.length / size) size).splitLengths
    (pool.take (size * (pool.length / size)))

def leftovers (pool : List Root) (size : ℕ) : List Root :=
  pool.drop (size * (pool.length / size))

@[simp] theorem groups_length (pool : List Root) (size : ℕ) :
    (groups pool size).length = pool.length / size := by simp [groups]

theorem group_lengths (pool : List Root) (size : ℕ) :
    (groups pool size).map List.length = List.replicate (pool.length / size) size := by
  apply List.map_splitLengths_length
  simp only [List.sum_replicate, List.length_take]
  rw [min_eq_left (Nat.mul_div_le _ _)]
  simp [nsmul_eq_mul, Nat.mul_comm]

theorem group_length (pool : List Root) (size : ℕ) {group : List Root}
    (hgroup : group ∈ groups pool size) : group.length = size := by
  have hmem : group.length ∈ (groups pool size).map List.length := List.mem_map.mpr
    ⟨group, hgroup, rfl⟩
  rw [group_lengths] at hmem
  exact (List.mem_replicate.mp hmem).2

theorem groups_flatten (pool : List Root) (size : ℕ) :
    (groups pool size).flatten = pool.take (size * (pool.length / size)) := by
  apply List.flatten_splitLengths
  simp only [List.length_take, List.sum_replicate]
  rw [min_eq_left (Nat.mul_div_le _ _)]
  simp [nsmul_eq_mul, Nat.mul_comm]

theorem batches_partition (pool : List Root) (size : ℕ) :
    (groups pool size).flatten ++ leftovers pool size = pool := by
  rw [groups_flatten]
  exact List.take_append_drop _ _

theorem leftovers_length (pool : List Root) (size : ℕ) :
    (leftovers pool size).length = pool.length % size := by
  simp only [leftovers, List.length_drop]
  have h := Nat.mod_add_div pool.length size
  omega

theorem groups_nodup (pool : List Root) (size : ℕ) (hnodup : pool.Nodup) :
    (groups pool size).flatten.Nodup := by
  rw [groups_flatten]
  exact hnodup.take

theorem groups_leftovers_disjoint (pool : List Root) (size : ℕ) (hnodup : pool.Nodup) :
    List.Disjoint (groups pool size).flatten (leftovers pool size) := by
  apply List.Nodup.disjoint
  rwa [batches_partition]

/-- Choosing one survivor in each reserved batch never repeats an old root. -/
theorem survivors_nodup (batches : List (List Root)) (hnodup : batches.flatten.Nodup)
    (choose : List Root → Root) (hchoose : ∀ group ∈ batches, choose group ∈ group) :
    (batches.map choose).Nodup := by
  induction batches with
  | nil => simp
  | cons group rest ih =>
    simp only [List.flatten_cons] at hnodup
    have hrest := hnodup.of_append_right
    have hdis := hnodup.disjoint
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
      have hleft := hchoose group (List.mem_cons_self)
      have hright : choose group ∈ rest.flatten := by
        rw [List.mem_flatten]
        exact ⟨other, hother, heq ▸ hchoose other (List.mem_cons_of_mem _ hother)⟩
      exact List.disjoint_left.mp hdis hleft hright
    · exact ih hrest (fun other ho => hchoose other (List.mem_cons_of_mem _ ho))

theorem committed_pool (pool : List Root) (size : ℕ) (hnodup : pool.Nodup)
    (choose : List Root → Root) (hchoose : ∀ group ∈ groups pool size, choose group ∈ group) :
    ((groups pool size).map choose).Nodup ∧
      ((groups pool size).map choose).length = pool.length / size := by
  exact ⟨survivors_nodup _ (groups_nodup pool size hnodup) choose hchoose, by simp⟩

open EnvyFreeResearch.R5ChoreSchedule

/-- A merger round costs one exponent unit because its actual group size is at most n+1. -/
theorem reserve_group_step (n B t size pool : ℕ) (hsize : 0 < size)
    (hbound : size ≤ n + 1) (hpool : reserve n B (t + 1) ≤ pool) :
    reserve n B t ≤ pool / size := by
  apply (Nat.le_div_iff_mul_le hsize).mpr
  calc
    reserve n B t * size ≤ reserve n B t * (n + 1) := Nat.mul_le_mul_left _ hbound
    _ = reserve n B (t + 1) := by simp only [reserve, pow_succ]; ring
    _ ≤ pool := hpool

theorem committed_reserve (pool : List Root) (n B t size : ℕ) (hsize : 0 < size)
    (hbound : size ≤ n + 1) (hpool : reserve n B (t + 1) ≤ pool.length)
    (choose : List Root → Root) :
    reserve n B t ≤ ((groups pool size).map choose).length := by
  simpa using reserve_group_step n B t size pool.length hsize hbound hpool

end EnvyFreeResearch.Full.Chores.Scheduler
