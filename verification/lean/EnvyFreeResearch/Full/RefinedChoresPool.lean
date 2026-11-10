import EnvyFreeResearch.Full.RefinedChoresBucketCapacity

/-! The finite-class weighted-pool obstruction for the root-local schedule.
This module proves no-stalling from actual package weights and their class
map. The physical update and terminal completion must supply those data. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresPool
open RefinedChoresBucketCapacity
open scoped Classical BigOperators

def buckets (n : ℕ) : ℕ := 4*n^2+1
abbrev Class (n : ℕ) :=
  ((Fin n × Finset (Fin n) × Fin (buckets n)) ⊕
    (Fin n × Finset (Fin n) × Finset (Fin n))) ⊕ (Fin n × Finset (Fin n))

def classCount (n : ℕ) : ℕ := n*2^n*buckets n + n*4^n + n*2^n

theorem class_card (n : ℕ) : Fintype.card (Class n) = classCount n := by
  simp only [Class,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_finset]
  unfold classCount
  have h : (2:ℕ)^n * 2^n = 4^n := by rw [← mul_pow]; norm_num
  nlinarith

def liveBound (n : ℕ) : ℕ := n*classCount n
def poolSize (n : ℕ) : ℕ := liveBound n * unpaid n + 1

/-- Every positive admissible package has a defined dyadic bucket from the
finite class universe. -/
def bucket {n : ℕ} (hn : 1 ≤ n) (w : ℕ) (hw : w ≤ unpaid n) : Fin (buckets n) :=
  ⟨Nat.log 2 w,by
    have h := (Nat.log_le_clog 2 w).trans
      (Nat.clog_le_of_le_pow (hw.trans (unpaid_le_power hn)))
    unfold buckets
    omega⟩

theorem bucket_lower {n : ℕ} (hn : 1 ≤ n) (w : ℕ) (hw : w ≤ unpaid n) (hp : 0 < w) :
    2^(bucket hn w hw).val ≤ w := Nat.pow_log_le_self 2 (by omega)

theorem bucket_upper {n : ℕ} (hn : 1 ≤ n) (w : ℕ) (hw : w ≤ unpaid n) :
    w < 2^((bucket hn w hw).val+1) := Nat.lt_pow_succ_log_self (by decide) w

/-- If no class has n+1 roots, the number of live packages is bounded by the
finite class universe. Individual thresholds may be smaller. -/
theorem live_count_bound {Root : Type*} [DecidableEq Root] (n : ℕ)
    (roots : Finset Root) (classify : Root → Class n)
    (hstall : ∀ c, (roots.filter (fun s => classify s = c)).card ≤ n) :
    roots.card ≤ liveBound n := by
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := roots) (t := Finset.univ) (f := classify) (fun _ _ => Finset.mem_univ _)
  rw [hsum]
  calc
    _ ≤ ∑ c : Class n, n := Finset.sum_le_sum (fun c _ => hstall c)
    _ = liveBound n := by simp only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,class_card,liveBound,Nat.mul_comm]

/-- A pool with the prescribed mass and bounded package weights cannot
stall: some class contains at least n+1 live roots. -/
theorem cannot_stall {Root : Type*} [DecidableEq Root] (n : ℕ)
    (roots : Finset Root) (classify : Root → Class n) (weight : Root → ℕ)
    (hweight : ∀ s ∈ roots, weight s ≤ unpaid n)
    (hmass : ∑ s ∈ roots, weight s = poolSize n) :
    ∃ c, n+1 ≤ (roots.filter (fun s => classify s = c)).card := by
  by_contra hn
  have hstall : ∀ c, (roots.filter (fun s => classify s = c)).card ≤ n := by
    intro c
    by_contra hc
    exact hn ⟨c,by omega⟩
  have hcount := live_count_bound n roots classify hstall
  have hsum : ∑ s ∈ roots, weight s ≤ roots.card * unpaid n := by
    calc
      _ ≤ ∑ _s ∈ roots, unpaid n := Finset.sum_le_sum hweight
      _ = _ := by simp
  have hbound := hsum.trans (Nat.mul_le_mul_right (unpaid n) hcount)
  rw [hmass] at hbound
  unfold poolSize at hbound
  omega

end EnvyFreeResearch.Full.RefinedChoresPool
#print axioms EnvyFreeResearch.Full.RefinedChoresPool.cannot_stall
