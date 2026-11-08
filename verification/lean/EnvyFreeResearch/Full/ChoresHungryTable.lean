import EnvyFreeResearch.Full.ChoresAnchored
import EnvyFreeResearch.Full.ChoresPersistent

/-!
# One normalized hungry Core profile for the complete finite record table

All parents are parameterized by `[0,1]`, with every old formal record at an
explicit distinct normalized coordinate. A single perturbation preserves all
cross-parent comparisons and equalities, including records retained from
failed candidates. The constructed profile has the exact `HungryCosts` type
consumed by the unconditional Core and memoization theorems.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open Set

/-- The weak lexicographic comparison used by cached EF tests. -/
def recordLE (a b : ℝ × ℚ) : Prop := recordLT a b ∨ a = b

lemma recordLE_primary_le {a b : ℝ × ℚ} (h : recordLE a b) : a.1 ≤ b.1 := by
  rcases h with h | rfl
  · exact Persistent.recordLT_primary_le h
  · exact le_rfl

def recordPosition (length : ℕ) (k : Fin (length + 1)) : ℝ := (k : ℝ) / length

lemma recordPosition_mem (length : ℕ) (hpos : 0 < length) (k : Fin (length + 1)) :
    recordPosition length k ∈ Icc (0 : ℝ) 1 := by
  have hl : (0 : ℝ) < length := by exact_mod_cast hpos
  refine ⟨div_nonneg (by positivity) hl.le, ?_⟩
  apply (div_le_one hl).mpr
  exact_mod_cast Nat.le_of_lt_succ k.isLt

lemma recordPosition_zero (length : ℕ) : recordPosition length 0 = 0 := by simp [recordPosition]

lemma recordPosition_last (length : ℕ) (hpos : 0 < length) :
    recordPosition length (Fin.last length) = 1 := by
  simp [recordPosition, ne_of_gt hpos]

lemma recordPosition_strictMono (length : ℕ) (hpos : 0 < length) : StrictMono (recordPosition length) := by
  intro a b hab
  apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hpos : (0 : ℝ) < length)).mpr
  exact_mod_cast hab

/-- Actual globally compatible hungry functions, rather than a postulated
successful record interface. Every recorded equality is realized exactly. -/
theorem simultaneous_hungry_profile (n : ℕ) (length : Fin n → ℕ)
    (hlength : ∀ p, 0 < length p)
    (record : Fin n → (p : Fin n) → Fin (length p + 1) → ℝ × ℚ)
    (hzero : ∀ i p, record i p 0 = (0, 0))
    (hstrict : ∀ i p (j k : Fin (length p + 1)), j < k →
      recordLT (record i p j) (record i p k)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : Core.HungryCosts n,
      (∀ i p k, C.cost i p (recordPosition (length p) k) = realizedCost ε (record i p k)) ∧
      (∀ i p k j q l,
        (recordLT (record i p k) (record j q l) ↔
          C.cost i p (recordPosition (length p) k) < C.cost j q (recordPosition (length q) l)) ∧
        (record i p k = record j q l ↔
          C.cost i p (recordPosition (length p) k) = C.cost j q (recordPosition (length q) l)) ∧
        (recordLE (record i p k) (record j q l) ↔
          C.cost i p (recordPosition (length p) k) ≤ C.cost j q (recordPosition (length q) l))) := by
  let Index := Fin n × ((p : Fin n) × Fin (length p + 1))
  let values : Index → ℝ × ℚ := fun r => record r.1 r.2.1 r.2.2
  obtain ⟨ε, hε, hcompare⟩ := exists_exact_comparison_realization values
  let v := fun i p k => realizedCost ε
    (record i p ⟨min k (length p), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
  have hv (i p : Fin n) (k : ℕ) (hk : k ≤ length p) :
      v i p k = realizedCost ε (record i p ⟨k, Nat.lt_succ_of_le hk⟩) := by
    simp only [v, Nat.min_eq_left hk]
  have hvzero (i p : Fin n) : v i p 0 = 0 := by
    rw [hv i p 0 (Nat.zero_le _)]
    simp [hzero i p, realizedCost]
  have hvstrict (i p : Fin n) : ∀ k < length p, v i p k < v i p (k + 1) := by
    intro k hk
    rw [hv i p k hk.le, hv i p (k + 1) (Nat.succ_le_of_lt hk)]
    apply (hcompare ⟨i, ⟨p, ⟨k, Nat.lt_succ_of_le hk.le⟩⟩⟩
      ⟨i, ⟨p, ⟨k + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hk)⟩⟩⟩).1.mp
    exact hstrict i p _ _ (by change k < k + 1; omega)
  have hlen (p : Fin n) : (0 : ℝ) < length p := by exact_mod_cast hlength p
  have hscaled (p : Fin n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
      (length p : ℝ) * x ∈ Icc (0 : ℝ) (length p) := by
    refine ⟨mul_nonneg (hlen p).le hx.1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2 (hlen p).le
  let C : Core.HungryCosts n := {
    cost := fun i p x => prefixInterpolation (length p) (v i p) ((length p : ℝ) * x)
    continuous := fun i p => ((prefixInterpolation_continuous (length p) (v i p)).comp
      (show Continuous (fun x : ℝ => (length p : ℝ) * x) by fun_prop)).continuousOn
    strict := fun i p x hx y hy hxy => prefixInterpolation_strictMonoOn (length p) (v i p)
      (hvstrict i p) (hscaled p hx) (hscaled p hy) (mul_lt_mul_of_pos_left hxy (hlen p))
    zero := fun i p => by
      rw [mul_zero]
      simpa only [Nat.cast_zero, hvzero i p] using
        prefixInterpolation_at_record (length p) (v i p) 0 (Nat.zero_le _) }
  have hrecord (i p : Fin n) (k : Fin (length p + 1)) :
      C.cost i p (recordPosition (length p) k) = realizedCost ε (record i p k) := by
    change prefixInterpolation (length p) (v i p) ((length p : ℝ) * ((k : ℝ) / length p)) = _
    rw [mul_div_cancel₀ _ (ne_of_gt (hlen p)),
      prefixInterpolation_at_record _ _ k.val (Nat.le_of_lt_succ k.isLt)]
    exact hv i p k.val (Nat.le_of_lt_succ k.isLt)
  refine ⟨ε, hε, C, hrecord, ?_⟩
  intro i p k j q l
  rw [hrecord, hrecord]
  have hc := hcompare ⟨i, ⟨p, k⟩⟩ ⟨j, ⟨q, l⟩⟩
  dsimp only [values] at hc
  refine ⟨hc.1, hc.2, ?_⟩
  simp only [recordLE, hc.1, hc.2, le_iff_lt_or_eq]

namespace Core

/-- A cached state refers to immutable records on the corresponding parents. -/
structure RecordState {n : ℕ} (length : Fin n → ℕ) where
  endpoint : (p : Fin n) → Fin (length p + 1)
  matching : Equiv.Perm (Fin n)

def RecordState.realize {n : ℕ} {length : Fin n → ℕ} (s : RecordState length) : State n :=
  ⟨fun p => recordPosition (length p) (s.endpoint p), s.matching⟩

def RecordState.FormalEF {n : ℕ} {length : Fin n → ℕ}
    (record : Fin n → (p : Fin n) → Fin (length p + 1) → ℝ × ℚ)
    (s : RecordState length) : Prop := ∀ i p,
  recordLE (record i (s.matching i) (s.endpoint (s.matching i))) (record i p (s.endpoint p))

def RecordState.FormalAnchored {n : ℕ} {length : Fin n → ℕ}
    (record : Fin n → (p : Fin n) → Fin (length p + 1) → ℝ × ℚ)
    (s : RecordState length) : Prop := ∃ rank : Fin n → ℕ, ∀ i,
  s.endpoint (s.matching i) = Fin.last (length (s.matching i)) ∨
    ∃ j, rank j < rank i ∧ record i (s.matching j) (s.endpoint (s.matching j)) =
      record i (s.matching i) (s.endpoint (s.matching i))

lemma RecordState.realize_feasible {n : ℕ} {length : Fin n → ℕ}
    (hlength : ∀ p, 0 < length p) (s : RecordState length) : Feasible s.realize :=
  fun p => recordPosition_mem (length p) (hlength p) (s.endpoint p)

/-- The same single realization preserves every complete EF decision on every
record-state; it is not chosen anew for individual candidates. -/
lemma RecordState.realize_envyFree_iff {n : ℕ} {length : Fin n → ℕ}
    (record : Fin n → (p : Fin n) → Fin (length p + 1) → ℝ × ℚ)
    (C : HungryCosts n)
    (hweak : ∀ i p k q l, recordLE (record i p k) (record i q l) ↔
      C.cost i p (recordPosition (length p) k) ≤ C.cost i q (recordPosition (length q) l))
    (s : RecordState length) : EnvyFree C.cost s.realize ↔ s.FormalEF record := by
  constructor <;> intro h i p
  · exact (hweak i _ _ _ _).mpr (h i p)
  · exact (hweak i _ _ _ _).mp (h i p)

lemma RecordState.realize_anchored {n : ℕ} {length : Fin n → ℕ}
    (hlength : ∀ p, 0 < length p)
    (record : Fin n → (p : Fin n) → Fin (length p + 1) → ℝ × ℚ)
    (C : HungryCosts n)
    (hequal : ∀ i p k q l, record i p k = record i q l →
      C.cost i p (recordPosition (length p) k) = C.cost i q (recordPosition (length q) l))
    (s : RecordState length) (hs : s.FormalAnchored record) : Anchored C.cost s.realize := by
  obtain ⟨rank, hrank⟩ := hs
  refine ⟨rank, ?_⟩
  intro i
  rcases hrank i with hw | ⟨j, hj, heq⟩
  · left
    change recordPosition _ (s.endpoint (s.matching i)) = 1
    rw [hw, recordPosition_last _ (hlength _)]
  · exact Or.inr ⟨j, hj, hequal i _ _ _ _ heq⟩

/-- Formal EF immediately implies physical EF on the unperturbed primary
costs, including arbitrary plateaus and coincident physical endpoints. -/
lemma RecordState.primary_envyFree {n : ℕ} {length : Fin n → ℕ}
    (record : Fin n → (p : Fin n) → Fin (length p + 1) → ℝ × ℚ)
    (s : RecordState length) (hs : s.FormalEF record) : ∀ i p,
    (record i (s.matching i) (s.endpoint (s.matching i))).1 ≤ (record i p (s.endpoint p)).1 :=
  fun i p => recordLE_primary_le (hs i p)

end Core
end EnvyFreeResearch.Full.Chores
