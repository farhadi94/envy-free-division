import EnvyFreeResearch.Full.ChoresIntervalCore

/-!
# Quantitative cutter progress of the actual interval Core

The whole-parent certificate and the cutter's proved EF comparisons imply
both manuscript inequalities. The residue value is the sum of the actual
physical complementary suffix values, not a formal perturbation.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.IntervalCore

open Set IntervalOracle PhysicalCore InitialPartition
open scoped BigOperators

def residueValue {n : ℕ} (P : Profile (Fin n)) (parent : Fin n → Parent n)
    (s : PhysicalCore.State n n) (i : Fin n) : ℝ :=
  ∑ p, (P.cumulative i (parent p).right - P.cumulative i (s.endpoint p).point)

lemma sum_complements_bound {n : ℕ} (v : Fin n → ℝ) (a b : ℝ) (p : Fin n)
    (hp : v p = a) (hb : ∀ q, b ≤ v q) :
    (∑ q, (a - v q)) ≤ (n - 1 : ℕ) * (a - b) := by
  classical
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun q => a - v q) (Finset.mem_univ p)
  rw [hp, sub_self, add_zero] at hsum
  rw [← hsum]
  calc
    ∑ q ∈ Finset.univ.erase p, (a - v q) ≤ ∑ _q ∈ Finset.univ.erase p, (a - b) :=
      Finset.sum_le_sum (fun q _ => sub_le_sub_left (hb q) a)
    _ = (n - 1 : ℕ) * (a - b) := by simp; ring

theorem cutter_progress {n : ℕ} (hn : 2 ≤ n) (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i)) (c : Fin n) (a b : ℝ)
    (parent : Fin n → Parent n) (s : PhysicalCore.State n n)
    (hcorrect : Correct P c a b (.prefixes parent s)) :
    0 ≤ residueValue P parent s c ∧
    residueValue P parent s c ≤ ((n - 1 : ℕ) : ℝ) / n * (P.cumulative c b - P.cumulative c a) ∧
    ∃ j, (s.endpoint (s.matching j)).point = (parent (s.matching j)).right ∧
      residueValue P parent s c / (n - 1 : ℕ) ≤
        prefixValue P (parentFrame parent) s c (s.matching j) -
        prefixValue P (parentFrame parent) s c (s.matching c) := by
  obtain ⟨_, hvalue, hequal, _, _, hpoints, hEF, j, hj⟩ := hcorrect
  let share := (P.cumulative c b - P.cumulative c a) / n
  let v := prefixValue P (parentFrame parent) s c
  have heq : ∀ p, P.cumulative c (parent p).right - P.cumulative c (parent p).left = share :=
    fun p => (hvalue c p).symm.trans (hequal p)
  have hv : ∀ p, 0 ≤ v p := by
    intro p
    exact sub_nonneg.mpr (hmono c (hpoints p).1)
  have hw : v (s.matching j) = share := by
    change P.cumulative c (s.endpoint (s.matching j)).point - P.cumulative c (parent (s.matching j)).left = share
    rw [hj]
    exact heq _
  have hres : residueValue P parent s c = ∑ p, (share - v p) := by
    apply Finset.sum_congr rfl
    intro p _
    change P.cumulative c (parent p).right - P.cumulative c (s.endpoint p).point =
      share - (P.cumulative c (s.endpoint p).point - P.cumulative c (parent p).left)
    linarith only [heq p]
  have hbound := sum_complements_bound v share (v (s.matching c)) (s.matching j) hw (hEF c)
  rw [← hres] at hbound
  have hden : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 0 < n - 1 by omega)
  refine ⟨?_, ?_, j, hj, ?_⟩
  · exact Finset.sum_nonneg (fun p _ => sub_nonneg.mpr (hmono c (hpoints p).2))
  · calc
      residueValue P parent s c ≤ (n - 1 : ℕ) * (share - v (s.matching c)) := hbound
      _ ≤ (n - 1 : ℕ) * share := mul_le_mul_of_nonneg_left (sub_le_self _ (hv _)) (le_of_lt hden)
      _ = ((n - 1 : ℕ) : ℝ) / n * (P.cumulative c b - P.cumulative c a) := by dsimp only [share]; ring
  · apply (div_le_iff₀ hden).mpr
    change residueValue P parent s c ≤ (v (s.matching j) - v (s.matching c)) * (n - 1 : ℕ)
    rw [hw, mul_comm]
    exact hbound

end EnvyFreeResearch.Full.Chores.IntervalCore
