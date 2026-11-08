import EnvyFreeResearch.Full.ChoresOuterResidueAssembly

/-! Numerical bounds for the literal full residue. Every original private
slot is counted once; there is no sum over historical reset operations. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open scoped Classical BigOperators

variable {n : ℕ} {RootId : Type*} [Fintype RootId]

theorem full_residue_bounds (μ : Measure ℝ) [IsFiniteMeasure μ]
    (R0 : Set ℝ) (cache : RootId → Fin n → List (Parent n)) (J : ℕ) (H : ℝ)
    (hH : 0 < H) (hcard : Fintype.card RootId ≤ J)
    (hsmall : ∀ root p, μ.real (material (cache root p)) ≤ (n : ℝ)*μ.real R0/H) :
    μ.real R0 ≤ μ.real (R0 ∪ Outer.privateUnion cache) ∧
    μ.real (R0 ∪ Outer.privateUnion cache) ≤ (1+(J : ℝ)*(n : ℝ)^2/H)*μ.real R0 := by
  refine ⟨measureReal_mono subset_union_left,?_⟩
  have hn : 0 ≤ (n : ℝ)*μ.real R0/H :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) hH.le
  have hroot (root : RootId) : μ.real (⋃ p, material (cache root p)) ≤
      (n : ℝ)*((n : ℝ)*μ.real R0/H) := by
    calc
      _ ≤ ∑ p : Fin n, μ.real (material (cache root p)) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : Fin n, (n : ℝ)*μ.real R0/H := Finset.sum_le_sum (fun p _ => hsmall root p)
      _ = _ := by simp
  have hunion : μ.real (Outer.privateUnion cache) ≤
      (J : ℝ)*((n : ℝ)*((n : ℝ)*μ.real R0/H)) := by
    calc
      _ ≤ ∑ root : RootId, μ.real (⋃ p, material (cache root p)) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _root : RootId, (n : ℝ)*((n : ℝ)*μ.real R0/H) := Finset.sum_le_sum (fun root _ => hroot root)
      _ = (Fintype.card RootId : ℝ)*((n : ℝ)*((n : ℝ)*μ.real R0/H)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg (Nat.cast_nonneg _) hn)
  calc
    _ ≤ μ.real R0+μ.real (Outer.privateUnion cache) := measureReal_union_le _ _
    _ ≤ μ.real R0+(J : ℝ)*((n : ℝ)*((n : ℝ)*μ.real R0/H)) := add_le_add le_rfl hunion
    _ = _ := by ring

theorem exhausted_scalar_domination (n J : ℕ) (H r u : ℝ)
    (hr : 0 ≤ r) (hscale : (n : ℝ)+2 ≤ H) (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
    (hu : u ≤ (1+(J : ℝ)*(n : ℝ)^2/H)*r) : u ≤ (H-(n : ℝ)/H)*r := by
  have hH : 0 < H := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hHone : 1 ≤ H := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hdiv : (n : ℝ)/H ≤ n := (div_le_iff₀ hH).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hj : (J : ℝ)*(n : ℝ)^2/H ≤ 1 := (div_le_iff₀ hH).mpr (by simpa using hreserve)
  have hfactor : 1+(J : ℝ)*(n : ℝ)^2/H ≤ H-(n : ℝ)/H := by linarith
  exact hu.trans (mul_le_mul_of_nonneg_right hfactor hr)

end EnvyFreeResearch.Full.Chores.Terminal
