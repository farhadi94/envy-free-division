import EnvyFreeResearch.Full.ChoresInterpolation

/-!
# One hungry measure profile for an entire finite formal-record table

Each parent has finitely many prefix records, including an empty record of
formal value `(0,0)`. All observers see strict lexicographic growth along each
parent. A single positive perturbation produces actual finite atomless Borel
measures with those prefix values and with positive cost on each nondegenerate
abstract interval. Comparisons and equalities across the entire table are
preserved simultaneously. This does not assert that a Core execution succeeds:
replaying the adaptive dynamic program is still a separate obligation.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open Set MeasureTheory

variable {Agent Parent : Type*} [Fintype Agent] [Fintype Parent]

/-- The continuous-measure portion of simultaneous finite realization. -/
theorem simultaneous_measure_realization (length : Parent → ℕ)
    (record : Agent → (p : Parent) → Fin (length p + 1) → ℝ × ℚ)
    (hzero : ∀ i p, record i p 0 = (0, 0))
    (hstrict : ∀ i p (j k : Fin (length p + 1)), j < k →
      recordLT (record i p j) (record i p k)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ μ : Agent → Parent → Measure ℝ,
      (∀ i p, IsFiniteMeasure (μ i p)) ∧
      (∀ i p, NullSingletonClass (μ i p)) ∧
      (∀ i p (k : Fin (length p + 1)),
        (μ i p).real (Icc 0 (k : ℝ)) = realizedCost ε (record i p k)) ∧
      (∀ i p {a b : ℝ}, 0 ≤ a → a < b → b ≤ length p →
        0 < μ i p (Ioc a b)) ∧
      (∀ i p (k : Fin (length p + 1)) j q (l : Fin (length q + 1)),
        (recordLT (record i p k) (record j q l) ↔
          (μ i p).real (Icc 0 (k : ℝ)) < (μ j q).real (Icc 0 (l : ℝ))) ∧
        (record i p k = record j q l ↔
          (μ i p).real (Icc 0 (k : ℝ)) = (μ j q).real (Icc 0 (l : ℝ)))) := by
  let Record := Agent × ((p : Parent) × Fin (length p + 1))
  let value : Record → ℝ × ℚ := fun r => record r.1 r.2.1 r.2.2
  obtain ⟨ε, hε, hcompare⟩ := exists_exact_comparison_realization value
  let values : Agent → Parent → ℕ → ℝ := fun i p k =>
    realizedCost ε (record i p ⟨min k (length p), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
  have hvalues (i : Agent) (p : Parent) (k : ℕ) (hk : k ≤ length p) :
      values i p k = realizedCost ε (record i p ⟨k, Nat.lt_succ_of_le hk⟩) := by
    simp only [values, Nat.min_eq_left hk]
  have hvzero (i : Agent) (p : Parent) : values i p 0 = 0 := by
    rw [hvalues i p 0 (Nat.zero_le _)]
    simpa [realizedCost] using congrArg (realizedCost ε) (hzero i p)
  have hvstrict (i : Agent) (p : Parent) : ∀ k < length p,
      values i p k < values i p (k + 1) := by
    intro k hk
    rw [hvalues i p k hk.le, hvalues i p (k + 1) (Nat.succ_le_of_lt hk)]
    apply (hcompare ⟨i, ⟨p, ⟨k, Nat.lt_succ_of_le hk.le⟩⟩⟩
      ⟨i, ⟨p, ⟨k + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hk)⟩⟩⟩).1.mp
    exact hstrict i p _ _ (by change k < k + 1; omega)
  let μ : Agent → Parent → Measure ℝ := fun i p =>
    (prefixStieltjes (length p) (values i p) (fun k hk => (hvstrict i p k hk).le)).measure
  have hrecord (i : Agent) (p : Parent) (k : Fin (length p + 1)) :
      (μ i p).real (Icc 0 (k : ℝ)) = realizedCost ε (record i p k) := by
    change (prefixStieltjes (length p) (values i p)
      (fun j hj => (hvstrict i p j hj).le)).measure.real (Icc 0 (k.val : ℝ)) = _
    rw [prefixStieltjes_record_value _ _ _ (hvzero i p) k.val (Nat.le_of_lt_succ k.isLt)]
    exact hvalues i p k.val (Nat.le_of_lt_succ k.isLt)
  refine ⟨ε, hε, μ, ?_, ?_, hrecord, ?_, ?_⟩
  · intro i p
    exact prefixStieltjes_finite (length p) (values i p)
      (fun k hk => (hvstrict i p k hk).le) (hvzero i p)
  · intro i p
    exact prefixStieltjes_noAtoms (length p) (values i p)
      (fun k hk => (hvstrict i p k hk).le)
  · intro i p a b ha hab hb
    exact prefixStieltjes_hungry (length p) (values i p) (hvstrict i p)
      ⟨ha, hab.le.trans hb⟩ ⟨ha.trans hab.le, hb⟩ hab
  · intro i p k j q l
    rw [hrecord i p k, hrecord j q l]
    exact hcompare ⟨i, ⟨p, k⟩⟩ ⟨j, ⟨q, l⟩⟩

end EnvyFreeResearch.Full.Chores
