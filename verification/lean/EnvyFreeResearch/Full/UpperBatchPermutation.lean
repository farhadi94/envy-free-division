import EnvyFreeResearch.Full.UpperPreparedIsolation

/-!
# Independent random batch permutation

Uniformly relabeling arbitrary batches makes their labeled law exchangeable;
the batches need not have identical laws. The assignment-isolation estimates
are also averaged over the actual independent permutation/threshold product.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperBatchPermutation

open UpperAssignment UpperSeedMatrix UpperRepairJobs UpperChoreIsolation
  UpperAssignmentIsolation UpperThresholdProduct

theorem uniform_equiv_preserves {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (e : α ≃ α) :
    MeasurePreserving e (uniformOn Set.univ) (uniformOn Set.univ) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_of_countable _) hs, uniformOn_univ, uniformOn_univ]
  have heq : e ⁻¹' s = e.symm '' s := by
    ext t
    constructor
    · intro h
      exact ⟨e t, h, e.symm_apply_apply t⟩
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
  rw [heq, Measure.count_injective_image e.symm.injective]

variable {Agent : Type*} [Fintype Agent]

def permutationLaw (Agent : Type*) [Fintype Agent] : Measure (Equiv.Perm Agent) :=
  uniformOn Set.univ

instance permutationLaw_probability : IsProbabilityMeasure (permutationLaw Agent) := by
  unfold permutationLaw
  infer_instance

def composeRight (tau : Equiv.Perm Agent) : Equiv.Perm (Equiv.Perm Agent) where
  toFun pi := tau.trans pi
  invFun pi := tau.symm.trans pi
  left_inv pi := by ext j; simp
  right_inv pi := by ext j; simp

def labeled {Tape Piece : Type*} (batches : Tape → Agent → Piece)
    (draw : Tape × Equiv.Perm Agent) (label : Agent) : Piece :=
  batches draw.1 (draw.2 label)

theorem labeled_measurable {Tape Piece : Type*} [MeasurableSpace Tape] [MeasurableSpace Piece]
    (batches : Tape → Agent → Piece) (hbatches : ∀ j, Measurable (fun tape => batches tape j)) :
    Measurable (labeled batches) := by
  apply Measurable.of_eval
  intro j
  exact measurable_from_prod_countable_left (fun pi => hbatches (pi j))

/-- Independent uniform permutation makes the labeled batches exchangeable
for every underlying batch family and every preceding-history law. -/
theorem labeled_law_exchangeable {Tape Piece : Type*} [MeasurableSpace Tape] [MeasurableSpace Piece]
    (μ : Measure Tape) [SFinite μ] (batches : Tape → Agent → Piece)
    (hbatches : ∀ j, Measurable (fun tape => batches tape j)) (tau : Equiv.Perm Agent) :
    (μ.prod (permutationLaw Agent)).map (fun draw j => labeled batches draw (tau j)) =
      (μ.prod (permutationLaw Agent)).map (labeled batches) := by
  let changeTape : Tape × Equiv.Perm Agent → Tape × Equiv.Perm Agent :=
    Prod.map id (composeRight tau)
  have hchange : MeasurePreserving changeTape (μ.prod (permutationLaw Agent))
      (μ.prod (permutationLaw Agent)) :=
    (MeasurePreserving.id μ).prod (uniform_equiv_preserves (composeRight tau))
  have heq : (fun draw j => labeled batches draw (tau j)) = (labeled batches) ∘ changeTape := by
    funext draw j
    rfl
  rw [heq, ← Measure.map_map (labeled_measurable batches hbatches) hchange.measurable,
    hchange.map_eq]

def permutedWeights {k L : ℕ} (weights : Job k → Fin L → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (job : Job k) : Fin L → Fin k → ℝ :=
  weights (job.1, pi job.2)

/-- Direct Tonelli averaging on a finite product; the same bound holds for
every permutation before averaging, so no assignment-dependent event is
conditioned on. -/
theorem finite_product_event_le {X Y : Type*} [Finite X] [Finite Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (bad : X → Y → Prop) (bound : ℝ≥0∞) (hfiber : ∀ x, ν {y | bad x y} ≤ bound) :
    (μ.prod ν) {p | bad p.1 p.2} ≤ bound := by
  rw [Measure.prod_apply (Set.to_countable _).measurableSet]
  calc
    _ ≤ ∫⁻ _x, bound ∂μ := lintegral_mono hfiber
    _ = bound := by simp

/-- Both exact isolation bounds hold after the independent uniform batch
permutation, for arbitrary (possibly different) witness families per batch. -/
theorem random_batches_isolation {k L : ℕ} (hk : 2 ≤ k)
    (weights : Job k → Fin L → Fin k → ℝ) (old A : Fin k → Fin k → ℝ)
    (hA : ∀ i h, 0 ≤ A i h) (hsym : ∀ i h, A i h = A h i)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : ∀ job : Job k, ∀ r,
      A job.1.1.1 job.1.1.2 / 3 ≤ |weights job r job.1.1.1 - weights job r job.1.1.2|) :
    let law := (permutationLaw (Fin k)).prod (tapeLaw (jobCount k - 1 + 1) L)
    let table := fun draw => UpperSeedMatrix.matrix (system hk (permutedWeights weights draw.1)) old draw.2
    let bound := ENNReal.ofReal ((k : ℝ)^2 * (k - 1 : ℝ) *
      (12 * lam * Real.log (2 * k) + 1) / (L + 1 : ℕ))
    law {draw | ∃ transfer : Equiv.Perm (Fin k), 0 < margin (table draw) A lam transfer} ≤ bound ∧
    law {draw | ∃ transfer : Equiv.Perm (Fin k),
      0 < margin (fun i j => -table draw i j) A lam transfer} ≤ bound := by
  dsimp only
  constructor
  · apply finite_product_event_le (permutationLaw (Fin k)) (tapeLaw (jobCount k - 1 + 1) L)
      (fun pi draw => ∃ transfer : Equiv.Perm (Fin k),
        0 < margin (UpperSeedMatrix.matrix (system hk (permutedWeights weights pi)) old draw) A lam transfer) _
    intro pi
    exact isolation_probability hk (permutedWeights weights pi) old A hA hsym lam hlam
      (fun job r => hgap (job.1, pi job.2) r)
  · apply finite_product_event_le (permutationLaw (Fin k)) (tapeLaw (jobCount k - 1 + 1) L)
      (fun pi draw => ∃ transfer : Equiv.Perm (Fin k),
        0 < margin (fun i j => -UpperSeedMatrix.matrix (system hk (permutedWeights weights pi)) old draw i j) A lam transfer) _
    intro pi
    exact chore_isolation_probability hk (permutedWeights weights pi) old A hA hsym lam hlam
      (fun job r => hgap (job.1, pi job.2) r)

end EnvyFreeResearch.Full.UpperBatchPermutation
