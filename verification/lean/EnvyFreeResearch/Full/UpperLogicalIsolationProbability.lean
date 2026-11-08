import EnvyFreeResearch.Full.UpperLogicalIsolationPure

/-! Original preparation law times fresh permutation/threshold law. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperRepairJobs UpperBatchPermutation UpperThresholdProduct UpperIdealPayments UpperAssignmentIsolation
  UpperLogicalPreparation UpperLogicalPreparationGuard UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable Chores
variable {k L n : ℕ}

abbrev IsolationDraw (k L : ℕ) := Equiv.Perm (Fin k) × (Fin (jobCount k - 1 + 1) → Fin (L + 1))
def isolationLaw (k L : ℕ) : Measure (IsolationDraw k L) :=
  (permutationLaw (Fin k)).prod (tapeLaw (jobCount k - 1 + 1) L)
instance isolationLaw_probability : IsProbabilityMeasure (isolationLaw k L) := by
  unfold isolationLaw
  infer_instance

def isolationBound (k L : ℕ) (lam : ℝ) : ℝ :=
  (k : ℝ)^2 * (k - 1 : ℝ) * (12 * lam * Real.log (2 * k) + 1) / (L + 1 : ℕ)

def signedTable (chores : Bool) (V : Fin k → Fin k → ℝ) : Fin k → Fin k → ℝ :=
  if chores then fun i j => -V i j else V

def cycleReject (chores : Bool) (V A : Fin k → Fin k → ℝ) (lam : ℝ) : Bool :=
  decide (findPositive (signedTable chores V) A lam ≠ none)

theorem cycleReject_iff (chores : Bool) (V A : Fin k → Fin k → ℝ) (lam : ℝ) :
    cycleReject chores V A lam = true ↔ ∃ pi, 0 < margin (signedTable chores V) A lam pi := by
  simp only [cycleReject, decide_eq_true_eq, findPositive_failure]

theorem core_cycle_probability (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ)
    (old A : Fin k → Fin k → ℝ) (hA : ∀ i j, 0 ≤ A i j) (hsym : ∀ i j, A i j = A j i)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : ∀ j a, A j.1.1.1 j.1.1.2 / 3 ≤ |w j a j.1.1.1 - w j a j.1.1.2|) (chores : Bool) :
    isolationLaw k L {t | cycleReject chores (coreMatrix hk w old t.1 t.2) A lam = true} ≤
      ENNReal.ofReal (isolationBound k L lam) := by
  have h := random_batches_isolation hk w old A hA hsym lam hlam hgap
  simp_rw [cycleReject_iff]
  cases chores
  · exact h.1
  · exact h.2

variable {X : Type*} [MeasurableSpace X]

theorem cycleReject_measurable (chores : Bool) (V A : X → Fin k → Fin k → ℝ) (lam : ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (hA : ∀ i j, Measurable (fun x => A x i j)) :
    Measurable (fun x => cycleReject chores (V x) (A x) lam) := by
  have hsign : ∀ i j, Measurable (fun x => signedTable chores (V x) i j) := by
    intro i j
    cases chores
    · exact hV i j
    · exact (hV i j).neg
  apply UpperDomainDifference.decide_measurable
  simp_rw [findPositive_failure, ofPred_exists]
  apply MeasurableSet.iUnion
  intro pi
  apply measurableSet_lt measurable_const
  exact Finset.measurable_sum _ (fun i _ =>
    UpperIdealMeasurable.edge_measurable (fun x => signedTable chores (V x)) A (fun _ => lam) hsign hA measurable_const i (pi i))

/-- Direct averaging on the original full preparation parameter. Rejected
preparation contributes zero; no conditioning changes its sample law. -/
theorem family_cycle_probability (hk : 2 ≤ k) (P : Measure X) [IsProbabilityMeasure P]
    (approved : X → Bool) (happroved : Measurable approved)
    (w : X → Job k → Fin L → Fin k → ℝ) (old A : X → Fin k → Fin k → ℝ)
    (hw : ∀ j a i, Measurable (fun x => w x j a i)) (hold : ∀ i j, Measurable (fun x => old x i j))
    (hAmeas : ∀ i j, Measurable (fun x => A x i j))
    (hA : ∀ x, approved x = true → ∀ i j, 0 ≤ A x i j)
    (hsym : ∀ x, approved x = true → ∀ i j, A x i j = A x j i)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : ∀ x, approved x = true → ∀ j a,
      A x j.1.1.1 j.1.1.2 / 3 ≤ |w x j a j.1.1.1 - w x j a j.1.1.2|) (chores : Bool) :
    (P.prod (isolationLaw k L)) {p | approved p.1 = true ∧
      cycleReject chores (coreMatrix hk (w p.1) (old p.1) p.2.1 p.2.2) (A p.1) lam = true} ≤
      ENNReal.ofReal (isolationBound k L lam) := by
  have hV := coreMatrix_measurable hk (fun p : X × IsolationDraw k L => w p.1)
    (fun p => old p.1) (fun p => p.2.1) (fun p => p.2.2)
    (fun j a i => (hw j a i).comp measurable_fst) (fun i j => (hold i j).comp measurable_fst)
    (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  have hreject := cycleReject_measurable chores _ (fun p : X × IsolationDraw k L => A p.1) lam hV
    (fun i j => (hAmeas i j).comp measurable_fst)
  have hm : MeasurableSet {p : X × IsolationDraw k L | approved p.1 = true ∧
      cycleReject chores (coreMatrix hk (w p.1) (old p.1) p.2.1 p.2.2) (A p.1) lam = true} :=
    (measurableSet_eq_fun (happroved.comp measurable_fst) measurable_const).inter
      (measurableSet_eq_fun hreject measurable_const)
  rw [Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (isolationBound k L lam) ∂P := by
      apply lintegral_mono
      intro x
      change isolationLaw k L {t | approved x = true ∧
        cycleReject chores (coreMatrix hk (w x) (old x) t.1 t.2) (A x) lam = true} ≤ _
      by_cases hx : approved x = true
      · simpa only [hx, true_and] using core_cycle_probability hk (w x) (old x) (A x)
          (hA x hx) (hsym x hx) lam hlam (hgap x hx) chores
      · have he : {t : IsolationDraw k L | approved x = true ∧
            cycleReject chores (coreMatrix hk (w x) (old x) t.1 t.2) (A x) lam = true} = ∅ := by
          ext t
          constructor
          · intro ht
            exact hx ht.1
          · intro ht
            exact False.elim ht
        rw [he, measure_empty]
        exact (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (isolationBound k L lam))
    _ = _ := by simp

/-- The gap hypothesis of the product theorem is proved for the actual
recorded preparation and its actual passing guard. -/
theorem actual_cycle_probability [Nonempty (Fin k)]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (cap : ℝ) (labels : Parent k q → I)
    (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true)
    (old : Fin k → State n) (lam : ℝ) (hlam : 0 ≤ lam) (chores : Bool) :
    isolationLaw k L {t | cycleReject chores
      (coreMatrix hk (weights policy active origin q m L draw theta labels)
        (oldMatrix active old (reserveState policy active origin q m draw theta labels)) t.1 t.2)
      (disagreement policy active origin q m draw theta labels) lam = true} ≤
        ENNReal.ofReal (isolationBound k L lam) :=
  core_cycle_probability hk _ _ _ (UpperPayments.cellGap_nonneg _)
    (UpperPayments.cellGap_symmetric _) lam hlam
    (weights_gap μ policy hpolicy active origin hgood hpositive q m L draw hbudget theta cap labels hpass) chores

end EnvyFreeResearch.Full.UpperLogicalIsolation
