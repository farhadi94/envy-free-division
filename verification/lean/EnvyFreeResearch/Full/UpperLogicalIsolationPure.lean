import EnvyFreeResearch.Full.UpperLogicalIsolationData
import EnvyFreeResearch.Full.UpperLogicalIsolationCore
import EnvyFreeResearch.Full.UpperGridData
import EnvyFreeResearch.Full.UpperIdealMeasurable

/-! Pure post-query isolation data, jointly Borel on the returned grid and history. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperLogicalPreparation UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairJobs UpperSeedMatrix UpperBatchPermutation UpperRepresentatives UpperIdealPayments
variable {n k L coarse fine : ℕ}

def dataPairs (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) : List (Fin (coarse + fine + 1) × Fin (coarse + fine + 1)) :=
  match UpperGridData.representatives active origin data (requests k L) with
  | none => []
  | some result => result.1

def dataWeights (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I) : Job k → Fin L → Fin k → ℝ :=
  coreWeights (UpperGridData.table active origin data)
    (multipliers active origin (UpperGridData.reserve data theta labels)) (dataPairs active origin data L) 0

def dataDisagreement (active : Fin k → Fin n) (data : UpperGridData.Data n coarse fine)
    (theta : I) (labels : Fin (coarse + 1) → I) : Fin k → Fin k → ℝ :=
  UpperPayments.cellGap (UpperCorrectionSetup.table active (UpperGridData.reserve data theta labels) (UpperGridData.cuts data))

def coreMatrix (hk : 2 ≤ k) (w : Job k → Fin L → Fin k → ℝ) (old : Fin k → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) : Fin k → Fin k → ℝ :=
  matrix (system hk (permutedWeights w pi)) old threshold

def dataMatrix (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) : Fin k → Fin k → ℝ :=
  coreMatrix hk (dataWeights active origin data L theta labels)
    (oldMatrix active old (UpperGridData.reserve data theta labels)) pi threshold

theorem dataPairs_execute [Nonempty (Fin k)] (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) :
    dataPairs active origin (UpperGridMerge.prepare policy active origin q m draw) L =
      representativePairs policy active origin q m L draw := by
  unfold dataPairs representativePairs
  rw [UpperGridData.representatives_execute]
  cases representativeRun policy active origin q m draw (requests k L) <;> rfl

theorem dataWeights_execute [Nonempty (Fin k)] (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I) :
    dataWeights active origin (UpperGridMerge.prepare policy active origin q m draw) L theta labels =
      weights policy active origin q m L draw theta labels := by
  unfold dataWeights coreWeights coreChosen weights chosenCell
  simp only [UpperGridData.table_execute, UpperGridData.reserve_execute]
  rw [dataPairs_execute]

theorem dataDisagreement_execute (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I) :
    dataDisagreement active (UpperGridMerge.prepare policy active origin q m draw) theta labels =
      disagreement policy active origin q m draw theta labels := rfl

variable {X : Type*} [MeasurableSpace X]

theorem coreChosen_measurable {Cell : Type*} [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (values : X → Fin k → Cell → ℝ) (normalizer : X → Fin k → ℝ) (pairs : X → List (Cell × Cell))
    (fallback : Cell) (hvalues : ∀ i e, Measurable (fun x => values x i e))
    (hnormalizer : ∀ i, Measurable (fun x => normalizer x i)) (hpairs : Measurable pairs) (j : Job k) (a : Fin L) :
    Measurable (fun x => coreChosen (values x) (normalizer x) (pairs x) fallback j a) :=
  picked_measurable values normalizer UpperPreparedIsolation.rows pairs fallback hvalues hnormalizer hpairs (j, a)

theorem coreWeights_measurable {Cell : Type*} [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (values : X → Fin k → Cell → ℝ) (normalizer : X → Fin k → ℝ) (pairs : X → List (Cell × Cell))
    (fallback : Cell) (hvalues : ∀ i e, Measurable (fun x => values x i e))
    (hnormalizer : ∀ i, Measurable (fun x => normalizer x i)) (hpairs : Measurable pairs) (j : Job k) (a : Fin L) (i : Fin k) :
    Measurable (fun x => coreWeights (values x) (normalizer x) (pairs x) fallback j a i) :=
  (hnormalizer i).mul ((score_eval_measurable (fun x => values x i) (hvalues i)).comp
    (measurable_id.prodMk (coreChosen_measurable values normalizer pairs fallback hvalues hnormalizer hpairs j a)))

theorem dataPairs_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => dataPairs active (origin x) (data x) L) := by
  have h := ProtocolMeasurable.measurable_option_cases
    (present := fun (_ : X) (result : List (Fin (coarse + fine + 1) × Fin (coarse + fine + 1)) × Finset (Fin (coarse + 1))) => result.1)
    (absent := fun _ => ([] : List (Fin (coarse + fine + 1) × Fin (coarse + fine + 1))))
    (UpperGridData.representatives_measurable active origin data (requests k L) horigin hdata)
    (measurable_fst.comp measurable_snd) measurable_const
  convert h using 1
  funext x
  unfold dataPairs
  cases UpperGridData.representatives active (origin x) (data x) (requests k L) <;> rfl

theorem dataWeights_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : X → Fin (coarse + 1) → I)
    (horigin : Measurable origin) (hdata : Measurable data) (hlabels : ∀ p, Measurable (fun x => labels x p))
    (j : Job k) (a : Fin L) (i : Fin k) :
    Measurable (fun x => dataWeights active (origin x) (data x) L theta (labels x) j a i) := by
  apply coreWeights_measurable
  · exact UpperGridData.table_measurable active origin data horigin hdata
  · intro r
    exact (total_measurable origin _ horigin measurable_const).div
      (total_measurable _ _ (UpperGridData.reserve_measurable data theta labels hdata hlabels) measurable_const)
  · exact dataPairs_measurable active origin data L horigin hdata

theorem coreMatrix_measurable (hk : 2 ≤ k) (w : X → Job k → Fin L → Fin k → ℝ)
    (old : X → Fin k → Fin k → ℝ) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (hw : ∀ j a i, Measurable (fun x => w x j a i)) (hold : ∀ i j, Measurable (fun x => old x i j))
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (i c : Fin k) :
    Measurable (fun x => coreMatrix hk (w x) (old x) (pi x) (threshold x) i c) := by
  have hw' (j : Fin (jobCount k - 1 + 1)) (a : Fin L) (r : Fin k) :
      Measurable (fun x => (system hk (permutedWeights (w x) (pi x))).weight j a r) := by
    exact (score_eval_measurable (fun x (job : Job k) => w x job a r) (fun job => hw job a r)).comp
      (measurable_id.prodMk ((measurable_of_countable (fun p : Equiv.Perm (Fin k) => permuteJob p (jobEquiv hk j))).comp hpi))
  apply (hold i c).add
  apply Finset.measurable_sum
  intro j _
  change Measurable (fun x => if (jobEquiv hk j).2 = c then _ else (0 : ℝ))
  split_ifs
  · apply Finset.measurable_sum
    intro a _
    exact (hw' j a i).ite
      (kept_measurableSet _ _ (fun a => (hw' j a _).sub (hw' j a _)) (hthreshold j) a) measurable_const
  · exact measurable_const

theorem dataDisagreement_measurable (active : Fin k → Fin n)
    (data : X → UpperGridData.Data n coarse fine) (theta : I) (labels : X → Fin (coarse + 1) → I)
    (hdata : Measurable data) (hlabels : ∀ p, Measurable (fun x => labels x p)) (i j : Fin k) :
    Measurable (fun x => dataDisagreement active (data x) theta (labels x) i j) :=
  UpperPayments.cellGap_measurable _ (UpperCorrectionSetup.table_measurable active _ _
    (UpperGridData.reserve_measurable data theta labels hdata hlabels)
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata))) i j

theorem oldMatrix_measurable (active : Fin k → Fin n) (old : X → Fin k → State n) (reserve : X → State n)
    (hold : ∀ j, Measurable (fun x => old x j)) (hreserve : Measurable reserve) (i j : Fin k) :
    Measurable (fun x => oldMatrix active (old x) (reserve x) i j) :=
  (total_measurable _ _ (hold j) measurable_const).div (total_measurable reserve _ hreserve measurable_const)

theorem dataMatrix_measurable (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : X → State n)
    (old : X → Fin k → State n) (data : X → UpperGridData.Data n coarse fine)
    (L : ℕ) (theta : I) (labels : X → Fin (coarse + 1) → I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hdata : Measurable data)
    (hlabels : ∀ p, Measurable (fun x => labels x p)) (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (i c : Fin k) :
    Measurable (fun x => dataMatrix hk active (origin x) (old x) (data x) L theta (labels x) (pi x) (threshold x) i c) :=
  coreMatrix_measurable hk _ _ pi threshold
    (dataWeights_measurable active origin data L theta labels horigin hdata hlabels)
    (oldMatrix_measurable active old _ hold (UpperGridData.reserve_measurable data theta labels hdata hlabels))
    hpi hthreshold i c

end EnvyFreeResearch.Full.UpperLogicalIsolation
