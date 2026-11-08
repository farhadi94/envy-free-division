import EnvyFreeResearch.Full.UpperRepairLegality
import EnvyFreeResearch.Full.UpperRepairSnapshotProbability

/-! Query-free selection and checking of an actual Snapshot margin from the
returned Repair caches. The selection normalizes by the returned residue, so
it needs no hidden reserve metadata from the Repair implementation. -/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperSnapshotRepair

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotContrast UpperDomainDifference

variable {n k : ℕ}

def values (active : Fin k → Fin n) (result : PhysicalResult n k) (i j : Fin k) : ℝ :=
  total (result.1 j) (active i) / total result.2.1 (active i)

def pair (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (result : PhysicalResult n k) : Fin k × Fin k :=
  maximizingPair hk chores (values active result)

def score (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (result : PhysicalResult n k) : ℝ :=
  signedGap chores (values active result) (pair hk chores active result).1 (pair hk chores active result).2

def passes (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ) (result : PhysicalResult n k) : Bool :=
  !result.2.2 && decide (0 < score hk chores active result ∧ gamma ≤ score hk chores active result)

theorem passes_iff (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ) (result : PhysicalResult n k) :
    passes hk chores active gamma result = true ↔ result.2.2 = false ∧
      0 < score hk chores active result ∧ gamma ≤ score hk chores active result := by
  simp only [passes, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq]

section Measurability
variable {X : Type} [MeasurableSpace X]

theorem values_measurable (active : Fin k → Fin n) (result : X → PhysicalResult n k)
    (hresult : Measurable result) (i j : Fin k) : Measurable (fun x => values active (result x) i j) :=
  (total_measurable _ (fun _ => active i)
    ((measurable_pi_apply j).comp (measurable_fst.comp hresult)) measurable_const).div
    (total_measurable _ (fun _ => active i) (measurable_fst.comp (measurable_snd.comp hresult)) measurable_const)

theorem pair_measurable (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (result : X → PhysicalResult n k)
    (hresult : Measurable result) : Measurable (fun x => pair hk chores active (result x)) :=
  maximizingPair_measurable hk chores _ (values_measurable active result hresult)

theorem score_measurable (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (result : X → PhysicalResult n k)
    (hresult : Measurable result) : Measurable (fun x => score hk chores active (result x)) := by
  unfold score
  let Z : X → Fin k → Fin k → ℝ := fun x => values active (result x)
  have hZ : ∀ i j, Measurable (fun x => Z x i j) :=
    values_measurable active result hresult
  have hcoordinate : Measurable (fun z : X × (Fin k × Fin k) =>
      signedGap chores (Z z.1) z.2.1 z.2.2) := by
    apply measurable_from_prod_countable_left
    intro ij
    exact signedGap_measurable chores Z hZ ij.1 ij.2
  have hp : Measurable (fun x => (x, pair hk chores active (result x))) :=
    measurable_id.prodMk (pair_measurable hk chores active result hresult)
  change Measurable ((fun z : X × (Fin k × Fin k) =>
    signedGap chores (Z z.1) z.2.1 z.2.2) ∘ (fun x => (x, pair hk chores active (result x))))
  exact hcoordinate.comp hp

theorem passes_measurable (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (result : X → PhysicalResult n k) (hresult : Measurable result) :
    Measurable (fun x => passes hk chores active gamma (result x)) := by
  have hs := score_measurable hk chores active result hresult
  have hc := decide_measurable (fun x => 0 < score hk chores active (result x) ∧ gamma ≤ score hk chores active (result x))
    ((measurableSet_lt measurable_const hs).inter (measurableSet_le measurable_const hs))
  exact (measurable_of_countable (fun p : Bool × Bool => !p.1 && p.2)).comp
    ((measurable_snd.comp (measurable_snd.comp hresult)).prodMk hc)

end Measurability

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (result : PhysicalResult n k)
  (halloc : ∀ j, WellFormed μ (result.1 j)) (hresidue : WellFormed μ result.2.1)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain result.2.1.cells))

include halloc hresidue in
theorem values_correct :
    values active result = normalizedValues (fun i => μ (active i)) (domain result.2.1.cells)
      (fun j => domain (result.1 j).cells) := by
  funext i j
  rw [values, total_correct μ _ (halloc j), total_correct μ _ hresidue]
  rfl

include halloc hresidue hpositive in
theorem checked_physical (gamma : ℝ) (hpass : passes hk chores active gamma result = true) :
    (pair hk chores active result).1 ≠ (pair hk chores active result).2 ∧
      0 < physicalGap chores (fun i => μ (active i)) (fun j => domain (result.1 j).cells)
        (pair hk chores active result).1 (pair hk chores active result).2 ∧
      gamma * (μ (active (pair hk chores active result).1)).real (domain result.2.1.cells) ≤
        physicalGap chores (fun i => μ (active i)) (fun j => domain (result.1 j).cells)
          (pair hk chores active result).1 (pair hk chores active result).2 := by
  obtain ⟨_, hp, hb⟩ := (passes_iff hk chores active gamma result).mp hpass
  have hraw : physicalGap chores (fun i => μ (active i)) (fun j => domain (result.1 j).cells)
      (pair hk chores active result).1 (pair hk chores active result).2 =
      (μ (active (pair hk chores active result).1)).real (domain result.2.1.cells) * score hk chores active result := by
    rw [raw_gap chores (fun i => μ (active i)) (domain result.2.1.cells)
      (fun j => domain (result.1 j).cells) _ _ (hpositive _).ne', score,
      values_correct μ active result halloc hresidue]
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hz : score hk chores active result = 0 := by rw [score, heq, signedGap_self]
    linarith
  · rw [hraw]
    exact mul_pos (hpositive _) hp
  · rw [hraw]
    nlinarith [mul_le_mul_of_nonneg_left hb (hpositive (pair hk chores active result).1).le]

include halloc hresidue hpositive in
theorem passes_of_witness (gamma : ℝ) (hgamma : 0 < gamma) (hstop : result.2.2 = false)
    (a b : Fin k)
    (hmargin : gamma * (μ (active a)).real (domain result.2.1.cells) ≤
      physicalGap chores (fun i => μ (active i)) (fun j => domain (result.1 j).cells) a b) :
    passes hk chores active gamma result = true := by
  have hcandidate : gamma ≤ signedGap chores (values active result) a b := by
    rw [values_correct μ active result halloc hresidue, normalized_gap]
    exact (le_div_iff₀ (hpositive a)).mpr hmargin
  have hmax := maximizingPair_spec hk chores (values active result) a b
  have hb : gamma ≤ score hk chores active result := hcandidate.trans hmax
  exact (passes_iff hk chores active gamma result).mpr ⟨hstop, hgamma.trans_le hb, hb⟩

end EnvyFreeResearch.Full.UpperSnapshotRepair
