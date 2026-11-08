import EnvyFreeResearch.Full.UpperPayments
import EnvyFreeResearch.Full.UpperCorrectionSupply

/-!
# Concrete correction jobs in original oracle units

The normalized whole-payment algorithm is used only as finite arithmetic on
cached rows. Actual correction jobs multiply its values by recorded reserve
masses; the response policy always sees the original measure profile.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperRawPayments

open UpperPayments UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply
  UpperWholePaymentsPhysical

variable {n k : ℕ} {Cell : Type*} [Fintype Cell]

/-- Literal whole payments from the actual floating/rounding selector. -/
def pending (cells : Cell → Set ℝ) (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta : ℝ) : Fin k → Set ℝ :=
  piece cells (allocation a t eta)

theorem pending_mass (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (active : Fin k → Fin n) (cells : Cell → Set ℝ) (hmeas : ∀ e, MeasurableSet (cells e))
    (hdis : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (scale : Fin n → ℝ) (a : Fin k → Cell → ℝ)
    (hcache : ∀ i e, a i e * scale (active i) = (μ (active i)).real (cells e))
    (t : Fin k → ℝ) (eta : ℝ) (i j : Fin k) :
    (μ (active i)).real (pending cells a t eta j) = value a t eta i j * scale (active i) := by
  rw [pending, piece_mass (μ (active i)) cells hmeas hdis]
  simp_rw [← hcache]
  exact (Finset.sum_mul _ _ _).symm

omit [Fintype Cell] in
theorem normalized_cache (μ : Fin n → Measure ℝ) (active : Fin k → Fin n)
    (reserve : Set ℝ) (cells : Cell → Set ℝ) (a : Fin k → Cell → ℝ)
    (hpositive : ∀ i, 0 < (μ (active i)).real reserve)
    (hcache : ∀ i e, a i e = (μ (active i)).real (cells e) / (μ (active i)).real reserve) :
    ∀ i e, a i e * (μ (active i)).real reserve = (μ (active i)).real (cells e) := by
  intro i e
  rw [hcache, div_mul_cancel₀ _ (hpositive i).ne']

theorem value_upper (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hnormal : ∀ i, ∑ e, a i e = 1) (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1)
    (hsize : (k : ℝ)^2 ≤ lam) (i j : Fin k) :
    value a t eta i j ≤ t j + lam * cellGap a i j := by
  have h := allocation_spec a t eta heta ha hsmall hnormal ht hsum
  have howner : value a t eta j j ≤ t j := by
    have hd := (h.2.1 j).1
    unfold deficit at hd
    linarith
  have hgap := (le_abs_self _).trans (h.2.2.2 i j)
  have hm := mul_le_mul_of_nonneg_right hsize (cellGap_nonneg a i j)
  simp only [Fintype.card_fin] at hgap
  linarith

variable [Nonempty (Fin k)]

def activeSet (active : Fin k → Fin n) : Finset (Fin n) := Finset.univ.image active

def jobs (active : Fin k → Fin n) (scale : Fin n → ℝ)
    (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (j : Fin k) : Job n where
  owner := active j
  deficit := deficit a t eta j * scale (active j)
  previous i := value a t eta (Function.invFun active i) j * scale i
  desired i := t j * scale i
  tolerance i := lam * cellGap a (Function.invFun active i) j * scale i
  checked i := decide (i ∈ activeSet active)

theorem jobs_owner (active : Fin k → Fin n) (scale : Fin n → ℝ)
    (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (j : Fin k) :
    (jobs active scale a t eta lam j).owner ∈ activeSet active :=
  Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

theorem jobs_checked (active : Fin k → Fin n) (scale : Fin n → ℝ)
    (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (j : Fin k)
    (i : Fin n) (hi : i ∈ activeSet active) :
    (jobs active scale a t eta lam j).checked i = true := by
  simpa only [jobs, decide_eq_true_eq] using hi

theorem jobs_previous (active : Fin k → Fin n) (hinj : Function.Injective active) (scale : Fin n → ℝ)
    (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (i j : Fin k) :
    (jobs active scale a t eta lam j).previous (active i) = value a t eta i j * scale (active i) := by
  simp only [jobs, Function.leftInverse_invFun hinj i]

theorem jobs_budget_nonneg (active : Fin k → Fin n) (scale : Fin n → ℝ)
    (hscale : ∀ i, 0 ≤ scale i) (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hnormal : ∀ i, ∑ e, a i e = 1) (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1)
    (hsize : (k : ℝ)^2 ≤ lam) (j : Fin k) (i : Fin n) :
    0 ≤ budget (jobs active scale a t eta lam j) i := by
  have h := value_upper a t eta lam heta ha hsmall hnormal ht hsum hsize (Function.invFun active i) j
  have hm := mul_nonneg (sub_nonneg.mpr h) (hscale i)
  simpa only [budget, jobs, add_mul, sub_mul] using hm

/-- The two separate normalized budgets yield the strict raw cap required by
actual-loop supply. -/
theorem jobs_cap_sum (active : Fin k → Fin n) (scale : Fin n → ℝ)
    (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (ha : ∀ i e, 0 ≤ a i e)
    (hsmall : ∀ i e, a i e ≤ eta) (htarget : (∑ j, t j) < 1 / 16)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16) (i : Fin n) (hi : 0 < scale i) :
    (∑ j, ((jobs active scale a t eta lam j).desired i +
      (jobs active scale a t eta lam j).tolerance i)) < scale i / 8 := by
  have hb : (∑ j : Fin k, (t j + lam * cellGap a (Function.invFun active i) j)) < 1 / 8 := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      add_le_add_left (mul_le_mul_of_nonneg_left
        (cellGap_le a eta heta ha hsmall (Function.invFun active i) j) hlam) (t j))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    rw [Finset.sum_add_distrib]
    nlinarith
  have hm := mul_lt_mul_of_pos_right hb hi
  have heq : (∑ j, ((jobs active scale a t eta lam j).desired i +
      (jobs active scale a t eta lam j).tolerance i)) =
        (∑ j : Fin k, (t j + lam * cellGap a (Function.invFun active i) j)) * scale i := by
    simp only [jobs, Finset.sum_mul, add_mul]
  rw [heq]
  linarith

theorem jobs_deficit_bounds (active : Fin k → Fin n) (scale : Fin n → ℝ)
    (hscale : ∀ i, 0 ≤ scale i) (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hnormal : ∀ i, ∑ e, a i e = 1) (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1) (j : Fin k) :
    0 ≤ (jobs active scale a t eta lam j).deficit ∧
      (jobs active scale a t eta lam j).deficit ≤ t j * scale (active j) ∧
      (jobs active scale a t eta lam j).deficit ≤ eta * scale (active j) := by
  have h := (allocation_spec a t eta heta ha hsmall hnormal ht hsum).2.1 j
  exact ⟨mul_nonneg h.1 (hscale _),
    mul_le_mul_of_nonneg_right (h.2.trans (min_le_left _ _)) (hscale _),
    mul_le_mul_of_nonneg_right (h.2.trans (min_le_right _ _)) (hscale _)⟩

section Physical

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]

theorem jobs_previous_physical (active : Fin k → Fin n) (hinj : Function.Injective active)
    (cells : Cell → Set ℝ) (hmeas : ∀ e, MeasurableSet (cells e))
    (hdis : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (scale : Fin n → ℝ) (a : Fin k → Cell → ℝ)
    (hcache : ∀ i e, a i e * scale (active i) = (μ (active i)).real (cells e))
    (t : Fin k → ℝ) (eta lam : ℝ) (j : Fin k) (i : Fin n) (hi : i ∈ activeSet active) :
    (jobs active scale a t eta lam j).previous i = (μ i).real (pending cells a t eta j) := by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  rw [jobs_previous active hinj]
  exact (pending_mass μ active cells hmeas hdis scale a hcache t eta r j).symm

theorem jobs_owner_deficit (active : Fin k → Fin n)
    (cells : Cell → Set ℝ) (hmeas : ∀ e, MeasurableSet (cells e))
    (hdis : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (scale : Fin n → ℝ) (a : Fin k → Cell → ℝ)
    (hcache : ∀ i e, a i e * scale (active i) = (μ (active i)).real (cells e))
    (t : Fin k → ℝ) (eta lam : ℝ) (j : Fin k) :
    (jobs active scale a t eta lam j).deficit = t j * scale (active j) -
      (μ (active j)).real (pending cells a t eta j) := by
  rw [pending_mass μ active cells hmeas hdis scale a hcache]
  simp only [jobs, deficit, sub_mul]

end Physical

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem jobs_measurable (active : Fin k → Fin n) (scale : X → Fin n → ℝ)
    (a : X → Fin k → Cell → ℝ) (t : X → Fin k → ℝ) (eta lam : X → ℝ)
    (hscale : ∀ i, Measurable (fun z => scale z i))
    (ha : ∀ i e, Measurable (fun z => a z i e)) (ht : ∀ j, Measurable (fun z => t z j))
    (heta : Measurable eta) (hlam : Measurable lam) (j : Fin k) :
    Measurable (fun z => jobs active (scale z) (a z) (t z) (eta z) (lam z) j) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z => (active j,
    deficit (a z) (t z) (eta z) j * scale z (active j),
    (fun i => value (a z) (t z) (eta z) (Function.invFun active i) j * scale z i),
    (fun i => t z j * scale z i),
    (fun i => lam z * cellGap (a z) (Function.invFun active i) j * scale z i),
    (fun i : Fin n => decide (i ∈ activeSet active))))
  exact measurable_const.prodMk
    (((deficit_measurable a t eta ha ht heta j).mul (hscale _)).prodMk
      ((Measurable.of_eval (fun i => (value_measurable a t eta ha ht heta _ j).mul (hscale i))).prodMk
        ((Measurable.of_eval (fun i => (ht j).mul (hscale i))).prodMk
          ((Measurable.of_eval (fun i => (hlam.mul (cellGap_measurable a ha _ j)).mul (hscale i))).prodMk
            measurable_const))))

/-- Scale values are read from the actual reserve history. -/
def recordedJobs (active : Fin k → Fin n) (reserve : State n)
    (a : Fin k → Cell → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) : Fin k → Job n :=
  jobs active (total reserve) a t eta lam

theorem recordedJobs_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (a : X → Fin k → Cell → ℝ) (t : X → Fin k → ℝ) (eta lam : X → ℝ)
    (hreserve : Measurable reserve) (ha : ∀ i e, Measurable (fun z => a z i e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (hlam : Measurable lam) :
    Measurable (fun z => recordedJobs active (reserve z) (a z) (t z) (eta z) (lam z)) :=
  Measurable.of_eval (fun j => jobs_measurable active _ a t eta lam
    (fun i => total_measurable reserve (fun _ => i) hreserve measurable_const) ha ht heta hlam j)

end Measurability

end EnvyFreeResearch.Full.UpperRawPayments
