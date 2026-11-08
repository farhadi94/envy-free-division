import EnvyFreeResearch.Full.UpperDomainDifferenceSequence
import EnvyFreeResearch.Full.UpperDomainDifferenceMeasurable
import EnvyFreeResearch.Full.UpperDomainDifferenceFold

/-!
# Measurable sequential remaining domains and exact cache accesses

Correction records use the product Borel encoding of their amount, circle
start, and two real endpoints. Actual finite state folding is measurable on
changing component and correction lists, and accesses to a correct prefix
cache equal measurable physical component masses.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain Chores ProtocolMeasurable

def correctionCode (r : Correction) : I × UpperCircular.Circle × ℝ × ℝ :=
  (r.amount, r.start, r.first, r.last)

instance correctionMeasurableSpace : MeasurableSpace Correction :=
  MeasurableSpace.comap correctionCode inferInstance

theorem correctionCode_measurable : Measurable correctionCode := comap_measurable _

theorem correction_amount_measurable : Measurable Correction.amount :=
  measurable_fst.comp correctionCode_measurable

theorem correction_start_measurable : Measurable Correction.start :=
  measurable_fst.comp (measurable_snd.comp correctionCode_measurable)

theorem correction_first_measurable : Measurable Correction.first :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp correctionCode_measurable))

theorem correction_last_measurable : Measurable Correction.last :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp correctionCode_measurable))

theorem remaining_eq_foldl (cs : List Component) (records : List Correction) :
    remaining cs records = records.foldl applyCorrection cs := by
  induction records generalizing cs with
  | nil => rfl
  | cons r rest ih => exact ih _

variable {X : Type*} [MeasurableSpace X]

theorem applyCorrection_measurable (cs : X → List Component) (r : X → Correction)
    (hcs : Measurable cs) (hr : Measurable r) :
    Measurable (fun z => applyCorrection (cs z) (r z)) :=
  removeCorrection_measurable cs _ _ _ _ hcs
    (correction_amount_measurable.comp hr) (correction_start_measurable.comp hr)
    (correction_first_measurable.comp hr) (correction_last_measurable.comp hr)

/-- Full Borel measurability of an actual finite sequence of corrections on
a changing endpoint-owned domain. -/
theorem remaining_measurable (cs : X → List Component) (records : X → List Correction)
    (hcs : Measurable cs) (hrecords : Measurable records) :
    Measurable (fun z => remaining (cs z) (records z)) := by
  have hstep : Measurable (fun p : X × List Component × Correction => applyCorrection p.2.1 p.2.2) :=
    applyCorrection_measurable _ _ (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)
  have h := list_foldl_measurable (fun _ cs r => applyCorrection cs r) cs records hstep hcs hrecords
  simpa only [remaining_eq_foldl] using h

theorem remainingAfterWhole_measurable (cs : X → List Component)
    (remove : X → Component → Bool) (records : X → List Correction)
    (hcs : Measurable cs) (hremove : Measurable (fun p : X × Component => remove p.1 p.2))
    (hrecords : Measurable records) :
    Measurable (fun z => remainingAfterWhole (cs z) (remove z) (records z)) := by
  apply remaining_measurable
  · apply list_filter_measurable
    · exact (measurable_of_countable (fun b : Bool => !b)).comp hremove
    · exact hcs
  · exact hrecords

theorem executeRecorded_measurable {n : ℕ} (cs : X → List Component)
    (records : X → List Correction) (history : X → UpperCircularStage.History n)
    (hcs : Measurable cs) (hrecords : Measurable records) (hhistory : Measurable history) :
    Measurable (fun z => executeRecorded (cs z) (records z) (history z)) :=
  (remaining_measurable cs records hcs hrecords).prodMk hhistory

variable (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem component_mass_measurable : Measurable (mass μ) := by
  have hp := (prefixCost_continuous μ 0).measurable
  have h : Measurable (fun c : Component => prefixCost μ 0 c.right - prefixCost μ 0 c.left) :=
    (hp.comp component_right_measurable).sub (hp.comp component_left_measurable)
  convert h using 1
  funext c
  rw [mass_eq_prefix_difference, prefix_Ioc_eq_prefixCost μ, prefix_Ioc_eq_prefixCost μ]

/-- Truthful recorded prefixes determine each accessed cached value; no
measurability hypothesis on an unobserved extension of the cache is needed. -/
theorem cached_access_measurable {Observer : Type*} (μs : Observer → Measure ℝ)
    [∀ i, IsFiniteMeasure (μs i)] [∀ i, NullSingletonClass (μs i)]
    (values : X → Observer → ℝ → ℝ) (cs : X → List Component) (c : X → Component)
    (hvalues : ∀ z, PrefixCorrect μs (values z) (cs z)) (hmem : ∀ z, c z ∈ cs z)
    (hc : Measurable c) (i : Observer) :
    Measurable (fun z => cached (values z) i (c z)) := by
  convert (component_mass_measurable (μs i)).comp hc using 1
  funext z
  exact cached_exact (values z) (cs z) (hvalues z) i (c z) (hmem z)

theorem sumValues_mass_measurable (cs : X → List Component) (hcs : Measurable cs) :
    Measurable (fun z => sumValues (mass μ) (cs z)) := by
  have hmap := list_map_measurable (fun _ c => mass μ c) cs
    ((component_mass_measurable μ).comp measurable_snd) hcs
  have hsum := list_foldl_measurable (fun (_ : X) (a b : ℝ) => a + b)
    (fun _ => (0 : ℝ)) (fun z => (cs z).map (mass μ))
    ((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd))
    measurable_const hmap
  simpa only [sumValues, List.sum_eq_foldl] using hsum

theorem domain_mass_measurable (cs : X → List Component) (hcs : Measurable cs)
    (hdisjoint : ∀ z, DisjointComponents (cs z)) :
    Measurable (fun z => μ.real (domain (cs z))) := by
  convert sumValues_mass_measurable μ cs hcs using 1
  funext z
  exact domain_mass_sum μ (cs z) (hdisjoint z)

end EnvyFreeResearch.Full.UpperDomainDifference
