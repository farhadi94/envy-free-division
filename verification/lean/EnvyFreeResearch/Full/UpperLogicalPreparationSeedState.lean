import EnvyFreeResearch.Full.UpperLogicalPreparationState
import EnvyFreeResearch.Full.UpperSeeds

/-!
# Recorded physical states for threshold seed unions

A seed is computed by finite witness indices and the cached signed threshold
rule, then retained from the final recorded atoms. It makes no oracle calls.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperGridCells UpperLogicalCells UpperSeeds

variable {Fine : Type*} [Fintype Fine] {L n m : ℕ}

def seedIndices (witnesses : Fin L → Fine) (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) : Finset Fine :=
  Finset.univ.filter (fun e => ∃ a, e = witnesses a ∧ kept gamma threshold a)

theorem selectedUnion_seedIndices (fine : Fine → Set ℝ) (witnesses : Fin L → Fine)
    (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) :
    selectedUnion fine (seedIndices witnesses gamma threshold) =
      ⋃ a, if kept gamma threshold a then fine (witnesses a) else ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ := (mem_selectedUnion _ _ x).mp hx
    obtain ⟨a, rfl, ha⟩ := (Finset.mem_filter.mp he).2
    exact mem_iUnion.mpr ⟨a, by simpa only [ha, ite_true] using hxe⟩
  · intro hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    by_cases hk : kept gamma threshold a
    · exact (mem_selectedUnion _ _ x).mpr ⟨witnesses a, by simp [seedIndices]; exact ⟨a, rfl, hk⟩,
        by simpa only [hk, ite_true] using ha⟩
    · simp only [hk, ite_false, mem_empty_iff_false] at ha

variable {X : Type*} [MeasurableSpace X]

theorem kept_measurableSet (gamma : X → Fin L → ℝ) (threshold : X → Fin (L + 1))
    (hgamma : ∀ a, Measurable (fun z => gamma z a)) (hthreshold : Measurable threshold) (a : Fin L) :
    MeasurableSet {z | kept (gamma z) (threshold z) a} := by
  have heq : {z | kept (gamma z) (threshold z) a} =
      ⋃ t : Fin (L + 1), ({z | threshold z = t} ∩ {z | kept (gamma z) t a}) := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · exact fun h => ⟨threshold z, rfl, h⟩
    · rintro ⟨t, ht, h⟩
      simpa only [ht] using h
  rw [heq]
  apply MeasurableSet.iUnion
  intro t
  apply (measurableSet_eq_fun hthreshold measurable_const).inter
  unfold kept
  split_ifs
  · exact measurableSet_lt measurable_const (hgamma a)
  · exact measurableSet_lt (hgamma a) measurable_const

theorem seedIndices_measurable [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
    (witnesses : X → Fin L → Fine) (gamma : X → Fin L → ℝ) (threshold : X → Fin (L + 1))
    (hwitnesses : ∀ a, Measurable (fun z => witnesses z a))
    (hgamma : ∀ a, Measurable (fun z => gamma z a)) (hthreshold : Measurable threshold) :
    Measurable (fun z => seedIndices (witnesses z) (gamma z) (threshold z)) := by
  apply measurable_finset_iff.mpr
  intro e
  apply measurableSet_setOfPred.mp
  have heq : {z | e ∈ seedIndices (witnesses z) (gamma z) (threshold z)} =
      ⋃ a, ({z | e = witnesses z a} ∩ {z | kept (gamma z) (threshold z) a}) := by
    ext z
    simp only [seedIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion (fun a =>
    (measurableSet_eq_fun measurable_const (hwitnesses a)).inter
      (kept_measurableSet gamma threshold hgamma hthreshold a))

def seedState (state : State n) (cuts : Fin (m + 2) → ℝ) (witnesses : Fin L → Fin (m + 1))
    (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) : State n :=
  retain state cuts (seedIndices witnesses gamma threshold)

theorem seedState_domain (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (witnesses : Fin L → Fin (m + 1)) (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) :
    domain (seedState state cuts witnesses gamma threshold).cells =
      ⋃ a, if kept gamma threshold a then cell (domain state.cells) cuts (witnesses a) else ∅ := by
  rw [seedState, retain_domain state cuts hzero hmono hsep, selectedUnion_seedIndices]

theorem seedState_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (state : State n) (hstate : WellFormed μ state) (cuts : Fin (m + 2) → ℝ)
    (witnesses : Fin L → Fin (m + 1)) (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) :
    WellFormed μ (seedState state cuts witnesses gamma threshold) :=
  retain_wellFormed μ state hstate cuts _

theorem seedState_history (state : State n) (cuts : Fin (m + 2) → ℝ)
    (witnesses : Fin L → Fin (m + 1)) (gamma : Fin L → ℝ) (threshold : Fin (L + 1)) :
    (seedState state cuts witnesses gamma threshold).history = state.history := rfl

theorem seedState_measurable (state : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (witnesses : X → Fin L → Fin (m + 1)) (gamma : X → Fin L → ℝ) (threshold : X → Fin (L + 1))
    (hstate : Measurable state) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (hwitnesses : ∀ a, Measurable (fun z => witnesses z a))
    (hgamma : ∀ a, Measurable (fun z => gamma z a)) (hthreshold : Measurable threshold) :
    Measurable (fun z => seedState (state z) (cuts z) (witnesses z) (gamma z) (threshold z)) :=
  retain_measurable state cuts _ hstate hcuts
    (seedIndices_measurable witnesses gamma threshold hwitnesses hgamma hthreshold)

end EnvyFreeResearch.Full.UpperLogicalPreparation
