import EnvyFreeResearch.Full.UpperDomainDifferenceCache

/-!
# Sequential recorded corrections and unchanged query history

The excluded physical set is built from the actual current domain at every
step. The final remaining-domain equality is then proved by list induction.
All operations consume recorded endpoints and cached real arithmetic only.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain UpperPhysical

structure Correction where
  amount : I
  start : UpperCircular.Circle
  first : ℝ
  last : ℝ

def applyCorrection (cs : List Component) (r : Correction) : List Component :=
  removeCorrection cs r.amount r.start r.first r.last

def correctionPiece (cs : List Component) (r : Correction) : Set ℝ :=
  physicalPiece (domain cs) r.amount r.start r.first r.last

def remaining : List Component → List Correction → List Component
  | cs, [] => cs
  | cs, r :: rest => remaining (applyCorrection cs r) rest

def excluded : List Component → List Correction → Set ℝ
  | _, [] => ∅
  | cs, r :: rest => correctionPiece cs r ∪ excluded (applyCorrection cs r) rest

theorem remaining_domain (cs : List Component) (records : List Correction) :
    domain (remaining cs records) = domain cs \ excluded cs records := by
  induction records generalizing cs with
  | nil => simp [remaining, excluded]
  | cons r rest ih =>
    rw [remaining, ih]
    change domain (removeCorrection cs r.amount r.start r.first r.last) \ _ = _
    rw [removeCorrection_domain]
    ext x
    simp only [excluded, correctionPiece, mem_sdiff, mem_union]
    tauto

theorem remaining_ordered (cs : List Component) (records : List Correction) (hcs : Ordered cs) :
    Ordered (remaining cs records) := by
  induction records generalizing cs with
  | nil => exact hcs
  | cons r rest ih =>
    exact ih _ (removeCorrection_ordered cs hcs r.amount r.start r.first r.last)

theorem remaining_disjoint (cs : List Component) (records : List Correction)
    (hcs : DisjointComponents cs) : DisjointComponents (remaining cs records) := by
  induction records generalizing cs with
  | nil => exact hcs
  | cons r rest ih =>
    exact ih _ (removeCorrection_disjoint cs hcs r.amount r.start r.first r.last)

def endpoints (records : List Correction) : List ℝ :=
  records.flatMap (fun r => [r.first, r.last])

theorem remaining_recorded (cs : List Component) (records : List Correction) {p : ℝ}
    (hp : Recorded (remaining cs records) p) : p ∈ endpoints records ∨ Recorded cs p := by
  induction records generalizing cs with
  | nil => exact Or.inr hp
  | cons r rest ih =>
    rcases ih (applyCorrection cs r) hp with hp | hp
    · exact Or.inl (by simp [endpoints] at hp ⊢; exact Or.inr (Or.inr hp))
    · rcases removeCorrection_recorded cs r.amount r.start r.first r.last hp with h | h | h
      · exact Or.inl (by simp [endpoints, h])
      · exact Or.inl (by simp [endpoints, h])
      · exact Or.inr h

theorem remaining_prefixCorrect {Observer : Type*} {μ : Observer → Measure ℝ}
    (values : Observer → ℝ → ℝ) (cs : List Component) (hvalues : PrefixCorrect μ values cs)
    (records : List Correction)
    (hrecords : ∀ i p, p ∈ endpoints records → values i p = (μ i).real (Ioc 0 p)) :
    PrefixCorrect μ values (remaining cs records) := by
  intro i p hp
  rcases remaining_recorded cs records hp with hp | hp
  · exact hrecords i p hp
  · exact hvalues i p hp

theorem remaining_cached_exact {Observer : Type*} {μ : Observer → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (values : Observer → ℝ → ℝ) (cs : List Component) (hvalues : PrefixCorrect μ values cs)
    (records : List Correction)
    (hrecords : ∀ i p, p ∈ endpoints records → values i p = (μ i).real (Ioc 0 p))
    (i : Observer) (c : Component) (hc : c ∈ remaining cs records) :
    cached values i c = mass (μ i) c :=
  cached_exact values _ (remaining_prefixCorrect values cs hvalues records hrecords) i c hc

/-- Pure finite postprocessing of already recorded corrections. No oracle
policy is an argument, and the answered history is returned unchanged. -/
def executeRecorded {n : ℕ} (cs : List Component) (records : List Correction)
    (history : UpperCircularStage.History n) : List Component × UpperCircularStage.History n :=
  (remaining cs records, history)

theorem executeRecorded_history {n : ℕ} (cs : List Component) (records : List Correction)
    (history : UpperCircularStage.History n) : (executeRecorded cs records history).2 = history := rfl

theorem executeRecorded_query_increment {n : ℕ} (cs : List Component) (records : List Correction)
    (history : UpperCircularStage.History n) :
    (executeRecorded cs records history).2.length - history.length = 0 := Nat.sub_self _

/-- Whole-cell exclusions followed by the actual sequential corrections. -/
def remainingAfterWhole (cs : List Component) (remove : Component → Bool)
    (records : List Correction) : List Component :=
  remaining (cs.filter (fun c => !remove c)) records

theorem remainingAfterWhole_domain (cs : List Component) (hcs : DisjointComponents cs)
    (remove : Component → Bool) (records : List Correction) :
    domain (remainingAfterWhole cs remove records) = domain cs \
      (domain (cs.filter remove) ∪ excluded (cs.filter (fun c => !remove c)) records) := by
  rw [remainingAfterWhole, remaining_domain, whole_filter_domain cs hcs]
  ext x
  simp only [mem_sdiff, mem_union]
  tauto


/-- The next correction's total domain mass is an exact sum of its updated
component cache, for every original observer. -/
theorem remaining_mass_sum {Observer : Type*} {μ : Observer → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (values : Observer → ℝ → ℝ) (cs : List Component) (hcs : DisjointComponents cs)
    (hvalues : PrefixCorrect μ values cs) (records : List Correction)
    (hrecords : ∀ i p, p ∈ endpoints records → values i p = (μ i).real (Ioc 0 p)) (i : Observer) :
    (μ i).real (domain (remaining cs records)) =
      sumValues (cached values i) (remaining cs records) := by
  rw [domain_mass_sum (μ i) _ (remaining_disjoint cs records hcs)]
  exact (cached_sum_eq (μ i) _ _
    (fun c hc => remaining_cached_exact values cs hvalues records hrecords i c hc)).symm

end EnvyFreeResearch.Full.UpperDomainDifference
