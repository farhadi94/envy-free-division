import EnvyFreeResearch.Full.ChoresComponentRecordedSubCore
import EnvyFreeResearch.Full.ChoresPackageProposal

/-!
# Payments computed from the actual recorded retained suffixes

Only positive clipped proposals execute.  The recorded all-observer suffix
costs supply the original affine utilities, so a zero clipped proposal never
creates a fictitious credit.  Same-label SubCore comparisons and the unused
whole-parent comparison pay precisely the two cases of the merger ledger.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentPayments
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Persistent SubCore SubCorePhysical SubCoreLeaves Suffix SubCoreEntry ComponentRecording
open scoped Classical

variable {n : ℕ} {Task Root : Type*} [Fintype Task] [DecidableEq Task]
  [Fintype Root] [Nonempty Root]

def domains (blocks : Root → Fin n → Set ℝ) (label : Fin n → Fin n) :
    Root → Fin n → Set ℝ := fun s i => blocks s (label i)

def offsets (gap : Root → Fin n → Fin n → ℝ) (label : Fin n → Fin n) :
    Root → Fin n → ℝ := fun s i => gap s (label i) i

def utility {Payload : Type*} (agent : Task → Fin n) (label : Fin n → Fin n)
    (gap : Root → Fin n → Fin n → ℝ) (out : Recorded Payload Task Root n)
    (i : Fin n) (j : Task) : ℝ :=
  cachedValue (out.parts j).suffixParts i - gap (out.allocation.assigned j) (label (agent j)) i

def credit {Payload : Type*} (agent : Task → Fin n) (label : Fin n → Fin n)
    (gap : Root → Fin n → Fin n → ℝ) (out : Recorded Payload Task Root n) (j : Task) : ℝ :=
  max 0 (utility agent label gap out (agent j) j)

def execute {Payload : Type*} (agent : Task → Fin n) (label : Fin n → Fin n)
    (gap : Root → Fin n → Fin n → ℝ) (out : Recorded Payload Task Root n) (j : Task) : Bool :=
  decide (0 < credit agent label gap out j)

def extra {Payload : Type*} (agent : Task → Fin n) (label : Fin n → Fin n)
    (gap : Root → Fin n → Fin n → ℝ) (out : Recorded Payload Task Root n)
    (i : Fin n) (j : Task) : ℝ :=
  if execute agent label gap out j then max 0 (utility agent label gap out i j) else 0

theorem positive_utility {Payload : Type*} (agent : Task → Fin n) (label : Fin n → Fin n)
    (gap : Root → Fin n → Fin n → ℝ) (out : Recorded Payload Task Root n) (j : Task)
    (hj : execute agent label gap out j = true) :
    0 < utility agent label gap out (agent j) j ∧
      utility agent label gap out (agent j) j = credit agent label gap out j := by
  have hpos : 0 < credit agent label gap out j := of_decide_eq_true hj
  have hu : 0 < utility agent label gap out (agent j) j := by
    simpa only [credit, lt_max_iff, lt_self_iff_false, false_or] using hpos
  exact ⟨hu, (max_eq_right hu.le).symm⟩

theorem actual_credit {Payload : Type*} (agent : Task → Fin n) (label : Fin n → Fin n)
    (gap : Root → Fin n → Fin n → ℝ) (out : Recorded Payload Task Root n) (j : Task) :
    (if execute agent label gap out j then utility agent label gap out (agent j) j else 0) =
      credit agent label gap out j := by
  by_cases hj : execute agent label gap out j = true
  · simp only [hj, ite_true]
    exact (positive_utility agent label gap out j hj).2
  · have hnonpos : credit agent label gap out j ≤ 0 := by
      exact le_of_not_gt (fun h => hj (decide_eq_true h))
    have hz : credit agent label gap out j = 0 :=
      le_antisymm hnonpos (le_max_left _ _)
    simp [hj, hz]

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ) (agent : Task → Fin n) (label : Fin n → Fin n)
  (gap : Root → Fin n → Fin n → ℝ) {Payload : Type*}
  (out : Recorded Payload Task Root n)
  (hparts : PartsCorrect cost (domains blocks label) agent out)
include hparts

theorem suffix_subset (j : Task) :
    material (out.parts j).suffixParts ⊆ blocks (out.allocation.assigned j) (label (agent j)) := by
  rw [(hparts j).2.2.2]
  exact inter_subset_left

theorem suffix_values (i : Fin n) (j : Task) :
    utility agent label gap out i j =
      (cost i).real (material (out.parts j).suffixParts) -
        gap (out.allocation.assigned j) (label (agent j)) i := by
  unfold utility
  rw [material_value cost _ (hparts j).2.1 (hparts j).2.2.1]

theorem same_label_utility (i j : Task) (hlabel : label (agent j) = label (agent i)) :
    utility agent label gap out (agent i) j =
      affineUtility cost (domains blocks label) (offsets gap label)
        (out.allocation.assigned j) (agent i)
        (out.allocation.point (out.allocation.assigned j)).record.point := by
  rw [suffix_values cost blocks agent label gap out hparts]
  rw [(hparts j).2.2.2]
  simp only [affineUtility, physicalSuffix, domains, offsets, hlabel]

theorem clipped_comparison
    (hcorrect : PhysicalCorrect (clippedUtility cost (domains blocks label) (offsets gap label))
      agent out.allocation) (i j : Task) (hlabel : label (agent j) = label (agent i)) :
    max 0 (utility agent label gap out (agent i) j) ≤ credit agent label gap out i := by
  have h := hcorrect.best i (out.allocation.assigned j)
  unfold credit
  rw [same_label_utility cost blocks agent label gap out hparts i j hlabel,
    same_label_utility cost blocks agent label gap out hparts i i rfl]
  exact h

theorem stripped_comparison
    (hcorrect : PhysicalCorrect (clippedUtility cost (domains blocks label) (offsets gap label))
      agent out.allocation) (i j : Task) (hlabel : label (agent j) = label (agent i)) :
    extra agent label gap out (agent i) j ≤ credit agent label gap out i := by
  unfold extra
  split
  · exact clipped_comparison cost blocks agent label gap out hparts hcorrect i j hlabel
  · exact le_max_left _ _

theorem affine_own_nonnegative
    (hcorrect : PhysicalCorrect (affineUtility cost (domains blocks label) (offsets gap label))
      agent out.allocation) (i : Task) :
    0 ≤ utility agent label gap out (agent i) i := by
  rw [same_label_utility cost blocks agent label gap out hparts i i rfl]
  exact hcorrect.nonnegative i

theorem affine_comparison
    (hcorrect : PhysicalCorrect (affineUtility cost (domains blocks label) (offsets gap label))
      agent out.allocation) (i j : Task) (hlabel : label (agent j) = label (agent i)) :
    max 0 (utility agent label gap out (agent i) j) ≤ utility agent label gap out (agent i) i := by
  apply max_le
  · exact affine_own_nonnegative cost blocks agent label gap out hparts hcorrect i
  · rw [same_label_utility cost blocks agent label gap out hparts i j hlabel,
      same_label_utility cost blocks agent label gap out hparts i i rfl]
    exact hcorrect.best i (out.allocation.assigned j)

theorem affine_whole_retained
    (hcorrect : PhysicalCorrect (affineUtility cost (domains blocks label) (offsets gap label))
      agent out.allocation)
    (hcache : Masked.CacheCorrect (measureProfile cost) (domains blocks label) out.cache) :
    ∃ j, material (out.parts j).suffixParts = blocks (out.allocation.assigned j) (label (agent j)) ∧
      0 ≤ utility agent label gap out (agent j) j := by
  obtain ⟨j, hj⟩ := hcorrect.whole
  refine ⟨j, ?_, affine_own_nonnegative cost blocks agent label gap out hparts hcorrect j⟩
  rw [(hparts j).2.2.2, hj, sub_self]
  exact inter_eq_left.mpr
    (cached_domain_subset cost (domains blocks label) out.cache hcache _ _)

theorem protected_utility_nonpositive (i : Fin n) (j : Task)
    (hprotected : (cost i).real (blocks (out.allocation.assigned j) (label (agent j))) ≤
      gap (out.allocation.assigned j) (label (agent j)) i) :
    utility agent label gap out i j ≤ 0 := by
  have hmono := measureReal_mono (μ := cost i) (suffix_subset cost blocks agent label out hparts j)
  rw [suffix_values cost blocks agent label gap out hparts]
  linarith

theorem protected_extra_zero (i : Fin n) (j : Task)
    (hprotected : (cost i).real (blocks (out.allocation.assigned j) (label (agent j))) ≤
      gap (out.allocation.assigned j) (label (agent j)) i) :
    extra agent label gap out i j = 0 := by
  have hu := protected_utility_nonpositive cost blocks agent label gap out hparts i j hprotected
  simp only [extra, max_eq_left hu, ite_self]

theorem unused_threshold
    (hcorrect : PhysicalCorrect (clippedUtility cost (domains blocks label) (offsets gap label))
      agent out.allocation)
    (hcache : Masked.CacheCorrect (measureProfile cost) (domains blocks label) out.cache)
    (unused : Root) (hunused : ∀ j, out.allocation.assigned j ≠ unused) (i : Task) :
    max 0 ((cost (agent i)).real (blocks unused (label (agent i))) -
      gap unused (label (agent i)) (agent i)) ≤ credit agent label gap out i := by
  have h := hcorrect.best i unused
  rw [hcorrect.unused unused hunused] at h
  unfold clippedUtility affineUtility at h
  rw [physical_suffix_whole cost (domains blocks label) out.cache hcache unused (agent i)] at h
  unfold credit
  rw [same_label_utility cost blocks agent label gap out hparts i i rfl]
  exact h

theorem complementary_credit (parent : Root → Fin n → Set ℝ) (baseline : Root → Fin n → ℝ)
    (hblock : ∀ s p, blocks s p ⊆ parent s p)
    (hgap : ∀ s p i, gap s p i = (cost i).real (parent s p) - baseline s i)
    (i : Fin n) (j : Task) :
    baseline (out.allocation.assigned j) i -
      (cost i).real (parent (out.allocation.assigned j) (label (agent j)) \
        material (out.parts j).suffixParts) = utility agent label gap out i j := by
  rw [suffix_values cost blocks agent label gap out hparts, hgap]
  exact PackageGeometry.physical_complement_credit (cost i) _ _
    ((suffix_subset cost blocks agent label out hparts j).trans (hblock _ _))
    (material_measurable _) _

end EnvyFreeResearch.Full.Chores.ComponentPayments
