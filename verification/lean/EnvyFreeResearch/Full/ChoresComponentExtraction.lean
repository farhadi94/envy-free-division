import EnvyFreeResearch.Full.ChoresComponentClosed
import EnvyFreeResearch.Full.ChoresAugmentComplement

/-! The terminal extraction domain is the union of complete assigned
physical suffixes. Its cache, disjointness, and size bounds are derived
from those actual outputs, including affine-zero assignments. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentExtraction
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ComponentRecording
open ComponentPayments Persistent SubCoreEntry
open scoped Classical BigOperators

variable {n : ℕ} {Task Root Payload : Type*} [Fintype Task] [DecidableEq Task]
  [Fintype Root] [Nonempty Root]
  (agent : Task → Fin n) (label : Fin n → Fin n) (out : Recorded Payload Task Root n)

def extracted : Set ℝ := ⋃ j, material (out.parts j).suffixParts

def extractedCache : List (Parent n) :=
  Augment.joinLabels (fun j => (out.parts j).suffixParts) Finset.univ.toList

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ)
  (hparts : PartsCorrect cost (domains blocks label) agent out)

include hparts

theorem suffix_family_valid
    (hdisjoint : ∀ s t, s ≠ t → ∀ p q, Disjoint (blocks s p) (blocks t q)) :
    Augment.FamilyValid (measureProfile cost) (fun j => (out.parts j).suffixParts) := by
  refine ⟨fun j => ⟨(hparts j).2.1, (hparts j).2.2.1⟩, ?_⟩
  intro i j hij
  exact (hdisjoint _ _ (fun heq => hij (out.allocation.assigned.injective heq)) _ _).mono
    (suffix_subset cost blocks agent label out hparts i)
    (suffix_subset cost blocks agent label out hparts j)

theorem extracted_cache_correct
    (hdisjoint : ∀ s t, s ≠ t → ∀ p q, Disjoint (blocks s p) (blocks t q)) :
    CacheValid (measureProfile cost) (extracted out) (extractedCache out) := by
  obtain ⟨hv, ho, hm⟩ := Augment.join_labels_valid (measureProfile cost)
    (fun j => (out.parts j).suffixParts)
    (suffix_family_valid agent label out cost blocks hparts hdisjoint)
    Finset.univ.toList (Finset.nodup_toList _)
  exact ⟨hv, ho, by simpa only [extractedCache, extracted, Finset.mem_toList,
    Finset.mem_univ, iUnion_true] using hm⟩

theorem extracted_small (i : Fin n) (H r : ℝ) (hH : 0 < H) (hr : 0 ≤ r)
    (hcard : Fintype.card Task ≤ n)
    (hsmall : ∀ j, (cost i).real (blocks (out.allocation.assigned j) (label (agent j))) ≤
      (n : ℝ) * r / H) :
    (cost i).real (extracted out) ≤ (n : ℝ) ^ 2 * r / H := by
  have hone (j : Task) : (cost i).real (material (out.parts j).suffixParts) ≤ (n : ℝ) * r / H :=
    (measureReal_mono (μ := cost i) (suffix_subset cost blocks agent label out hparts j)).trans
      (hsmall j)
  calc
    (cost i).real (extracted out) ≤ ∑ j : Task, (cost i).real (material (out.parts j).suffixParts) :=
      measureReal_iUnion_fintype_le (μ := cost i) _
    _ ≤ ∑ _j : Task, (n : ℝ) * r / H := Finset.sum_le_sum (fun j _ => hone j)
    _ = (Fintype.card Task : ℝ) * ((n : ℝ) * r / H) := by simp
    _ ≤ (n : ℝ) * ((n : ℝ) * r / H) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hr) hH.le)
    _ = _ := by ring

omit hparts in
theorem extracted_large (i : Fin n) (H r : ℝ) (atoms : Root → Set ℝ)
    (hlarge : ∀ s, H * r ≤ (cost i).real (atoms s))
    (hcontains : ∀ j, atoms (out.allocation.assigned j) ⊆
      blocks (out.allocation.assigned j) (label (agent j)))
    (hwhole : ∃ j, material (out.parts j).suffixParts =
      blocks (out.allocation.assigned j) (label (agent j))) :
    H * r ≤ (cost i).real (extracted out) := by
  obtain ⟨j, hj⟩ := hwhole
  apply (hlarge (out.allocation.assigned j)).trans
  exact measureReal_mono (μ := cost i) (fun x hx =>
    mem_iUnion.mpr ⟨j, hj.symm ▸ hcontains j hx⟩)

theorem terminal_deviation (gap : Root → Fin n → Fin n → ℝ)
    (parent : Root → Fin n → Set ℝ) (baseline : Root → Fin n → ℝ)
    (hblock : ∀ s p, blocks s p ⊆ parent s p)
    (hgap : ∀ s p i, gap s p i = (cost i).real (parent s p) - baseline s i)
    (i : Fin n) (j : Task) (H r : ℝ)
    (hlarge : H * r ≤ gap (out.allocation.assigned j) (label (agent j)) i)
    (hsmall : (cost i).real (blocks (out.allocation.assigned j) (label (agent j))) ≤
      (n : ℝ) * r / H) :
    (H - (n : ℝ) / H) * r ≤
      (cost i).real (parent (out.allocation.assigned j) (label (agent j)) \
        material (out.parts j).suffixParts) - baseline (out.allocation.assigned j) i := by
  have hsub := (suffix_subset cost blocks agent label out hparts j).trans (hblock _ _)
  rw [measureReal_sdiff hsub (material_measurable _)]
  have hrem := measureReal_mono (μ := cost i)
    (suffix_subset cost blocks agent label out hparts j)
  rw [hgap] at hlarge
  have heq : (H - (n : ℝ) / H) * r = H * r - (n : ℝ) * r / H := by ring
  rw [heq]
  linarith

end EnvyFreeResearch.Full.Chores.ComponentExtraction
