import EnvyFreeResearch.Full.ChoresSubCoreLeavesAffine
import EnvyFreeResearch.Full.ChoresMaskedGeometry

/-! The stored primary values in the concrete suffix leaves are actual
original-cost affine or clipped utilities of literal masked suffixes.
This identifies the finite SubCore comparisons with physical payments. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCoreLeaves
open Set MeasureTheory IntervalOracle Persistent Suffix SubCorePhysical

variable {n : ℕ} {Root : Type*}
variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

theorem masked_profile_monotone (domains : Root → Fin n → Set ℝ) (p : Root) (i : Fin n) :
    Monotone ((Masked.rowProfile cost (domains p)).cumulative i) :=
  prefixCost_monotone ((cost i).restrict (domains p i)) 0

theorem masked_interval_value (domains : Fin n → Set ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (i : Fin n) :
    (Masked.rowProfile cost domains).cumulative i b-
      (Masked.rowProfile cost domains).cumulative i a = (cost i).real (domains i ∩ Ioc a b) := by
  simpa only [Masked.rowProfile,OrderedUnion.restrictedProfile,measureProfile] using
    OrderedUnion.restricted_interval_value cost (domains i) ha hab i

def physicalSuffix (domains : Root → Fin n → Set ℝ) (p : Root) (i : Fin n) (x : ℝ) : Set ℝ :=
  domains p i ∩ Ioc (1-x) 1

theorem affine_primary_physical (domains : Root → Fin n → Set ℝ)
    (offset : Root → Fin n → ℝ) (p : Root) (r : Record n)
    (hsound : AffineSound (Masked.rowProfile cost (domains p)) (offset p) r)
    (hpoint : r.point ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (r.formal i).1 = (cost i).real (physicalSuffix domains p i r.point)-offset p i := by
  have hdiff := masked_interval_value cost (domains p)
    (show 0 ≤ 1-r.point by linarith [hpoint.2])
    (show 1-r.point ≤ 1 by linarith [hpoint.1]) i
  rw [hsound i]
  change ((Masked.rowProfile cost (domains p)).cumulative i 1-
    (Masked.rowProfile cost (domains p)).cumulative i (1-r.point))-offset p i = _
  rw [hdiff]
  rfl

theorem clipped_raw_physical (domains : Root → Fin n → Set ℝ)
    (offset : Root → Fin n → ℝ) (p : Root) (r : ClippedRecord n)
    (hsound : ClippedSound (Masked.rowProfile cost (domains p)) (offset p) r)
    (hpoint : r.record.point ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    r.raw i = (cost i).real (physicalSuffix domains p i r.record.point)-offset p i := by
  have hdiff := masked_interval_value cost (domains p)
    (show 0 ≤ 1-r.record.point by linarith [hpoint.2])
    (show 1-r.record.point ≤ 1 by linarith [hpoint.1]) i
  rw [hsound.1 i]
  change ((Masked.rowProfile cost (domains p)).cumulative i 1-
    (Masked.rowProfile cost (domains p)).cumulative i (1-r.record.point))-offset p i = _
  rw [hdiff]
  rfl

theorem clipped_primary_physical (domains : Root → Fin n → Set ℝ)
    (offset : Root → Fin n → ℝ) (p : Root) (r : ClippedRecord n)
    (hsound : ClippedSound (Masked.rowProfile cost (domains p)) (offset p) r)
    (hpoint : r.record.point ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (r.record.formal i).1 = max 0 ((cost i).real (physicalSuffix domains p i r.record.point)-offset p i) := by
  rw [hsound.2 i,clipped_raw_physical cost domains offset p r hsound hpoint i]

theorem primary_le_of_formal_le (a b : ℝ × ℚ) (h : toLex a ≤ toLex b) : a.1 ≤ b.1 := by
  rcases pair_lower_of_lex_le a b h with h | h
  · rcases h with h | h
    · exact h.le
    · exact h.1.le
  · exact (congrArg Prod.fst h).le

/-- Exact formal EF comparisons imply the actual affine comparisons,
including comparisons between different original parents and offsets. -/
theorem affine_comparison_physical (domains : Root → Fin n → Set ℝ)
    (offset : Root → Fin n → ℝ) (p q : Root) (r s : Record n)
    (hr : AffineSound (Masked.rowProfile cost (domains p)) (offset p) r)
    (hs : AffineSound (Masked.rowProfile cost (domains q)) (offset q) s)
    (hpr : r.point ∈ Icc (0 : ℝ) 1) (hps : s.point ∈ Icc (0 : ℝ) 1) (i : Fin n)
    (hcomp : toLex (r.formal i) ≤ toLex (s.formal i)) :
    (cost i).real (physicalSuffix domains p i r.point)-offset p i ≤
      (cost i).real (physicalSuffix domains q i s.point)-offset q i := by
  rw [← affine_primary_physical cost domains offset p r hr hpr i,
    ← affine_primary_physical cost domains offset q s hs hps i]
  exact primary_le_of_formal_le _ _ hcomp

theorem clipped_comparison_physical (domains : Root → Fin n → Set ℝ)
    (offset : Root → Fin n → ℝ) (p q : Root) (r s : ClippedRecord n)
    (hr : ClippedSound (Masked.rowProfile cost (domains p)) (offset p) r)
    (hs : ClippedSound (Masked.rowProfile cost (domains q)) (offset q) s)
    (hpr : r.record.point ∈ Icc (0 : ℝ) 1) (hps : s.record.point ∈ Icc (0 : ℝ) 1) (i : Fin n)
    (hcomp : toLex (r.record.formal i) ≤ toLex (s.record.formal i)) :
    max 0 ((cost i).real (physicalSuffix domains p i r.record.point)-offset p i) ≤
      max 0 ((cost i).real (physicalSuffix domains q i s.record.point)-offset q i) := by
  rw [← clipped_primary_physical cost domains offset p r hr hpr i,
    ← clipped_primary_physical cost domains offset q s hs hps i]
  exact primary_le_of_formal_le _ _ hcomp

end EnvyFreeResearch.Full.Chores.SubCoreLeaves
