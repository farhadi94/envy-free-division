import EnvyFreeResearch.Full.ChoresSubCoreLeavesMeasures

/-! Top-level SubCore totals are computed from the existing original-cost
component cache. No additional free evaluations or masked oracle are supplied. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCoreEntry
open Set MeasureTheory IntervalOracle SubCorePhysical SubCoreLeaves OrderedUnion
variable {n : ℕ} {Root : Type*}

def cachedTotals (cache : Masked.Cache Root n) (p : Root) (i : Fin n) : ℝ :=
  OrderedUnion.cachedValue (cache p i) i

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
  (hc : Masked.CacheCorrect (measureProfile cost) domains cache)

include hc

theorem cached_domain_subset (p : Root) (i : Fin n) : domains p i ⊆ Ioc (0 : ℝ) 1 := by
  intro x hx
  have hm : x ∈ material (cache p i) := (hc p i).2.2.symm ▸ hx
  obtain ⟨part,hpart,hxpart⟩ := (mem_material_iff _ _).mp hm
  have hb := ((valid_iff_forall _ _).mp (hc p i).1 part hpart).1
  exact ⟨hb.1.trans_lt hxpart.1,hxpart.2.trans hb.2.2⟩

theorem cached_totals_profile (p : Root) (i : Fin n) :
    cachedTotals cache p i = (Masked.rowProfile cost (domains p)).cumulative i 1 := by
  have hmat : material (cache p i) = domains p i ∩ Ioc (0 : ℝ) 1 :=
    (hc p i).2.2.trans (inter_eq_left.mpr (cached_domain_subset cost domains cache hc p i)).symm
  have hv := cached_restricted_interval cost (domains p i) (a := 0) (b := 1)
    (by norm_num) (by norm_num) (cache p i) (hc p i).1 (hc p i).2.1 hmat i
  rw [(restrictedProfile cost (domains p i)).zero i,sub_zero] at hv
  simpa only [cachedTotals,Masked.rowProfile,restrictedProfile,measureProfile] using hv.symm

theorem cached_totals_measure (p : Root) (i : Fin n) :
    cachedTotals cache p i = (cost i).real (domains p i) := by
  change OrderedUnion.cachedValue (cache p i) i = _
  rw [← material_value cost (cache p i) (hc p i).1 (hc p i).2.1 i,(hc p i).2.2]

theorem physical_suffix_whole (p : Root) (i : Fin n) :
    physicalSuffix domains p i 1 = domains p i := by
  simp only [physicalSuffix,sub_self]
  exact inter_eq_left.mpr (cached_domain_subset cost domains cache hc p i)

end EnvyFreeResearch.Full.Chores.SubCoreEntry
