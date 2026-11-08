import EnvyFreeResearch.Full.UpperPhysical

/-! Literal nested circular prefixes. Strictly increasing cumulative targets
prevent history-dependent plateau roots from creating gaps at equal targets. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical

theorem physical_prefix_mono (domain : Set ℝ) (start : UpperCircular.Circle) (a b : I)
    (hab : (a : ℝ) < b) (first lastA lastB : ℝ) (F : ℝ → ℝ) (hF : Monotone F)
    (hA : F lastA = (value (start + project a) : ℝ))
    (hB : F lastB = (value (start + project b) : ℝ)) :
    physicalPiece domain a start first lastA ⊆ physicalPiece domain b start first lastB := by
  by_cases ha0 : a = 0
  · rw [ha0, physicalPiece_zero]
    exact empty_subset _
  by_cases hb1 : b = 1
  · rw [hb1, physicalPiece_one]
    exact physicalPiece_subset _ _ _ _ _
  have ha : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1 (fun h => ha0 (Subtype.ext h.symm))
  have hb : (b : ℝ) < 1 := lt_of_le_of_ne b.property.2 (fun h => hb1 (Subtype.ext h))
  have ha1 : a ≠ 1 := by intro h; have he := congrArg Subtype.val h; change (a : ℝ) = 1 at he; linarith
  have hb0 : b ≠ 0 := by intro h; have he := congrArg Subtype.val h; change (b : ℝ) = 0 at he; linarith
  by_cases hsumA : (value start : ℝ) + a ≤ 1
  · have htargetA := endpoint_target_no_wrap start a hsumA
    have hnoA : value start < value (start + project a) := by
      change (value start : ℝ) < (value (start + project a) : ℝ)
      rw [htargetA]
      linarith
    by_cases hsumB : (value start : ℝ) + b ≤ 1
    · have htargetB := endpoint_target_no_wrap start b hsumB
      have hnoB : value start < value (start + project b) := by
        change (value start : ℝ) < (value (start + project b) : ℝ)
        rw [htargetB]
        linarith
      have hlast : lastA ≤ lastB := by
        by_contra hn
        have h := hF (le_of_not_ge hn)
        rw [hA, hB, htargetA, htargetB] at h
        linarith
      simp only [physicalPiece, ha0, ha1, hb0, hb1, ite_false, hnoA, hnoB, ite_true]
      intro x hx
      exact ⟨hx.1, hx.2.1, hx.2.2.trans hlast⟩
    · have htargetB := endpoint_target_wrap start b (lt_of_not_ge hsumB)
      have hwrapB : ¬value start < value (start + project b) := by
        change ¬(value start : ℝ) < (value (start + project b) : ℝ)
        rw [htargetB]
        linarith
      simp only [physicalPiece, ha0, ha1, hb0, hb1, ite_false, hnoA, hwrapB, ite_true]
      intro x hx
      exact ⟨hx.1, fun hh => (not_lt_of_ge hh.2) hx.2.1⟩
  · have hsumB : 1 < (value start : ℝ) + b := by linarith
    have htargetA := endpoint_target_wrap start a (lt_of_not_ge hsumA)
    have htargetB := endpoint_target_wrap start b hsumB
    have hwrapA : ¬value start < value (start + project a) := by
      change ¬(value start : ℝ) < (value (start + project a) : ℝ)
      rw [htargetA]
      linarith
    have hwrapB : ¬value start < value (start + project b) := by
      change ¬(value start : ℝ) < (value (start + project b) : ℝ)
      rw [htargetB]
      linarith
    have hlast : lastA ≤ lastB := by
      by_contra hn
      have h := hF (le_of_not_ge hn)
      rw [hA, hB, htargetA, htargetB] at h
      linarith
    simp only [physicalPiece, ha0, ha1, hb0, hb1, ite_false, hwrapA, hwrapB]
    intro x hx
    exact ⟨hx.1, fun hh => hx.2 ⟨hlast.trans_lt hh.1, hh.2⟩⟩

end EnvyFreeResearch.Full.UpperSnapshotSmall
