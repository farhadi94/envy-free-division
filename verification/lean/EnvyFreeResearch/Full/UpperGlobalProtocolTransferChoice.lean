import EnvyFreeResearch.Full.UpperGlobalProtocolTransferFactors

/-! A first-safe finite search, with a Borel implementation rather than an
arbitrary existential selector. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Transfer
open MeasureTheory
open scoped Classical

 def firstSafe {A : Type*} (fallback : A) (good : A → Prop) : List A → A
  | [] => fallback
  | a::rest => if good a then a else firstSafe fallback good rest

theorem firstSafe_good {A : Type*} (fallback : A) (good : A → Prop) (xs : List A)
    (h : ∃ a ∈ xs, good a) : good (firstSafe fallback good xs) := by
  induction xs with
  | nil => simp at h
  | cons a rest ih =>
    unfold firstSafe
    split_ifs with ha
    · exact ha
    · apply ih
      obtain ⟨b,hb,hgood⟩ := h
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (ha hgood).elim
      · exact ⟨b,hb,hgood⟩

theorem firstSafe_measurable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (fallback : A) (good : X → A → Prop) (xs : List A)
    (hg : ∀ a, MeasurableSet {x | good x a}) :
    Measurable (fun x => firstSafe fallback (good x) xs) := by
  induction xs with
  | nil => exact measurable_const
  | cons a rest ih => exact Measurable.ite (hg a) measurable_const ih

def factorIndex {k : ℕ} (theta tau : ℝ) (x : Fin k → ℝ) (fallback : Fin k) : Fin k :=
  firstSafe fallback
    (fun e => ∀ i, factor theta tau e.val*x i ≤ 3*tau/8 ∨ 2 ≤ factor theta tau e.val*x i)
    (List.finRange k)

theorem factorIndex_safe {k : ℕ} (theta tau : ℝ) (x : Fin k → ℝ) (j : Fin k)
    (htheta : 0 < theta) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hx : ∀ i, 0 ≤ x i) (hj : x j=0) :
    ∀ i, factor theta tau (factorIndex theta tau x j).val*x i ≤ 3*tau/8 ∨
      2 ≤ factor theta tau (factorIndex theta tau x j).val*x i := by
  obtain ⟨e,he⟩ := geometric_safe_factor theta tau x j htheta htau htau1 hx hj
  exact firstSafe_good j
    (fun f : Fin k => ∀ i, factor theta tau f.val*x i ≤ 3*tau/8 ∨ 2 ≤ factor theta tau f.val*x i)
    (List.finRange k) ⟨e,List.mem_finRange e,he⟩

theorem factorIndex_measurable {k : ℕ} (theta tau : ℝ) (j : Fin k) :
    Measurable (fun x : Fin k → ℝ => factorIndex theta tau x j) := by
  apply firstSafe_measurable
  intro e
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le ((measurable_pi_apply i).const_mul _) measurable_const).union
    (measurableSet_le measurable_const ((measurable_pi_apply i).const_mul _))

end EnvyFreeResearch.Full.UpperGlobal.Transfer
