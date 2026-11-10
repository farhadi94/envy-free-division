import EnvyFreeResearch.Full.RefinedUpperWholeLinear

/-! The strengthened whole-cell construction is a deterministic Borel map
of the observed finite table: enumerate ownership tables and retain the first
one satisfying the proved inequalities. No nonmeasurable floating choice is
used in the implemented protocol. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperLinearSelector
open RefinedUpperWholeLinear
variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def Valid (a : Agent → Cell → ℝ) (t : Agent → ℝ) (A : Agent → Agent → ℝ)
    (eta : ℝ) (owned : Agent → Finset Cell) : Prop :=
  (∀ i j, i ≠ j → Disjoint (owned i) (owned j)) ∧
  (∀ j, 0 ≤ t j-load a owned j j ∧ t j-load a owned j j ≤ min (t j) eta) ∧
  (∀ i j, |load a owned i j-load a owned j j| ≤ 4*(Fintype.card Agent:ℝ)*A i j)

def firstValid (a : Agent → Cell → ℝ) (t : Agent → ℝ) (A : Agent → Agent → ℝ)
    (eta : ℝ) : List (Agent → Finset Cell) → Agent → Finset Cell
  | [] => fun _ => ∅
  | owned::rest => if Valid a t A eta owned then owned else firstValid a t A eta rest

theorem firstValid_spec (a : Agent → Cell → ℝ) (t : Agent → ℝ) (A : Agent → Agent → ℝ)
    (eta : ℝ) (candidates : List (Agent → Finset Cell))
    (hex : ∃ owned ∈ candidates, Valid a t A eta owned) :
    Valid a t A eta (firstValid a t A eta candidates) := by
  induction candidates with
  | nil => simp at hex
  | cons owned rest ih =>
    by_cases h : Valid a t A eta owned
    · simp [firstValid,h]
    · have hrest : ∃ other ∈ rest, Valid a t A eta other := by
        obtain ⟨other,hmem,hvalid⟩ := hex
        rcases List.mem_cons.mp hmem with heq|hmem
        · exact False.elim (h (heq ▸ hvalid))
        · exact ⟨other,hmem,hvalid⟩
      simpa [firstValid,h] using ih hrest

def select (a : Agent → Cell → ℝ) (t : Agent → ℝ) (A : Agent → Agent → ℝ)
    (eta : ℝ) : Agent → Finset Cell := firstValid a t A eta Finset.univ.toList

theorem select_spec (a : Agent → Cell → ℝ) (t : Agent → ℝ)
    (A : Agent → Agent → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hnormal : ∀ i, ∑ e, a i e=1) (ht : ∀ j, 0 ≤ t j) (htsum : ∑ j, t j ≤ 1)
    (hA : ∀ i j, 0 ≤ A i j) (hgap : ∀ i j e, |a i e-a j e| ≤ A i j)
    (hk : 0 < Fintype.card Agent) : Valid a t A eta (select a t A eta) := by
  apply firstValid_spec
  obtain ⟨owned,hspec⟩ := exists_whole_payments a t A eta heta ha hsmall hnormal ht htsum hA hgap hk
  exact ⟨owned,by simp,hspec⟩

section Measurability
variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_valid (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ)
    (A : X → Agent → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (ht : ∀ j, Measurable (fun z => t z j))
    (hA : ∀ i j, Measurable (fun z => A z i j)) (heta : Measurable eta)
    (owned : Agent → Finset Cell) :
    MeasurableSet {z | Valid (a z) (t z) (A z) (eta z) owned} := by
  have hl (i j : Agent) : Measurable (fun z => load (a z) owned i j) :=
    Finset.measurable_sum _ (fun e _ => ha i e)
  have ho : MeasurableSet {z | ∀ j, 0 ≤ t z j-load (a z) owned j j ∧
      t z j-load (a z) owned j j ≤ min (t z j) (eta z)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_le measurable_const ((ht j).sub (hl j j))).inter
      (measurableSet_le ((ht j).sub (hl j j)) ((ht j).min heta))
  have hd : MeasurableSet {z | ∀ i j, |load (a z) owned i j-load (a z) owned j j| ≤
      4*(Fintype.card Agent:ℝ)*A z i j} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le ((hl i j).sub (hl j j)).abs (measurable_const.mul (hA i j))
  exact (MeasurableSet.const (∀ i j, i ≠ j → Disjoint (owned i) (owned j))).inter (ho.inter hd)

variable [MeasurableSpace (Agent → Finset Cell)]
theorem firstValid_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ)
    (A : X → Agent → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (ht : ∀ j, Measurable (fun z => t z j))
    (hA : ∀ i j, Measurable (fun z => A z i j)) (heta : Measurable eta)
    (candidates : List (Agent → Finset Cell)) :
    Measurable (fun z => firstValid (a z) (t z) (A z) (eta z) candidates) := by
  induction candidates with
  | nil => exact measurable_const
  | cons owned rest ih =>
    exact measurable_const.ite (measurableSet_valid a t A eta ha ht hA heta owned) ih

theorem select_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ)
    (A : X → Agent → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (ht : ∀ j, Measurable (fun z => t z j))
    (hA : ∀ i j, Measurable (fun z => A z i j)) (heta : Measurable eta) :
    Measurable (fun z => select (a z) (t z) (A z) (eta z)) :=
  firstValid_measurable a t A eta ha ht hA heta _
end Measurability
end EnvyFreeResearch.Full.RefinedUpperLinearSelector

#print axioms EnvyFreeResearch.Full.RefinedUpperWholeLinear.exists_whole_payments
#print axioms EnvyFreeResearch.Full.RefinedUpperLinearSelector.select_spec
#print axioms EnvyFreeResearch.Full.RefinedUpperLinearSelector.select_measurable
