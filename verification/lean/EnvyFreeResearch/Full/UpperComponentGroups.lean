import EnvyFreeResearch.Full.UpperComponentFamily

/-! Query-free grouping of recorded pieces into prescribed recipient
columns, retaining complete history and literal material. -/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperComponentAssembly

open UpperRecordedDomain UpperCorrectionExecution UpperEndpointCache UpperCircularStage

variable {n r k : ℕ}

def empty (history : History n) : State n := ⟨[], history⟩

theorem empty_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (history : History n) (htruth : Truthful μ history) :
    WellFormed μ (empty history) := by
  refine ⟨by simp [empty, Ordered], by simp [empty, DisjointComponents], htruth, ?_⟩
  intro i p hp
  obtain ⟨c, hc, _⟩ := hp
  simp [empty] at hc

theorem empty_measurable {X : Type} [MeasurableSpace X] (history : X → History n)
    (hhistory : Measurable history) : Measurable (fun x => empty (history x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x => (([] : List Component), history x))
  exact measurable_const.prodMk hhistory

def group (pieces : Fin r → State n) (column : Fin r → Fin k) (c : Fin k) (history : History n) : State n :=
  family (fun j => if column j = c then pieces j else empty history) history

theorem group_domain (pieces : Fin r → State n) (column : Fin r → Fin k) (c : Fin k) (history : History n) :
    domain (group pieces column c history).cells = ⋃ j, if column j = c then domain (pieces j).cells else ∅ := by
  rw [group, family_domain]
  apply iUnion_congr
  intro j
  split_ifs <;> rfl

theorem group_history (pieces : Fin r → State n) (column : Fin r → Fin k) (c : Fin k) (history : History n) :
    (group pieces column c history).history = history := rfl

theorem group_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (pieces : Fin r → State n) (column : Fin r → Fin k)
    (c : Fin k) (history : History n) (hpieces : ∀ j, WellFormed μ (pieces j))
    (hpair : Pairwise (fun i j => Disjoint (domain (pieces i).cells) (domain (pieces j).cells)))
    (htruth : Truthful μ history) (hhistory : ∀ j, (pieces j).history ⊆ history) :
    WellFormed μ (group pieces column c history) := by
  refine family_wellFormed μ _ history ?_ ?_ htruth ?_
  · intro j
    split_ifs
    · exact hpieces j
    · exact empty_wellFormed μ history htruth
  · intro i j hij
    split_ifs <;> first | exact hpair hij | simp [empty, domain]
  · intro j
    split_ifs
    · exact hhistory j
    · exact Subset.rfl

theorem group_measurable {X : Type} [MeasurableSpace X] (pieces : X → Fin r → State n)
    (column : Fin r → Fin k) (c : Fin k) (history : X → History n)
    (hpieces : ∀ j, Measurable (fun x => pieces x j)) (hhistory : Measurable history) :
    Measurable (fun x => group (pieces x) column c (history x)) := by
  apply family_measurable _ history _ hhistory
  intro j
  by_cases hj : column j = c
  · simpa only [hj, ite_true] using hpieces j
  · simpa only [hj, ite_false] using empty_measurable history hhistory

def packages (old : Fin k → State n) (pieces : Fin r → State n) (column : Fin r → Fin k)
    (history : History n) (c : Fin k) : State n :=
  join (old c) (group pieces column c history) history

theorem packages_domain (old : Fin k → State n) (pieces : Fin r → State n) (column : Fin r → Fin k)
    (history : History n) (c : Fin k) :
    domain (packages old pieces column history c).cells =
      domain (old c).cells ∪ ⋃ j, if column j = c then domain (pieces j).cells else ∅ := by
  rw [packages, join_domain, group_domain]

theorem packages_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (old : Fin k → State n) (pieces : Fin r → State n)
    (column : Fin r → Fin k) (history : History n) (hold : ∀ c, WellFormed μ (old c))
    (hpieces : ∀ j, WellFormed μ (pieces j))
    (hpair : Pairwise (fun i j => Disjoint (domain (pieces i).cells) (domain (pieces j).cells)))
    (hdis : ∀ c j, Disjoint (domain (old c).cells) (domain (pieces j).cells))
    (htruth : Truthful μ history) (holdHistory : ∀ c, (old c).history ⊆ history)
    (hpieceHistory : ∀ j, (pieces j).history ⊆ history) (c : Fin k) :
    WellFormed μ (packages old pieces column history c) := by
  apply join_wellFormed μ _ _ history (hold c)
    (group_wellFormed μ pieces column c history hpieces hpair htruth hpieceHistory) _ htruth (holdHistory c) Subset.rfl
  rw [group_domain]
  apply disjoint_iUnion_right.mpr
  intro j
  split_ifs
  · exact hdis c j
  · exact disjoint_empty _

theorem packages_measurable {X : Type} [MeasurableSpace X] (old : X → Fin k → State n)
    (pieces : X → Fin r → State n) (column : Fin r → Fin k) (history : X → History n)
    (hold : ∀ c, Measurable (fun x => old x c)) (hpieces : ∀ j, Measurable (fun x => pieces x j))
    (hhistory : Measurable history) (c : Fin k) :
    Measurable (fun x => packages (old x) (pieces x) column (history x) c) :=
  join_measurable _ _ history (hold c) (group_measurable pieces column c history hpieces hhistory) hhistory

end EnvyFreeResearch.Full.UpperComponentAssembly
