import EnvyFreeResearch.Full.UpperGlobalSinkGraph
import EnvyFreeResearch.Full.UpperGlobalProtocolTransferChoice
import EnvyFreeResearch.Full.UpperGlobalProtocolMeasurable

/-! A finite search on recorded Boolean edges selects a minimum-cardinality
proper sink. Every test is finite; strong connectivity is proved afterwards. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Sink
open MeasureTheory UpperGlobalPhysical GlobalCompletion
open scoped Classical
variable {n : ℕ}

abbrev GraphData (n : ℕ) := Finset (Fin n) × (Fin n → Fin n → Bool)

def select (g : GraphData n) : Finset (Fin n) :=
  Transfer.firstSafe ∅ (MinimalSink (fun i j => g.2 i j = true) g.1) Finset.univ.toList

theorem select_correct (g : GraphData n)
    (hn : ¬ StrongOn (fun i j => g.2 i j = true) g.1) :
    MinimalSink (fun i j => g.2 i j = true) g.1 (select g) := by
  obtain ⟨S,hS⟩ := exists_minimal_sink (fun i j => g.2 i j = true) g.1 hn
  exact Transfer.firstSafe_good ∅ _ _ ⟨S,by simp,hS⟩

theorem select_measurable : Measurable (select (n := n)) := measurable_of_countable _

def anchorGraph (direction : Direction) (a : Anchor n) : GraphData n :=
  (a.active,fun i j => decide (a.edge direction i j))

theorem anchor_edge_measurable (direction : Direction) (i j : Fin n) :
    MeasurableSet {a : Anchor n | a.edge direction i j} := by
  have hi : MeasurableSet {a : Anchor n | i ∈ a.active} :=
    (Set.to_countable {A : Finset (Fin n) | i ∈ A}).measurableSet.preimage anchor_active_measurable
  have hj : MeasurableSet {a : Anchor n | j ∈ a.active} :=
    (Set.to_countable {A : Finset (Fin n) | j ∈ A}).measurableSet.preimage anchor_active_measurable
  have hm : Measurable (fun a : Anchor n => margin direction a.cachedValue i j) := by
    cases direction with
    | cake =>
      exact (cachedValue_measurable id measurable_id i i).sub
        (cachedValue_measurable id measurable_id i j)
    | chore =>
      exact (cachedValue_measurable id measurable_id i j).sub
        (cachedValue_measurable id measurable_id i i)
  exact hi.inter (hj.inter ((MeasurableSet.const _).inter
    (measurableSet_lt hm (cachedResidue_measurable id measurable_id i))))

theorem anchorGraph_measurable (direction : Direction) :
    Measurable (anchorGraph (n := n) direction) := by
  apply anchor_active_measurable.prodMk
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact UpperDomainDifference.decide_measurable _ (anchor_edge_measurable direction i j)

def selectedSink (direction : Direction) (a : Anchor n) : Finset (Fin n) :=
  select (anchorGraph direction a)

theorem selectedSink_measurable (direction : Direction) :
    Measurable (selectedSink (n := n) direction) :=
  select_measurable.comp (anchorGraph_measurable direction)

theorem selectedSink_correct (direction : Direction) (a : Anchor n)
    (hn : ¬ StrongOn (a.edge direction) a.active) :
    MinimalSink (a.edge direction) a.active (selectedSink direction a) := by
  have he : (fun i j => (anchorGraph direction a).2 i j = true) = a.edge direction := by
    funext i j
    simp only [anchorGraph,decide_eq_true_eq]
  have h := select_correct (anchorGraph direction a) (by simpa only [anchorGraph,decide_eq_true_eq] using hn)
  simpa only [anchorGraph,decide_eq_true_eq,selectedSink] using h

theorem selectedSink_strong (direction : Direction) (a : Anchor n)
    (hn : ¬ StrongOn (a.edge direction) a.active) :
    StrongOn (a.edge direction) (selectedSink direction a) :=
  minimal_sink_strong _ _ _ (selectedSink_correct direction a hn)
end EnvyFreeResearch.Full.UpperGlobal.Sink
