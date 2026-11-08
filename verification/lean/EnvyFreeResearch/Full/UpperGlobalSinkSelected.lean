import EnvyFreeResearch.Full.UpperGlobalSinkFreeze
import EnvyFreeResearch.Full.UpperGlobalSinkChoice

/-! The concrete cached selection followed by physical freezing. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Sink
open MeasureTheory Set UpperGlobalPhysical GlobalCompletion
open scoped Classical
variable {n : ℕ}

def selectedFreeze (direction : Direction) (a : Anchor n) : Anchor n :=
  freezeAnchor a direction (selectedSink direction a)

theorem selectedFreeze_measurable (direction : Direction) :
    Measurable (selectedFreeze (n := n) direction) := by
  apply anchor_mk_measurable
  · intro j
    exact anchor_bundle_measurable id measurable_id j
  · exact anchor_residue_measurable
  · have hret : Measurable (fun x : Finset (Fin n) × Finset (Fin n) =>
        retained direction x.1 x.2) := measurable_of_countable _
    exact hret.comp (anchor_active_measurable.prodMk (selectedSink_measurable direction))

theorem selectedFreeze_progress (direction : Direction) (a : Anchor n)
    (hn : ¬ StrongOn (a.edge direction) a.active) :
    (selectedFreeze direction a).active.Nonempty ∧
    (selectedFreeze direction a).active ⊆ a.active ∧
    (selectedFreeze direction a).active.card < a.active.card := by
  have hs := (selectedSink_correct direction a hn).1
  have hsub := retained_subset direction a.active (selectedSink direction a) hs.2.1
  have hp := retained_progress direction (a.edge direction) a.active (selectedSink direction a) hs
  refine ⟨hp.1,hsub,Finset.card_lt_card ?_⟩
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
  intro heq
  obtain ⟨i,hi,hnot⟩ := hp.2
  have hiNew : i ∈ (selectedFreeze direction a).active := heq.symm ▸ hi
  exact hnot hiNew

theorem selected_cross_target (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n)
    (direction : Direction) (ha : a.Physical μ whole)
    (hn : ¬ StrongOn (a.edge direction) a.active)
    (i : Fin n) (hi : i ∈ selectedSink direction a)
    (j : Fin n) (hj : j ∈ a.active) (hjS : j ∉ selectedSink direction a) :
    j ∈ R4GlobalPotential.targets (margin direction (a.table μ).value) (a.table μ).residue i := by
  have h := sink_cross_dominates a direction (selectedSink direction a)
    (selectedSink_correct direction a hn).1 i hi j hj hjS
  rw [cachedValue_correct μ whole a ha,cachedResidue_correct μ whole a ha] at h
  simpa only [R4GlobalPotential.targets,Finset.mem_filter,Finset.mem_univ,true_and] using h

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n) (direction : Direction)
  (hn : ¬ StrongOn (a.edge direction) a.active)
include hn

def selectedFreeze_event (ha : a.Physical μ whole) :
    CompletionEvent direction (a.table μ) ((selectedFreeze direction a).table μ) :=
  freeze_event μ whole a direction (selectedSink direction a)
    (selectedSink_correct direction a hn).1 ha

theorem selectedFreeze_committed (ha : a.Committed μ direction whole) :
    (selectedFreeze direction a).Committed μ direction whole :=
  freeze_committed μ whole a direction (selectedSink direction a)
    (selectedSink_correct direction a hn).1 ha

end EnvyFreeResearch.Full.UpperGlobal.Sink
