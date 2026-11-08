import EnvyFreeResearch.Full.UpperSnapshotSmallActualScore
import EnvyFreeResearch.Full.UpperDynamicRouting

/-! Joint Borel immutable scores, without any ordering or disjointness
hypothesis on the supplied grid and component list. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperDomainDifference UpperLogicalCells
variable {X : Type*} [MeasurableSpace X] {m : ℕ}

theorem logical_cell_membership_measurable (U : Set ℝ) (hU : MeasurableSet U)
    (cuts : X → Fin (m+2) → ℝ) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (e : Fin (m+1)) : MeasurableSet {p : X × ℝ | p.2 ∈ cell U (cuts p.1) e} := by
  have hbase : MeasurableSet {p : X × ℝ | p.2 ∈ U} := hU.preimage measurable_snd
  have hint : MeasurableSet {p : X × ℝ | p.2 ∈ U ∩ Ioc (cuts p.1 e.castSucc) (cuts p.1 e.succ)} :=
    hbase.inter ((measurableSet_lt ((hcuts e.castSucc).comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd ((hcuts e.succ).comp measurable_fst)))
  by_cases he : e=0
  · convert hint.union (hbase.inter (measurableSet_eq_fun measurable_snd ((hcuts 0).comp measurable_fst))) using 1
    ext p
    simp only [cell,ite_eq_left he,mem_union,mem_inter_iff,mem_singleton_iff,mem_setOf_eq,Function.comp_apply]
  · simpa only [cell,ite_eq_right he,union_empty] using hint

/-- Conditional-volume mass is Borel jointly in a measurable varying cell
and an endpoint-encoded component, including empty or null conditioning cells. -/
theorem conditional_component_mass_joint (cells : X → Set ℝ)
    (hcell : MeasurableSet {p : X × ℝ | p.2 ∈ cells p.1}) :
    Measurable (fun p : X × Component => mass (cond volume (cells p.1)) p.2) := by
  have hden : Measurable (fun x => (volume : Measure ℝ) (cells x)) :=
    measurable_measure_prodMk_left hcell
  have hnumset : MeasurableSet {p : (X × Component) × ℝ |
      p.2 ∈ cells p.1.1 ∩ p.1.2.carrier} := by
    apply MeasurableSet.inter
    · exact hcell.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact component_membership_measurable (fun p : (X × Component) × ℝ => p.1.2)
        (fun p => p.2) (measurable_snd.comp measurable_fst) measurable_snd
  have hnum : Measurable (fun p : X × Component => (volume : Measure ℝ) (cells p.1 ∩ p.2.carrier)) :=
    measurable_measure_prodMk_left hnumset
  convert ((hden.comp measurable_fst).inv.mul hnum).ennreal_toReal using 1
  funext p
  exact congrArg ENNReal.toReal (ProbabilityTheory.cond_apply' p.2.measurable_carrier volume)

/-- The finite score uses actual conditional-volume masses, even for
malformed grids and lists; no a.e. restriction is hidden in this theorem. -/
theorem interpolatedTotal_joint_measurable (U : Set ℝ) (hU : MeasurableSet U)
    (score : X → Fin (m+1) → ℝ) (hscore : ∀ e, Measurable (fun x => score x e))
    (cuts : X → Fin (m+2) → ℝ) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (cs : X → List Component) (hcs : Measurable cs) :
    Measurable (fun x => interpolatedTotal (score x) (cell U (cuts x)) (cs x)) := by
  unfold interpolatedTotal
  apply Finset.measurable_sum
  intro e _
  have hm : Measurable (fun p : X × Component => mass (cond volume (cell U (cuts p.1) e)) p.2) :=
    conditional_component_mass_joint (fun x => cell U (cuts x) e)
      (logical_cell_membership_measurable U hU cuts hcuts e)
  have hs := UpperDynamicRouting.sumValues_measurable
    (fun x c => mass (cond volume (cell U (cuts x) e)) c) hm cs hcs
  exact (hscore e).mul hs
end EnvyFreeResearch.Full.UpperSnapshotSmall
