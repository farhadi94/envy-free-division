import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableScore

/-! Joint Borel physical-domain membership and interpolation for a varying
recorded origin. No valid-cut or disjoint-component hypothesis is required. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperSnapshotSmall
variable {X : Type*} [MeasurableSpace X] {m : ℕ}

theorem domain_fold_membership (cs : List Component) (x : ℝ) (b : Bool) :
    cs.foldl (fun acc c => acc || decide (x ∈ c.carrier)) b = (b || decide (x ∈ domain cs)) := by
  induction cs generalizing b with
  | nil => simp [domain]
  | cons c cs ih => simpa [domain,Bool.or_assoc] using ih (b || decide (x ∈ c.carrier))

theorem recorded_domain_membership_measurable (cs : X → List Component) (hcs : Measurable cs) :
    MeasurableSet {p : X × ℝ | p.2 ∈ domain (cs p.1)} := by
  have hstep : Measurable (fun p : (X × ℝ) × Bool × Component =>
      p.2.1 || decide (p.1.2 ∈ p.2.2.carrier)) :=
    (measurable_of_countable (fun p : Bool × Bool => p.1 || p.2)).comp
      ((measurable_fst.comp measurable_snd).prodMk
        (decide_measurable _ (component_membership_measurable (fun p : (X × ℝ) × Bool × Component => p.2.2) (fun p => p.1.2)
          (measurable_snd.comp measurable_snd) (measurable_snd.comp measurable_fst))))
  have hm := list_foldl_measurable (fun p : X × ℝ => fun acc c => acc || decide (p.2 ∈ c.carrier))
    (fun _ => false) (fun p => cs p.1) hstep measurable_const (hcs.comp measurable_fst)
  have hd : Measurable (fun p : X × ℝ => decide (p.2 ∈ domain (cs p.1))) := by
    simpa only [domain_fold_membership,Bool.false_or] using hm
  simpa only [decide_eq_true_eq] using measurableSet_eq_fun hd (show Measurable (fun _ : X × ℝ => true) from measurable_const)

theorem varying_cell_membership_measurable (U : X → Set ℝ)
    (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1})
    (cuts : X → Fin (m+2) → ℝ) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (e : Fin (m+1)) : MeasurableSet {p : X × ℝ | p.2 ∈ cell (U p.1) (cuts p.1) e} := by
  have hint : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1 ∩ Ioc (cuts p.1 e.castSucc) (cuts p.1 e.succ)} :=
    hU.inter ((measurableSet_lt ((hcuts e.castSucc).comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd ((hcuts e.succ).comp measurable_fst)))
  by_cases he : e=0
  · convert hint.union (hU.inter (measurableSet_eq_fun measurable_snd ((hcuts 0).comp measurable_fst))) using 1
    ext p
    simp only [cell,ite_eq_left he,mem_union,mem_inter_iff,mem_singleton_iff,mem_ofPred_eq,Function.comp_apply]
  · simpa only [cell,ite_eq_right he,union_empty] using hint

theorem varying_interpolatedTotal_measurable (U : X → Set ℝ)
    (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1})
    (score : X → Fin (m+1) → ℝ) (hscore : ∀ e, Measurable (fun x => score x e))
    (cuts : X → Fin (m+2) → ℝ) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (cs : X → List Component) (hcs : Measurable cs) :
    Measurable (fun x => interpolatedTotal (score x) (cell (U x) (cuts x)) (cs x)) := by
  unfold interpolatedTotal
  apply Finset.measurable_sum
  intro e _
  have hm : Measurable (fun p : X × Component => mass (ProbabilityTheory.cond volume (cell (U p.1) (cuts p.1) e)) p.2) :=
    conditional_component_mass_joint (fun x => cell (U x) (cuts x) e)
      (varying_cell_membership_measurable U hU cuts hcuts e)
  exact (hscore e).mul (UpperDynamicRouting.sumValues_measurable _ hm cs hcs)
end EnvyFreeResearch.Full.UpperSnapshotProtocol
