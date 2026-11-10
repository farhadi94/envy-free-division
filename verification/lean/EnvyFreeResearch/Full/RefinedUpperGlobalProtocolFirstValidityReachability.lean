import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionFirst
import EnvyFreeResearch.Full.RefinedUpperGlobalSinkGraph

noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperZeroRows GlobalCompletion
variable {n : ℕ}

theorem localGraph_reachable (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (direction : Direction) (hs : RefinedUpperGlobal.Sink.StrongOn (p.anchor.edge direction) p.anchor.active) :
    ∀ i j, Relation.ReflTransGen (fun a b => p.localGraph direction a b=true) i j := by
  have hmap : p.anchor.edge direction ≤
      (fun i j => p.localGraph direction (activeIndex p.anchor.active i) (activeIndex p.anchor.active j)=true) := by
    intro i j he
    apply (localGraph_iff p direction _ _).mpr
    simpa only [enumerate_activeIndex _ _ he.1,enumerate_activeIndex _ _ he.2.1] using he
  intro i j
  have h := Relation.ReflTransGen.lift (p := fun a b => p.localGraph direction a b=true) (activeIndex p.anchor.active) hmap _ _
    (hs _ (enumerate_mem _ i) _ (enumerate_mem _ j))
  simpa only [Function.onFun,activeIndex_apply] using h

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
