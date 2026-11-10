import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferPath

/-! Ordinary directed reachability supplies the finite simple paths used
by transfer. Repeated vertices are removed without reversing any edge. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
open scoped Classical

theorem simple_list_of_reachable {k : ℕ} {E : Fin k → Fin k → Prop} {a b : Fin k}
    (h : Relation.ReflTransGen E a b) :
    ∃ tail : List (Fin k), (a::tail).Nodup ∧ (a::tail).IsChain E ∧
      (a::tail).getLast (by simp)=b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[],by simp,List.IsChain.singleton _,rfl⟩
  | @head c d hcd hdb ih =>
    obtain ⟨tail,hn,hchain,hlast⟩ := ih
    by_cases hm : c ∈ d::tail
    · obtain ⟨pre,post,heq⟩ := List.mem_iff_append.mp hm
      have hn' : (pre++c::post).Nodup := heq ▸ hn
      have hc' : (pre++c::post).IsChain E := heq ▸ hchain
      have hl' : (pre++c::post).getLast (by simp)=b := by simpa only [← heq] using hlast
      refine ⟨post,(List.nodup_append.mp hn').2.1,hc'.right_of_append,?_⟩
      simpa using hl'
    · exact ⟨d::tail,List.nodup_cons.mpr ⟨hm,hn⟩,.cons_cons hcd hchain,by simpa using hlast⟩

def SimplePath.ofReachable {k : ℕ} {E : Fin k → Fin k → Prop} {a b : Fin k}
    (h : Relation.ReflTransGen E a b) : SimplePath E a b := by
  let tail := (simple_list_of_reachable h).choose
  have hn := (simple_list_of_reachable h).choose_spec.1
  have hchain := (simple_list_of_reachable h).choose_spec.2.1
  have hlast := (simple_list_of_reachable h).choose_spec.2.2
  refine ⟨tail.length,(a::tail).get,hn.injective_get,?_,?_,?_⟩
  · rfl
  · simpa only [List.get_eq_getElem,Fin.val_last,List.getElem_cons_length] using hlast
  · intro i
    exact (List.isChain_iff_getElem.mp hchain) i.val (by change i.val+1 < tail.length+1; exact Nat.succ_lt_succ i.isLt)

end EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
