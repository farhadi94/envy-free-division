import EnvyFreeResearch.Full.ChoresComponentPath

/-! Donor cycle matchings for an arbitrary allowed-edge graph. Pending paid
edges need not already be edges of an executed permutation. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresDirectedMatching
open scoped Classical
variable {Agent : Type*} [DecidableEq Agent]

structure Path (r : Agent → Agent → Prop) (a b : Agent) where
  tail : List Agent
  nodup : (a :: tail).Nodup
  chain : (a :: tail).IsChain r
  last_eq : (a :: tail).getLast (List.cons_ne_nil _ _) = b

def path (r : Agent → Agent → Prop) (a b : Agent) (h : Relation.ReflTransGen r a b) :
    Path r a b :=
  let hs := Chores.Components.exists_simple_chain h
  ⟨hs.choose, hs.choose_spec.1, hs.choose_spec.2.1, hs.choose_spec.2.2⟩

def Path.vertices {r : Agent → Agent → Prop} {a b : Agent} (p : Path r a b) : List Agent := a :: p.tail

def Path.matching {r : Agent → Agent → Prop} {a b : Agent} (p : Path r a b) : Equiv.Perm Agent :=
  p.vertices.formPerm

theorem Path.matching_last {r : Agent → Agent → Prop} {a b : Agent} (p : Path r a b) :
    p.matching b = a := by
  simpa only [Path.matching, Path.vertices, p.last_eq] using List.formPerm_apply_getLast a p.tail

theorem Path.matching_other {r : Agent → Agent → Prop} {a b : Agent} (p : Path r a b)
    (x : Agent) (hx : x ≠ b) : p.matching x = x ∨ r x (p.matching x) := by
  by_cases hmem : x ∈ p.vertices
  · obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    have hnext : k + 1 < p.vertices.length := by
      by_contra hn
      have hklast : k = p.vertices.length - 1 := by omega
      have hxb : x = b := by
        rw [← p.last_eq, List.getLast_eq_getElem]
        exact hget.symm.trans (by congr 1)
      exact hx hxb
    right
    have hstep := (List.isChain_iff_getElem.mp p.chain) k hnext
    have happly := List.formPerm_apply_lt_getElem p.vertices p.nodup k hnext
    change r p.vertices[k] p.vertices[k + 1] at hstep
    rw [← happly, hget] at hstep
    exact hstep
  · exact Or.inl (List.formPerm_apply_of_notMem hmem)

def donor (r : Agent → Agent → Prop) (p j : Agent) (hjp : Relation.ReflTransGen r j p) :
    Equiv.Perm Agent := (path r j p hjp).matching

theorem donor_recipient (r : Agent → Agent → Prop) (p j : Agent)
    (hjp : Relation.ReflTransGen r j p) : donor r p j hjp p = j :=
  (path r j p hjp).matching_last

theorem donor_allowed_other (r : Agent → Agent → Prop) (hr : ∀ a, r a a) (p j : Agent)
    (hjp : Relation.ReflTransGen r j p) (a : Agent) (ha : a ≠ p) :
    r a (donor r p j hjp a) := by
  rcases (path r j p hjp).matching_other a ha with heq | hrel
  · rw [show donor r p j hjp a = a from heq]
    exact hr a
  · exact hrel

end EnvyFreeResearch.Full.RefinedChoresDirectedMatching

#print axioms EnvyFreeResearch.Full.RefinedChoresDirectedMatching.donor_allowed_other
