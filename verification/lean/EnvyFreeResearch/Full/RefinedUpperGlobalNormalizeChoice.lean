import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeZero

noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
variable {n : ℕ}

theorem singleton_pick (fallback : Fin n) (s : Finset (Fin n))
    (hn : s.Nonempty) (hc : s.card ≤ 1) : s = {pick fallback s} := by
  have hs : ({pick fallback s} : Finset (Fin n)) ⊆ s := by
    intro x hx
    have he : x = pick fallback s := by simpa using hx
    exact he ▸ pick_mem fallback s hn
  exact (Finset.eq_of_subset_of_card_le hs (by simpa using hc)).symm

def second (fallback : Fin n) (s : Finset (Fin n)) : Fin n := pick fallback (s.erase (pick fallback s))

theorem two_pick (fallback : Fin n) (s : Finset (Fin n)) (hc : s.card = 2) :
    s = {pick fallback s,second fallback s} ∧ second fallback s ≠ pick fallback s := by
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  have hm := pick_mem fallback s hn
  have hecard := Finset.card_erase_of_mem hm
  have hen : (s.erase (pick fallback s)).Nonempty := Finset.card_pos.mp (by omega)
  have hs := pick_mem fallback _ hen
  have hsm : second fallback s ∈ s := (Finset.mem_erase.mp hs).2
  have hne : second fallback s ≠ pick fallback s := (Finset.mem_erase.mp hs).1
  refine ⟨?_,hne⟩
  have hsub : ({pick fallback s,second fallback s} : Finset (Fin n)) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hm
    · have he : x = second fallback s := by simpa using hx
      exact he ▸ hsm
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hc]
  simp [hne,Ne.symm hne]

end EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
