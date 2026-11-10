import EnvyFreeResearch.Full.RefinedUpperStabilityAdjacent

/-! Sorted tuple deletion instantiated in actual consecutive interval lists. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperSortedGrid UpperGridInterpolation
open scoped Classical

lemma ofFn_removeNth {A : Type*} {n : ℕ} (points : Fin (n+1) → A) (p : Fin (n+1)) :
    List.ofFn (p.removeNth points) = (List.ofFn points).eraseIdx p.val := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx,p.isLt]
  · intro j hj hj'
    rw [List.getElem_ofFn,List.getElem_eraseIdx]
    simp only [Fin.removeNth,Fin.succAbove,Fin.lt_def,Fin.val_castSucc]
    split_ifs <;> simp only [List.getElem_ofFn] <;> rfl

/-- Split a monotone tuple around one interior coordinate. The two lists
are computed from the actual tuple and its actual `removeNth` deletion. -/
theorem tuple_local_decomposition {m : ℕ} (points : Fin (m+2) → ℝ) (hp : Monotone points)
    (p : Fin m) :
    ∃ before after,
      List.ofFn points = before++points p.castSucc.castSucc::points p.succ.castSucc::points p.succ.succ::after ∧
      List.ofFn (p.succ.castSucc.removeNth points) =
        before++points p.castSucc.castSucc::points p.succ.succ::after ∧
      (∀ x ∈ before, x ≤ points p.castSucc.castSucc) ∧
      (∀ x ∈ after, points p.succ.succ ≤ x) := by
  let all := List.ofFn points
  let before := all.take p.val
  let after := all.drop (p.val+3)
  have hlen : all.length = m+2 := List.length_ofFn
  have hsplit : all = before++points p.castSucc.castSucc::points p.succ.castSucc::points p.succ.succ::after := by
    have h0 : p.val < all.length := by rw [hlen]; omega
    have h1 : p.val+1 < all.length := by rw [hlen]; omega
    have h2 : p.val+2 < all.length := by rw [hlen]; omega
    calc
      all = all.take p.val ++ all.drop p.val := (List.take_append_drop _ _).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons h0,List.drop_eq_getElem_cons h1,List.drop_eq_getElem_cons h2]
        simp only [all,List.getElem_ofFn]
        rfl
  refine ⟨before,after,hsplit,?_,?_,?_⟩
  · rw [ofFn_removeNth]
    change all.eraseIdx (p.val+1) = _
    rw [hsplit,List.eraseIdx_append_of_length_le]
    · have hb : before.length = p.val := by simp [before,hlen]; omega
      simp [hb]
    · have hb : before.length = p.val := by simp [before,hlen]; omega
      omega
  · intro x hx
    obtain ⟨j,hj,he⟩ := List.mem_take_iff_getElem.mp hx
    have hjm : j < m+2 := by omega
    rw [show x = points ⟨j,hjm⟩ from by simpa only [all,List.getElem_ofFn] using he.symm]
    exact hp (by simp only [Fin.le_def,Fin.val_castSucc]; omega)
  · intro x hx
    obtain ⟨j,hj,he⟩ := List.mem_drop_iff_getElem.mp hx
    have hjm : p.val+3+j < m+2 := by change j+(p.val+3) < all.length at hj; rw [hlen] at hj; omega
    rw [show x = points ⟨p.val+3+j,hjm⟩ from by simpa only [all,List.getElem_ofFn] using he.symm]
    exact hp (by simp only [Fin.le_def,Fin.val_succ]; omega)

/-- Actual sorting followed by deleting an interior raw sample gives the
physical local-edit identity used by the peeling stability theorem. -/
theorem sorted_interval_delete_filter {m : ℕ} (values : Fin (m+2) → ℝ)
    (raw : Fin (m+2)) (p : Fin m)
    (hrank : (UpperSortedGrid.select values).symm raw = p.succ.castSucc)
    (hunique : ∀ j, sorted values j = sorted values p.succ.castSucc → j = p.succ.castSucc) :
    (List.ofFn (intervalLabel (sorted values))).filter
        (fun c => c.1 ≠ values raw ∧ c.2 ≠ values raw) =
      (List.ofFn (fun i : Fin m => (sorted (raw.removeNth values) i.castSucc, sorted (raw.removeNth values) i.succ))).filter
        (fun c => c ≠ (sorted values p.castSucc.castSucc,sorted values p.succ.succ)) := by
  have hraw : values raw = sorted values p.succ.castSucc := by
    rw [← hrank]
    simp [UpperSortedGrid.sorted]
  have hleft : sorted values p.castSucc.castSucc < sorted values p.succ.castSucc := by
    have hle := sorted_monotone values (show p.castSucc.castSucc ≤ p.succ.castSucc from by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    by_contra hn
    have heq := le_antisymm hle (le_of_not_gt hn)
    have hi := congrArg Fin.val (hunique p.castSucc.castSucc heq)
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  have hright : sorted values p.succ.castSucc < sorted values p.succ.succ := by
    have hle := sorted_monotone values (show p.succ.castSucc ≤ p.succ.succ from by
      simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
    by_contra hn
    have heq := le_antisymm hle (le_of_not_gt hn)
    have hi := congrArg Fin.val (hunique p.succ.succ heq.symm)
    simp only [Fin.val_castSucc,Fin.val_succ] at hi
    omega
  obtain ⟨before,after,hsplit,hmerge,hbefore,hafter⟩ :=
    tuple_local_decomposition (sorted values) (sorted_monotone values) p
  change (List.ofFn (fun i => (sorted values i.castSucc,sorted values i.succ))).filter _ =
    (List.ofFn (fun i => (sorted (raw.removeNth values) i.castSucc,sorted (raw.removeNth values) i.succ))).filter _
  rw [← edges_ofFn,← edges_ofFn,sorted_removeNth,hrank,hsplit,hmerge,hraw]
  exact edges_local_filter before after _ _ _ hleft hright hbefore hafter

end EnvyFreeResearch.Full.RefinedUpperPeeling
