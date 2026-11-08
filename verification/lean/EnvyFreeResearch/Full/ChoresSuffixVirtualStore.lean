import EnvyFreeResearch.Full.ChoresSuffixVirtual

/-! Physical affine record lookup with a separate virtual baseline. The
virtual record is used only as a formal lower anchor; every selected record
has an actual physical endpoint and correct original-measure primary values. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix
open Set OracleProtocol IntervalOracle QueryProgram Persistent
open scoped Classical

variable {n : ℕ}

def affineVirtualEnsureProgram (bottom : Record n) (records : List (Record n))
    (i : Fin n) (target : ℝ × ℚ) : Program (Query (Fin n)) ℝ (EnsureResult n) :=
  match records with
  | [] => .failed
  | first::rest =>
    if recordLT target (first.formal i) then
      (affineInsertProgram bottom first i target).bind
        (fun fresh => .returned ⟨fresh::first::rest,fresh⟩)
    else affineEnsureProgram records i target

theorem affine_virtual_ensure_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (offset : Fin n → ℝ) (hoffset : ∀ j, 0 ≤ offset j)
    (bottom first : Record n) (rest : List (Record n)) (i : Fin n) (target : ℝ × ℚ)
    (horder : List.Pairwise Before (first::rest))
    (hsound : ∀ r ∈ first::rest, AffineSound P offset r)
    (hbound : ∀ r ∈ first::rest, r.point ∈ Icc (0 : ℝ) 1)
    (hfirst : first.point = 0) (hbefore : Before bottom first)
    (hbottom : ∀ j, (bottom.formal j).1 < 0) (htarget : 0 ≤ target.1)
    (hupper : ∃ last ∈ first::rest, recordLT target (last.formal i) ∨ last.formal i = target)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : EnsureResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (affineVirtualEnsureProgram bottom (first::rest) i target) prior result trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      List.Pairwise Before result.records ∧
      (∀ r ∈ result.records, AffineSound P offset r ∧ r.point ∈ Icc (0 : ℝ) 1) ∧
      (first::rest).Sublist result.records ∧ result.records.length ≤ (first::rest).length+1 ∧
      result.records.getLast? = (first::rest).getLast? ∧
      result.selected ∈ result.records ∧ result.selected.formal i = target ∧
      (∃ head, result.records.head? = some head ∧ head.point = 0 ∧ Before bottom head) := by
  by_cases hbelow : recordLT target (first.formal i)
  · obtain ⟨fresh,hexec,hfresh,hpoint,hlfresh,hfreshr,hcopy⟩ :=
      affine_insert_below_empty P oracle offset hoffset bottom first (hsound _ List.mem_cons_self)
        hfirst hbefore i target (hbottom i) htarget hbelow prior
    let result : EnsureResult n := ⟨fresh::first::rest,fresh⟩
    refine ⟨result,[],?_,Nat.zero_le _,by simp,?_,?_,List.Sublist.cons _ (List.Sublist.refl _),
      by simp [result],by simp [result],by simp [result],hcopy,fresh,rfl,hpoint,hlfresh⟩
    · simpa only [affineVirtualEnsureProgram,ite_eq_left hbelow,List.nil_append,List.append_nil] using
        hexec.bind (fun fresh => Program.returned (⟨fresh::first::rest,fresh⟩ : EnsureResult n))
          (Executes.returned result (prior++[]))
    · apply List.pairwise_cons.mpr
      refine ⟨?_,horder⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hfreshr
      · exact hfreshr.trans ((List.pairwise_cons.mp horder).1 r hr)
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨hfresh,by rw [hpoint]; norm_num⟩
      · exact ⟨hsound r hr,hbound r hr⟩
  · have hlower : recordLT (first.formal i) target ∨ first.formal i = target := by
      rcases record_trichotomy (first.formal i) target with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hbelow h).elim
    obtain ⟨result,trace,hexec,hlen,hcuts,hordered,hgood,hsub,hcount,hhead,hlast,hmem,hcopy⟩ :=
      affine_ensure_correct P hmono oracle hpolicy offset first rest i target horder hsound hbound
        hlower hupper prior
    refine ⟨result,trace,?_,hlen,hcuts,hordered,hgood,hsub,hcount,hlast,hmem,hcopy,
      first,hhead,hfirst,hbefore⟩
    simpa only [affineVirtualEnsureProgram,ite_eq_right hbelow] using hexec

end EnvyFreeResearch.Full.Chores.Suffix
