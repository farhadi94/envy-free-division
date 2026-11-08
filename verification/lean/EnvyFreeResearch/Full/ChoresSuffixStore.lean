import EnvyFreeResearch.Full.ChoresSuffixInsertion

/-! A concrete immutable affine suffix-record table. Repeated targets reuse
the exact earlier record; new targets insert into the actual adjacent formal
bracket. All old records, including unused trials, survive unchanged. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix
open Set OracleProtocol IntervalOracle QueryProgram InitialPartition Persistent
open scoped Classical

variable {n : ℕ}

def affineEnsureProgram (records : List (Record n)) (i : Fin n) (target : ℝ × ℚ) :
    Program (Query (Fin n)) ℝ (EnsureResult n) :=
  match locate i target records with
  | .failed => .failed
  | .reused r => .returned ⟨records,r⟩
  | .bracket pre left right post => (affineInsertProgram left right i target).bind
      (fun fresh => .returned ⟨pre ++ left :: fresh :: right :: post,fresh⟩)

theorem affine_ensure_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (offset : Fin n → ℝ) (first : Record n) (rest : List (Record n)) (i : Fin n) (target : ℝ × ℚ)
    (horder : List.Pairwise Before (first::rest))
    (hsound : ∀ r ∈ first::rest, AffineSound P offset r)
    (hbound : ∀ r ∈ first::rest, r.point ∈ Icc (0 : ℝ) 1)
    (hlower : recordLT (first.formal i) target ∨ first.formal i = target)
    (hupper : ∃ last ∈ first::rest, recordLT target (last.formal i) ∨ last.formal i = target)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : EnsureResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (affineEnsureProgram (first::rest) i target) prior result trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      List.Pairwise Before result.records ∧
      (∀ r ∈ result.records, AffineSound P offset r ∧ r.point ∈ Icc (0 : ℝ) 1) ∧
      (first::rest).Sublist result.records ∧ result.records.length ≤ (first::rest).length+1 ∧
      result.records.head? = (first::rest).head? ∧ result.records.getLast? = (first::rest).getLast? ∧
      result.selected ∈ result.records ∧ result.selected.formal i = target := by
  have hsuccess := locate_success i target first rest hlower hupper
  have hvalid := locate_valid i target (first::rest)
  cases hloc : locate i target (first::rest) with
  | failed => exact (hsuccess hloc).elim
  | reused r =>
    rw [hloc] at hvalid
    let result : EnsureResult n := ⟨first::rest,r⟩
    refine ⟨result,[],?_,Nat.zero_le _,by simp,horder,
      fun s hs => ⟨hsound s hs,hbound s hs⟩,List.Sublist.refl _,Nat.le_add_right _ _,
      rfl,rfl,hvalid.1,hvalid.2⟩
    simpa only [affineEnsureProgram,hloc] using (Executes.returned (oracle := oracle) result prior)
  | bracket pre left right post =>
    rw [hloc] at hvalid
    obtain ⟨hdecomp,hlt,hrt⟩ := hvalid
    have hleftmem : left ∈ first::rest := by rw [hdecomp]; simp
    have hrightmem : right ∈ first::rest := by rw [hdecomp]; simp
    have horder' : List.Pairwise Before (pre ++ left::right::post) := hdecomp ▸ horder
    have hbefore : Before left right :=
      (List.pairwise_cons.mp (List.pairwise_append.mp horder').2.1).1 right List.mem_cons_self
    obtain ⟨fresh,trace,hexec,hlen,hcuts,hfresh,hlfresh,hfreshr,hcopy⟩ :=
      affine_insert_correct P hmono oracle hpolicy offset left right i target
        (hsound _ hleftmem) (hsound _ hrightmem) hbefore
        (hbound _ hleftmem).1 (hbound _ hrightmem).2 hlt hrt prior
    let result : EnsureResult n := ⟨pre ++ left::fresh::right::post,fresh⟩
    refine ⟨result,trace,?_,hlen,hcuts,
      pairwise_insert_between Before (fun h h' => h.trans h') pre post left right fresh
        horder' hlfresh hfreshr,?_,?_,?_,?_,?_,?_,hcopy⟩
    · simpa only [affineEnsureProgram,hloc,List.append_nil] using hexec.bind
        (fun fresh => Program.returned (⟨pre ++ left::fresh::right::post,fresh⟩ : EnsureResult n))
        (Executes.returned result (prior++trace))
    · intro r hr
      rcases inserted_members pre post left right fresh r hr with rfl | hr
      · exact ⟨hfresh,(hbound _ hleftmem).1.trans hlfresh.1,hfreshr.1.trans (hbound _ hrightmem).2⟩
      · exact ⟨hsound r (hdecomp ▸ hr),hbound r (hdecomp ▸ hr)⟩
    · rw [hdecomp]
      exact old_records_sublist pre post left right fresh
    · change (pre ++ left::fresh::right::post).length ≤ (first::rest).length+1
      rw [hdecomp]
      simp only [List.length_append,List.length_cons]
      omega
    · change (pre ++ left::fresh::right::post).head? = (first::rest).head?
      rw [hdecomp]
      exact insert_head_preserved pre post left right fresh
    · change (pre ++ left::fresh::right::post).getLast? = (first::rest).getLast?
      rw [hdecomp]
      exact insert_last_preserved pre post left right fresh
    · simp [result]

end EnvyFreeResearch.Full.Chores.Suffix
