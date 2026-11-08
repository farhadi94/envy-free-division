import EnvyFreeResearch.Full.ChoresSuffixStore

/-! The affine virtual-bottom boundary case. A nonnegative primary target
can be formally below physical empty only when both primary values are zero.
Its exact secondary label is inserted at that same physical empty endpoint;
no virtual interior and no new physical query are used. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix
open Set OracleProtocol IntervalOracle QueryProgram Persistent
open scoped Classical

variable {n : ℕ}

theorem affine_insert_below_empty (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (offset : Fin n → ℝ) (hoffset : ∀ j, 0 ≤ offset j)
    (bottom first : Record n) (hfirst : AffineSound P offset first) (hpoint : first.point = 0)
    (hbefore : Before bottom first) (i : Fin n) (target : ℝ × ℚ)
    (hbottom : (bottom.formal i).1 < 0) (htarget : 0 ≤ target.1)
    (hbelow : recordLT target (first.formal i)) (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh : Record n,
      Executes oracle (affineInsertProgram bottom first i target) prior fresh [] ∧
      AffineSound P offset fresh ∧ fresh.point = 0 ∧ Before bottom fresh ∧
      Before fresh first ∧ fresh.formal i = target := by
  have hfirstvalue : (first.formal i).1 = -offset i := by
    rw [hfirst i,hpoint]
    simp only [affineValue,sub_zero,sub_self,zero_sub]
  have hprimary : target.1 = (first.formal i).1 := by
    have h := recordLT_primary_le hbelow
    have hoff := hoffset i
    linarith
  have hnotbottom : ¬ target.1 = (bottom.formal i).1 := by linarith
  have hlow : recordLT (bottom.formal i) target := Or.inl (lt_of_lt_of_le hbottom htarget)
  have hbetween : ∀ j, (bottom.formal j).1 ≤ (first.formal j).1 ∧
      (first.formal j).1 ≤ (first.formal j).1 :=
    fun j => ⟨recordLT_primary_le (hbefore.2 j),le_rfl⟩
  let fresh := makeRecord bottom first i target first.point (fun j => (first.formal j).1)
  have hs := makeRecord_spec bottom first i target first.point (fun j => (first.formal j).1)
    hbefore ⟨hbefore.1,le_rfl⟩ hbetween hprimary.symm hlow hbelow
  refine ⟨fresh,?_,hfirst,hpoint,hs.1,hs.2⟩
  simpa only [affineInsertProgram,ite_eq_right hnotbottom,ite_eq_left hprimary] using
    (Executes.returned (oracle := oracle) fresh prior)

end EnvyFreeResearch.Full.Chores.Suffix
