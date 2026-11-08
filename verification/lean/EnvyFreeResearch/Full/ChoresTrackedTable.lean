import EnvyFreeResearch.Full.ChoresOriginalAtomTable
import EnvyFreeResearch.Full.ChoresClearanceProgram

/-! Immutable tracked values are computed from the original physical
snapshot caches. The index type contains every original gap and every
observer's value of every original atom, with exactly J(n²+n³) entries.
The clearance procedure never adds its own snapshots to this table. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Clearance
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Snapshot
open OriginalAtoms Equalizers
open scoped Classical

abbrev TrackedIndex (J n : ℕ) :=
  (Fin J × Fin n × Fin n) ⊕ (Fin J × Fin n × Fin n × Fin n)

theorem tracked_card (J n : ℕ) : Fintype.card (TrackedIndex J n) = J*(n^2+n^3) := by
  simp only [TrackedIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

def atomAt {n : ℕ} (table : Table n) (p a : Fin n) : Atom n :=
  (atomsFromTable table p).get (Fin.cast (atoms_from_table_length table p).symm a)

theorem atomAt_mem {n : ℕ} (table : Table n) (p a : Fin n) :
    atomAt table p a ∈ atomsFromTable table p := List.get_mem _ _

def gap {n : ℕ} (out : Output n) (i p : Fin n) : ℝ :=
  cachedValue (out.parents p) i-cachedValue (out.parents i) i

def entries {n : ℕ} (originals : List (Output n)) : TrackedIndex originals.length n → Entry n
  | .inl (s,i,p) => ⟨i,gap (originals.get s) i p⟩
  | .inr (s,p,a,i) => ⟨i,(atomAt (originals.get s).equalizers p a).values i⟩

variable {n : ℕ} {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

theorem gap_physical {U : Set ℝ} {c : Fin n} {out : Output n}
    (hsound : Sound cost U c out) (i p : Fin n) :
    gap out i p = (cost i).real (out.piece p)-(cost i).real (out.piece i) := by
  simp only [gap,Output.piece,material_value cost _ (hsound.parent_cache _).1
    (hsound.parent_cache _).2.1]

theorem gap_nonnegative {U : Set ℝ} {c : Fin n} {out : Output n}
    (hsound : Sound cost U c out) (i p : Fin n) : 0 ≤ gap out i p := by
  rw [gap_physical hsound]
  exact sub_nonneg.mpr (hsound.envy_free i p)

theorem atomAt_sound {U : Set ℝ} {c : Fin n} {out : Output n}
    (hsound : Sound cost U c out) (p a : Fin n) :
    (atomAt out.equalizers p a).Sound cost (out.piece p) := by
  obtain ⟨h,_,_,_⟩ := original_atom_table cost (domainAllocation U c out.outcome p)
    (out.parents p) (hsound.parent_cache p) out.equalizers p (baselines out.parents)
    (hsound.equalizers p) (hsound.own_equalizers p).1
  rw [hsound.piece_eq]
  exact h _ (atomAt_mem out.equalizers p a)

theorem entries_nonnegative {U : Set ℝ} {c : Fin n} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : Chain cost c U xs cache) :
    ∀ t, 0 ≤ (entries xs t).value := by
  intro t
  cases t with
  | inl t =>
    rcases t with ⟨s,i,p⟩
    obtain ⟨domain,hsound⟩ := chain.member_sound (xs.get s) (List.get_mem _ _)
    exact gap_nonnegative hsound i p
  | inr t =>
    rcases t with ⟨s,p,a,i⟩
    obtain ⟨domain,hsound⟩ := chain.member_sound (xs.get s) (List.get_mem _ _)
    change 0 ≤ (atomAt (xs.get s).equalizers p a).values i
    rw [(atomAt_sound hsound p a).2 i]
    exact measureReal_nonneg

def allProgram {n : ℕ} (originals : List (Output n)) (H : ℝ) (L : ℕ)
    (cache : List (Parent n)) : Program (Query (Fin n)) ℝ (Batch n) :=
  program (entries originals) H L (Fintype.card (TrackedIndex originals.length n))
    Finset.univ.toList cache

theorem all_program_correct (hn : 2 ≤ n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (originals : List (Output n)) (H : ℝ) (hH : 0 < H) (L : ℕ)
    (hscale : H*contraction n^L ≤ 1/H)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ batch trace, Executes oracle (allProgram originals H L cache) prior batch trace ∧
      batch.snapshots.length ≤ originals.length*(n^2+n^3)*L ∧
      trace.length ≤ originals.length*(n^2+n^3)*L*queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ originals.length*(n^2+n^3)*L*cutBudget n ∧
      AnyChain cost U batch.snapshots batch.residue ∧
      Separated (entries originals) cost H (material batch.residue) := by
  have h := program_correct hn cost oracle hpolicy (entries originals) H hH L hscale
    (Fintype.card (TrackedIndex originals.length n)) Finset.univ.toList (by simp)
    U cache hc (fun t ht => (ht (by simp)).elim) prior
  simpa only [allProgram,tracked_card] using h

theorem separated_gap {xs : List (Output n)} {H : ℝ} {R : Set ℝ}
    (h : Separated (entries xs) cost H R) (s : Fin xs.length) (i p : Fin n) :
    gap (xs.get s) i p ≤ (cost i).real R/H ∨ H*(cost i).real R ≤ gap (xs.get s) i p :=
  h (.inl (s,i,p))

theorem separated_atom {xs : List (Output n)} {H : ℝ} {R : Set ℝ}
    (h : Separated (entries xs) cost H R) (s : Fin xs.length) (p a i : Fin n) :
    (atomAt (xs.get s).equalizers p a).values i ≤ (cost i).real R/H ∨
      H*(cost i).real R ≤ (atomAt (xs.get s).equalizers p a).values i := h (.inr (s,p,a,i))

end EnvyFreeResearch.Full.Chores.Clearance
