import EnvyFreeResearch.Full.ChoresFrontierOutcome
import EnvyFreeResearch.Full.ChoresFrontierParts

/-! Correctness of the concrete zero-query scan on actual original
measures. Its three outcomes derive the hypotheses needed by physical
compensation, including whole offered suffix costs rather than only
incremental extraction costs. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers
open scoped Classical

variable {n : ℕ} (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
  (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
  (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
  (hown : (table (p,p)).parts.prefixParts=cache)
  (r : Fin n → ℝ) (H : ℝ) (hr : ∀ i, 0 < r i) (hH : 1 < H)
  (hscale : (n : ℝ) < H*H)
  (hatoms : AtomSeparated (weight table p) r H)
  (hgaps : GapSeparated (weight table p) (rankOf table p) r H)
  (C : Finset (Fin n))

include hc hcorrect hown hr hH hscale hatoms hgaps

theorem physical_atomic (s : Stop n)
    (hstop : s.Valid (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C)
    (a : Fin n) (hscan : largestBad (weight table p) r H (rankOf table p s.agent)=some a) :
    PhysicalCorrect cost P cache table p baseline r H C (.atomic a) := by
  obtain ⟨hownA,hAC,hnotA,hBn,hnotB,hpart,hprotect,hlarge,hsmall⟩ :=
    atomic_scan_spec (weight table p) (rankOf table p) r H
      (weight_nonnegative cost P cache hc table p baseline hcorrect hown) hr hH hscale
      hatoms hgaps p (rank_owner table p) C s hstop a hscan
  dsimp only [PhysicalCorrect]
  refine ⟨hownA,hAC,?_,hBn,?_,?_,?_,?_,?_,?_,?_⟩
  · intro h
    exact hnotA (h ▸ Finset.mem_univ _)
  · intro h
    exact hnotB (h ▸ Finset.mem_univ _)
  · exact original_atom_in_suffix cost P cache hc table p baseline hcorrect hown a
  · intro i hi
    rw [← gap_is_tail cost P cache hc table p baseline hcorrect hown i,
      offer_value cost P cache hc table p baseline hcorrect hown]
    exact hpart i hi
  · intro i hi
    rw [← gap_is_tail cost P cache hc table p baseline hcorrect hown i,
      offer_value cost P cache hc table p baseline hcorrect hown]
    exact hprotect i hi
  · intro i hi
    obtain ⟨hs,_,_,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
    have hv := (hs _ (List.get_mem _ (Fin.cast (atoms_from_table_length table p).symm a))).2 i
    rw [← hv]
    exact hlarge i hi
  · intro i hi
    rw [offer_value cost P cache hc table p baseline hcorrect hown]
    exact hsmall i hi
  · exact (largestBad_some (weight table p) r H _ a hscan).2.2

omit hatoms in
theorem physical_outside (q : Fin n)
    (hstop : (Stop.outside q).Valid (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C)
    (hscan : largestBad (weight table p) r H (rankOf table p q)=none) :
    PhysicalCorrect cost P cache table p baseline r H C (.outside q) := by
  have hHpos : 0 < H := by linarith
  have hsmall := largestBad_none (weight table p) r H _ hscan
  dsimp only [PhysicalCorrect]
  refine ⟨(Finset.mem_sdiff.mp hstop.1).1,(Finset.mem_sdiff.mp hstop.1).2,hsmall,?_,?_⟩
  · intro i hi
    rw [← gap_is_tail cost P cache hc table p baseline hcorrect hown i,
      offer_value cost P cache hc table p baseline hcorrect hown]
    exact outside_small_protection (weight table p) (rankOf table p) r H
      (weight_nonnegative cost P cache hc table p baseline hcorrect hown) hr hHpos hscale hgaps C q hstop hsmall i hi
  · intro i
    rw [offer_value cost P cache hc table p baseline hcorrect hown]
    exact tail_small (weight table p) i (rankOf table p q) (r i) H (hr i).le hHpos
      (fun a ha => hsmall a ha i)

omit hatoms in
theorem physical_exhausted (q : Fin n)
    (hstop : (Stop.exhausted q).Valid (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C)
    (hscan : largestBad (weight table p) r H (rankOf table p q)=none) :
    PhysicalCorrect cost P cache table p baseline r H C (.exhausted q) := by
  have hHpos : 0 < H := by linarith
  have hsmall := largestBad_none (weight table p) r H _ hscan
  dsimp only [PhysicalCorrect]
  refine ⟨hstop.2.1,hsmall,?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [← gap_is_tail cost P cache hc table p baseline hcorrect hown i,
      offer_value cost P cache hc table p baseline hcorrect hown]
    exact exhausted_participant (weight table p) (rankOf table p) r H
      (weight_nonnegative cost P cache hc table p baseline hcorrect hown) C q hstop i hi
  · intro i hi
    rw [← gap_is_tail cost P cache hc table p baseline hcorrect hown i,
      offer_value cost P cache hc table p baseline hcorrect hown]
    exact exhausted_outside_protection (weight table p) (rankOf table p) r H
      (weight_nonnegative cost P cache hc table p baseline hcorrect hown) hr hHpos hscale hgaps q hsmall i hi
  · intro i hi
    rw [← gap_is_tail cost P cache hc table p baseline hcorrect hown i]
    exact omitted_gap_large (weight table p) (rankOf table p) r H hgaps i hi
  · intro i
    rw [offer_value cost P cache hc table p baseline hcorrect hown]
    exact tail_small (weight table p) i (rankOf table p q) (r i) H (hr i).le hHpos (fun a ha => hsmall a ha i)
  · intro i hi
    rw [← gap_is_tail cost P cache hc table p baseline hcorrect hown i,
      offer_value cost P cache hc table p baseline hcorrect hown]
    exact exhausted_deviation (weight table p) (rankOf table p) r H hr hHpos hgaps q hsmall i hi

theorem scan_correct :
    PhysicalCorrect cost P cache table p baseline r H C (scan table p r H C) := by
  let s := stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p
  have hE := owner_eligible (weight table p) (rankOf table p) r H p (rank_owner table p) (hr p).le (by linarith)
  change PhysicalCorrect cost P cache table p baseline r H C
    (match largestBad (weight table p) r H (rankOf table p s.agent) with
      | some a => .atomic a
      | none => match s with
        | .outside q => .outside q
        | .exhausted q => .exhausted q)
  have hs : s.Valid (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C :=
    stop_valid _ _ _ p hE
  cases hb : largestBad (weight table p) r H (rankOf table p s.agent) with
  | some a =>
    exact physical_atomic cost P cache hc table p baseline hcorrect hown r H hr hH hscale hatoms hgaps C s hs a hb
  | none =>
    cases hsdef : s with
    | outside q =>
      rw [hsdef] at hs hb
      exact physical_outside cost P cache hc table p baseline hcorrect hown r H hr hH hscale hgaps C q hs hb
    | exhausted q =>
      rw [hsdef] at hs hb
      exact physical_exhausted cost P cache hc table p baseline hcorrect hown r H hr hH hscale hgaps C q hs hb

end EnvyFreeResearch.Full.Chores.Frontier
