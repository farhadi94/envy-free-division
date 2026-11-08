import EnvyFreeResearch.Full.ChoresSubCorePhysicalTrims
import EnvyFreeResearch.Full.ChoresSuffixInitial
import EnvyFreeResearch.Full.ChoresMaskedTag

/-! Concrete clipped suffix leaves for the physical SubCore driver.
The invariant records actual parent-profile soundness, physical coordinates,
the immutable initial rows and the common empty formal head. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCoreLeaves
open Set OracleProtocol IntervalOracle QueryProgram Persistent Suffix SubCorePhysical
open scoped Classical

variable {n : ℕ} {Root : Type*}

def clippedInitial (offset total : Root → Fin n → ℝ) : Store Root (ClippedRecord n) :=
  fun p => [clippedEmpty (offset p),clippedWhole (offset p) (total p)]

def clippedBaseline (_i : Fin n) : Lex (ℝ × ℚ) := toLex (0,0)

abbrev clippedValidity (P : Root → Profile (Fin n)) (offset total : Root → Fin n → ℝ) :
    RecordValidity Root (ClippedRecord n) where
  valid := fun p r => ClippedSound (P p) (offset p) r ∧ r.record.point ∈ Icc (0 : ℝ) 1
  storeValid := fun store => ∀ p,
    (store p).head? = some (clippedEmpty (offset p)) ∧
    (clippedInitial offset total p).Sublist (store p)

theorem pair_lower_of_lex_le (a b : ℝ × ℚ) (h : toLex a ≤ toLex b) :
    recordLT a b ∨ a = b := by
  rcases lt_or_eq_of_le h with h | h
  · exact Or.inl (Prod.Lex.toLex_lt_toLex.mp h)
  · exact Or.inr (congrArg ofLex h)

theorem pair_upper_of_lex_le (a b : ℝ × ℚ) (h : toLex a ≤ toLex b) :
    recordLT a b ∨ b = a := by
  rcases pair_lower_of_lex_le a b h with h | h
  · exact Or.inl h
  · exact Or.inr h.symm

theorem clipped_rows_lower (offset : Fin n → ℝ) (hoffset : ∀ i, 0 ≤ offset i)
    (records : List (ClippedRecord n)) (hhead : records.head? = some (clippedEmpty offset))
    (horder : records.Pairwise (fun r s => Before r.record s.record)) :
    ∀ r ∈ records, ∀ i, clippedBaseline i ≤ toLex (r.record.formal i) := by
  cases records with
  | nil => simp at hhead
  | cons first rest =>
    have heq : first = clippedEmpty offset := Option.some.inj hhead
    subst first
    intro r hr i
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [clipped_empty_formal offset hoffset]
      exact le_rfl
    · have h := (List.pairwise_cons.mp horder).1 r hr
      have ht := Prod.Lex.toLex_lt_toLex.mpr (h.2 i)
      rw [clipped_empty_formal offset hoffset] at ht
      exact ht.le

theorem clipped_initial_wellFormed (P : Root → Profile (Fin n))
    (offset total : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (htotal : ∀ p i, total p i = (P p).cumulative i 1) :
    letI := clippedValidity P offset total
    WellFormed ClippedRecord.record clippedBaseline (clippedInitial offset total) := by
  letI := clippedValidity P offset total
  have horder (p : Root) : (clippedInitial offset total p).Pairwise
      (fun r s => Before r.record s.record) := by
    simpa [clippedInitial] using clipped_initial_before (offset p) (total p) (hoffset p)
  refine ⟨horder,?_,?_,?_⟩
  · intro p
    exact clipped_rows_lower (offset p) (hoffset p) _ rfl (horder p)
  · intro p r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨clipped_empty_sound (P p) (offset p),by norm_num [clippedEmpty]⟩
    · have heq := List.mem_singleton.mp hr
      subst r
      exact ⟨clipped_whole_sound (P p) (offset p) (total p) (htotal p),by norm_num [clippedWhole]⟩
  · intro p
    exact ⟨rfl,List.Sublist.refl _⟩

def clippedEnsure (p : Root) (i : Fin n) (target : ℝ × ℚ) (records : List (ClippedRecord n)) :
    Program (Masked.TaggedQuery Root n) ℝ (Lookup.Result (ClippedRecord n)) :=
  Masked.tagProgram p (clippedEnsureProgram records i target)

theorem clipped_whole_stored (P : Root → Profile (Fin n))
    (offset total : Root → Fin n → ℝ) (store : Store Root (ClippedRecord n)) (p : Root) :
    letI := clippedValidity P offset total
    WellFormed ClippedRecord.record clippedBaseline store →
      Stored ClippedRecord.record store p (orderedRecord (clippedWhole (offset p) (total p)).record) := by
  letI := clippedValidity P offset total
  intro hs
  exact ⟨clippedWhole (offset p) (total p),
    (hs.store_valid p).2.subset (by simp [clippedInitial]),rfl⟩

def ClippedResultGood (P : Profile (Fin n)) (offset : Fin n → ℝ)
    (records : List (ClippedRecord n)) (i : Fin n) (target : ℝ × ℚ)
    (out : Lookup.Result (ClippedRecord n)) : Prop :=
  out.records.Pairwise (fun r s => Before r.record s.record) ∧
  (∀ r ∈ out.records, ClippedSound P offset r ∧ r.record.point ∈ Icc (0 : ℝ) 1) ∧
  records.Sublist out.records ∧ out.records.head? = records.head? ∧
  out.selected ∈ out.records ∧ out.selected.record.formal i = target

theorem clipped_records_targets (P : Root → Profile (Fin n))
    (hmono : ∀ p i, Monotone ((P p).cumulative i))
    (offset total : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ)
    (hpolicy : Masked.IsLegalPolicy P oracle) :
    letI := clippedValidity P offset total
    RecordsTargets ClippedRecord.record clippedEnsure clippedBaseline oracle
      (fun q => isCutQuery q.2) n := by
  letI := clippedValidity P offset total
  intro store hstore p i target cap hcap hlower _hnonneg hupper prior
  have hhead : (store p).head? = some (clippedEmpty (offset p)) := (hstore.store_valid p).1
  have hinitial : (clippedInitial offset total p).Sublist (store p) := (hstore.store_valid p).2
  obtain ⟨capPayload,hcapMem,hcapView⟩ := hcap
  have hupper' : toLex (ofLex target) ≤ toLex (capPayload.record.formal i) := by
    change target ≤ toLex (cap.record.formal i) at hupper
    rw [← hcapView] at hupper
    exact hupper
  have hexists : ∃ first rest, store p = first::rest := by
    cases he : store p with
    | nil => simp [he] at hhead
    | cons first rest => exact ⟨first,rest,rfl⟩
  obtain ⟨first,rest,hlist⟩ := hexists
  have hfirst : first = clippedEmpty (offset p) := by
    rw [hlist] at hhead
    exact Option.some.inj hhead
  have hlow : recordLT (first.record.formal i) (ofLex target) ∨ first.record.formal i = ofLex target := by
    apply pair_lower_of_lex_le
    rw [hfirst,clipped_empty_formal (offset p) (hoffset p)]
    exact hlower
  have htop : ∃ last ∈ first::rest,
      recordLT (ofLex target) (last.record.formal i) ∨ last.record.formal i = ofLex target :=
    ⟨capPayload,hlist ▸ hcapMem,pair_upper_of_lex_le _ _ hupper'⟩
  have hsource : ∀ policy, AdaptiveOracle.IsLegalPolicy (P p) policy →
      ∃ result trace, Executes policy (clippedEnsureProgram (store p) i (ofLex target)) [] result trace ∧
        ClippedResultGood (P p) (offset p) (store p) i (ofLex target) result ∧
        trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 := by
    intro policy hlegal
    obtain ⟨out,trace,hexec,hQ,hC,horder,hgood,hsub,_hsize,hh,_hlast,hs,ht⟩ :=
      clipped_ensure_correct (P p) (hmono p) policy hlegal (offset p) first rest i (ofLex target)
        (hlist ▸ hstore.ordered p)
        (fun r hr => (hstore.valid p r (hlist.symm ▸ hr)).1)
        (fun r hr => (hstore.valid p r (hlist.symm ▸ hr)).2) hlow htop []
    refine ⟨out,trace,?_,?_,hQ,hC⟩
    · simpa only [hlist] using hexec
    · exact ⟨horder,hgood,hlist.symm ▸ hsub,hh.trans (congrArg List.head? hlist).symm,hs,ht⟩
  obtain ⟨out,trace,hexec,hgood,hQ,hC⟩ := Masked.tag_correct P oracle hpolicy prior p
    (clippedEnsureProgram (store p) i (ofLex target))
    (ClippedResultGood (P p) (offset p) (store p) i (ofLex target)) n 1 hsource
  obtain ⟨horder,hvalid,hsub,hheadOut,hselected,hcopy⟩ := hgood
  have hleaf : Executes oracle (clippedEnsure p i (ofLex target) (store p)) prior out trace := hexec
  obtain ⟨hglobal,hext,hrecord,htarget⟩ := ensure_global_executes ClippedRecord.record clippedEnsure
    oracle store p i target out prior trace hleaf hsub hselected hcopy
  refine ⟨⟨Function.update store p out.records,orderedRecord out.selected.record⟩,trace,
    hglobal,?_,hext,hrecord,htarget,hQ,hC⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro q
    by_cases hq : q = p
    · subst q
      simpa only [Function.update_self] using horder
    · simpa only [Function.update_of_ne hq] using hstore.ordered q
  · intro q r hr j
    by_cases hq : q = p
    · subst q
      exact clipped_rows_lower (offset p) (hoffset p) out.records
        (hheadOut.trans (hstore.store_valid p).1) horder r (by simpa using hr) j
    · exact hstore.lower q r (by simpa only [Function.update_of_ne hq] using hr) j
  · intro q r hr
    by_cases hq : q = p
    · subst q
      exact hvalid r (by simpa using hr)
    · exact hstore.valid q r (by simpa only [Function.update_of_ne hq] using hr)
  · intro q
    by_cases hq : q = p
    · subst q
      exact ⟨by simpa using hheadOut.trans (hstore.store_valid p).1,
        by simpa using hinitial.trans hsub⟩
    · simpa only [Function.update_of_ne hq] using hstore.store_valid q

end EnvyFreeResearch.Full.Chores.SubCoreLeaves
