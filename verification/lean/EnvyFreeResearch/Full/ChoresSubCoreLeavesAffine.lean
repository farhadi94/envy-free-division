import EnvyFreeResearch.Full.ChoresSubCoreLeavesClipped

/-! Concrete affine suffix leaves with a separate common virtual bottom.
Only nonnegative physical targets reach the recorder. A zero-primary target
below the first physical secondary label inserts an actual empty suffix;
the virtual interior is never sent to the physical oracle. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCoreLeaves
open Set OracleProtocol IntervalOracle QueryProgram Persistent Suffix SubCorePhysical
open scoped Classical

variable {n : ℕ} {Root : Type*} [Fintype Root] [Nonempty Root]

def affineInitial (offset total : Root → Fin n → ℝ) : Store Root (Record n) :=
  fun p => [affineEmpty (offset p),affineWhole (offset p) (total p)]

def affineBaseline (offset : Root → Fin n → ℝ) (i : Fin n) : Lex (ℝ × ℚ) :=
  toLex ((virtualBottom offset).formal i)

abbrev affineValidity (P : Root → Profile (Fin n)) (offset total : Root → Fin n → ℝ) :
    RecordValidity Root (Record n) where
  valid := fun p r => AffineSound (P p) (offset p) r ∧ r.point ∈ Icc (0 : ℝ) 1
  storeValid := fun store => ∀ p,
    (∃ head, (store p).head? = some head ∧ head.point = 0) ∧
    (affineInitial offset total p).Sublist (store p)

theorem affine_initial_wellFormed (P : Root → Profile (Fin n))
    (hmono : ∀ p i, Monotone ((P p).cumulative i))
    (offset total : Root → Fin n → ℝ) (htotal : ∀ p i, total p i = (P p).cumulative i 1) :
    letI := affineValidity P offset total
    WellFormed id (affineBaseline offset) (affineInitial offset total) := by
  letI := affineValidity P offset total
  have hgood (p : Root) (r : Record n) (hr : r ∈ affineInitial offset total p) :
      AffineSound (P p) (offset p) r ∧ r.point ∈ Icc (0 : ℝ) 1 := by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨affine_empty_sound (P p) (offset p),by norm_num [affineEmpty]⟩
    · have heq := List.mem_singleton.mp hr
      subst r
      exact ⟨affine_whole_sound (P p) (offset p) (total p) (htotal p),by norm_num [affineWhole]⟩
  refine ⟨?_,?_,hgood,?_⟩
  · intro p
    have hnonneg (i : Fin n) : 0 ≤ total p i := by
      rw [htotal p i,← (P p).zero i]
      exact hmono p i zero_le_one
    simpa [affineInitial] using affine_initial_before (offset p) (total p) hnonneg
  · intro p r hr i
    have h := virtual_before_physical (P p) (hmono p) offset p r (hgood p r hr).1 (hgood p r hr).2.1
    exact (Prod.Lex.toLex_lt_toLex.mpr (h.2 i)).le
  · intro p
    exact ⟨⟨affineEmpty (offset p),rfl,rfl⟩,List.Sublist.refl _⟩

def affineLookupProgram (offset : Root → Fin n → ℝ) (records : List (Record n))
    (i : Fin n) (target : ℝ × ℚ) : Program (Query (Fin n)) ℝ (Lookup.Result (Record n)) :=
  (affineVirtualEnsureProgram (virtualBottom offset) records i target).bind (fun out =>
    .returned ⟨out.records,out.selected⟩)

def affineEnsure (offset : Root → Fin n → ℝ) (p : Root) (i : Fin n)
    (target : ℝ × ℚ) (records : List (Record n)) :
    Program (Masked.TaggedQuery Root n) ℝ (Lookup.Result (Record n)) :=
  Masked.tagProgram p (affineLookupProgram offset records i target)

theorem affine_whole_stored (P : Root → Profile (Fin n))
    (offset total : Root → Fin n → ℝ) (store : Store Root (Record n)) (p : Root) :
    letI := affineValidity P offset total
    WellFormed id (affineBaseline offset) store →
      Stored id store p (orderedRecord (affineWhole (offset p) (total p))) := by
  letI := affineValidity P offset total
  intro hs
  exact ⟨affineWhole (offset p) (total p),
    (hs.store_valid p).2.subset (by simp [affineInitial]),rfl⟩

def AffineResultGood (P : Profile (Fin n)) (offset : Fin n → ℝ)
    (records : List (Record n)) (i : Fin n) (target : ℝ × ℚ)
    (out : Lookup.Result (Record n)) : Prop :=
  out.records.Pairwise Before ∧
  (∀ r ∈ out.records, AffineSound P offset r ∧ r.point ∈ Icc (0 : ℝ) 1) ∧
  records.Sublist out.records ∧
  (∃ head, out.records.head? = some head ∧ head.point = 0) ∧
  out.selected ∈ out.records ∧ out.selected.formal i = target

theorem affine_records_targets (P : Root → Profile (Fin n))
    (hmono : ∀ p i, Monotone ((P p).cumulative i))
    (offset total : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ)
    (hpolicy : Masked.IsLegalPolicy P oracle) :
    letI := affineValidity P offset total
    RecordsTargets id (affineEnsure offset) (affineBaseline offset) oracle
      (fun q => isCutQuery q.2) n := by
  letI := affineValidity P offset total
  intro store hstore p i target cap hcap _hlower hnonneg hupper prior
  obtain ⟨head,hhead,hheadPoint⟩ := (hstore.store_valid p).1
  have hinitial : (affineInitial offset total p).Sublist (store p) := (hstore.store_valid p).2
  obtain ⟨capPayload,hcapMem,hcapView⟩ := hcap
  have hupper' : toLex (ofLex target) ≤ toLex (capPayload.formal i) := by
    change target ≤ toLex (cap.record.formal i) at hupper
    rw [← hcapView] at hupper
    exact hupper
  have hexists : ∃ rest, store p = head::rest := by
    cases he : store p with
    | nil => simp [he] at hhead
    | cons first rest =>
      have hfirst : first = head := by simpa [he] using hhead
      subst first
      exact ⟨rest,rfl⟩
  obtain ⟨rest,hlist⟩ := hexists
  have hheadMem : head ∈ store p := hlist.symm ▸ List.mem_cons_self
  have hbefore : Before (virtualBottom offset) head :=
    virtual_before_physical (P p) (hmono p) offset p head
      (hstore.valid p head hheadMem).1 (hstore.valid p head hheadMem).2.1
  have htop : ∃ last ∈ head::rest,
      recordLT (ofLex target) (last.formal i) ∨ last.formal i = ofLex target :=
    ⟨capPayload,hlist ▸ hcapMem,pair_upper_of_lex_le _ _ hupper'⟩
  have hsource : ∀ policy, AdaptiveOracle.IsLegalPolicy (P p) policy →
      ∃ result trace, Executes policy (affineLookupProgram offset (store p) i (ofLex target)) [] result trace ∧
        AffineResultGood (P p) (offset p) (store p) i (ofLex target) result ∧
        trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 := by
    intro policy hlegal
    obtain ⟨out,trace,hexec,hQ,hC,horder,hgood,hsub,_hsize,_hlast,hs,ht,newHead,hh,hz,_hb⟩ :=
      affine_virtual_ensure_correct (P p) (hmono p) policy hlegal (offset p) (hoffset p)
        (virtualBottom offset) head rest i (ofLex target) (hlist ▸ hstore.ordered p)
        (fun r hr => (hstore.valid p r (hlist.symm ▸ hr)).1)
        (fun r hr => (hstore.valid p r (hlist.symm ▸ hr)).2) hheadPoint hbefore
        (virtual_primary_negative offset hoffset) hnonneg htop []
    let converted : Lookup.Result (Record n) := ⟨out.records,out.selected⟩
    refine ⟨converted,trace,?_,?_,hQ,hC⟩
    · have h := hexec.bind (fun out => Program.returned
        (⟨out.records,out.selected⟩ : Lookup.Result (Record n))) (Executes.returned converted ([]++trace))
      simpa only [affineLookupProgram,hlist,List.append_nil] using h
    · exact ⟨horder,hgood,hlist.symm ▸ hsub,⟨newHead,hh,hz⟩,hs,ht⟩
  obtain ⟨out,trace,hexec,hgood,hQ,hC⟩ := Masked.tag_correct P oracle hpolicy prior p
    (affineLookupProgram offset (store p) i (ofLex target))
    (AffineResultGood (P p) (offset p) (store p) i (ofLex target)) n 1 hsource
  obtain ⟨horder,hvalid,hsub,hnewHead,hselected,hcopy⟩ := hgood
  have hleaf : Executes oracle (affineEnsure offset p i (ofLex target) (store p)) prior out trace := hexec
  obtain ⟨hglobal,hext,hrecord,htarget⟩ := ensure_global_executes id (affineEnsure offset)
    oracle store p i target out prior trace hleaf hsub hselected hcopy
  refine ⟨⟨Function.update store p out.records,orderedRecord out.selected⟩,trace,
    hglobal,?_,hext,hrecord,htarget,hQ,hC⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro q
    by_cases hq : q = p
    · subst q
      simpa only [Function.update_self,id_eq] using horder
    · simpa only [Function.update_of_ne hq] using hstore.ordered q
  · intro q r hr j
    by_cases hq : q = p
    · subst q
      have hv := hvalid r (by simpa using hr)
      have h := virtual_before_physical (P p) (hmono p) offset p r hv.1 hv.2.1
      exact (Prod.Lex.toLex_lt_toLex.mpr (h.2 j)).le
    · exact hstore.lower q r (by simpa only [Function.update_of_ne hq] using hr) j
  · intro q r hr
    by_cases hq : q = p
    · subst q
      exact hvalid r (by simpa using hr)
    · exact hstore.valid q r (by simpa only [Function.update_of_ne hq] using hr)
  · intro q
    by_cases hq : q = p
    · subst q
      exact ⟨by simpa using hnewHead,by simpa using hinitial.trans hsub⟩
    · simpa only [Function.update_of_ne hq] using hstore.store_valid q

end EnvyFreeResearch.Full.Chores.SubCoreLeaves
