import EnvyFreeResearch.Full.RefinedChoresTerminalCohortComplement
import EnvyFreeResearch.Full.RefinedChoresTerminalAggregateFullMargin
import EnvyFreeResearch.Full.RefinedChoresTerminalAggregateAtomic

/-! Terminal-class physical bounds instantiated on the actual complete
closed pool and its literal complementary caches. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentExtraction Chores.SubCoreEntry ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length)
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
include hsound horiginal hsep hr hH hscale hr_eq

theorem TerminalGroup.exhausted_offers_small
    (htype : group.terminalClass = .inr group.terminalClass.participants)
    (s : group.Root) (i : Fin n) :
    (cost i).real (TerminalGroup.blocks data normal original r H group s group.label) ≤ (n : ℝ)*r i/H := by
  subst r
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  rw [horiginal] at hs
  have hclass := (group.class_eq s).trans (congrArg Sum.inl htype)
  have h := Terminal.scan_exhausted_bounds hsep (index (data.source (group.roots s))) hs group.label hr hH hscale
    (data.sourceSet normal (group.roots s)) (data.pending (group.roots s)).partition.representative
    group.terminalClass.participants (by simpa only [horiginal] using hclass)
  simpa only [TerminalGroup.blocks,TerminalGroup.selectedOriginal,TerminalGroup.components,
    RefinedChoresTerminalScans.blocks,RefinedChoresTerminalScans.offer,horiginal] using h.1 i

include hparts

theorem TerminalGroup.atomic_extracted_bounds (B : Finset (Fin n))
    (htype : group.terminalClass = .inl (group.terminalClass.participants,B))
    (hwhole : ∃ j : group.terminalClass.participants, material (out.parts j).suffixParts =
      TerminalGroup.blocks data normal original r H group (out.allocation.assigned j) group.label) :
    B.Nonempty ∧ B ≠ Finset.univ ∧
      (∀ i ∈ B, H*(cost i).real R ≤ (cost i).real (extracted out)) ∧
      (∀ i ∉ B, (cost i).real (extracted out) ≤ (n : ℝ)^2*(cost i).real R/H) := by
  subst r
  exact RefinedChoresTerminalAggregate.atomic_extracted_bounds
    (TerminalGroup.selectedOriginal data normal original _ H group) group.label
    (TerminalGroup.components data normal original _ H group) cost c
    (fun s => hsound (data.source (group.roots s))) xs (fun s => index (data.source (group.roots s)))
    (fun s => horiginal (data.source (group.roots s))) R H hsep hr hH hscale group.terminalClass.participants B
    (fun s => (data.pending (group.roots s)).partition.representative)
    (fun s => (group.class_eq s).trans (congrArg Sum.inl htype)) out hparts hwhole

variable (hcorrect : PhysicalCorrect (affineUtility cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label)))
      Subtype.val out.allocation)
    (hvalid : (TerminalGroup.output data normal original r H group hr0 hH0 out).Valid)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root a, G.piece root a = (original root).piece a)
include good hcorrect hvalid hG

theorem TerminalGroup.exhausted_pool_margin
    (htype : group.terminalClass = .inr group.terminalClass.participants)
    (i : Fin n) (hi : i ∉ group.terminalClass.participants) (j : group.terminalClass.participants) :
    (H-(n : ℝ)/H)*(cost i).real R ≤
      (cost i).real (ComponentPhysical.bundle (Outer.closePool
        (TerminalGroup.pool data normal original r H group hr0 hH0 out))
        (TerminalGroup.poolCache data normal original r H group hr0 hH0 out) j) -
      (cost i).real (ComponentPhysical.bundle (Outer.closePool
        (TerminalGroup.pool data normal original r H group hr0 hH0 out))
        (TerminalGroup.poolCache data normal original r H group hr0 hH0 out) i) := by
  subst r
  apply RefinedChoresTerminalAggregate.exhausted_full_pool_margin
    (TerminalGroup.selectedOriginal data normal original _ H group) group.label
    (TerminalGroup.components data normal original _ H group) cost c
    (fun s => hsound (data.source (group.roots s))) xs (fun s => index (data.source (group.roots s)))
    (fun s => horiginal (data.source (group.roots s))) R H hsep hr hH hscale group.terminalClass.participants
    (fun s => (data.pending (group.roots s)).partition.representative)
    (fun s => (group.class_eq s).trans (congrArg Sum.inl htype)) out hparts
    (data.frames ∘ group.roots) (fun s => good.original_frame _)
    (TerminalGroup.path data normal original _ H group hr0 hH0)
    (TerminalGroup.pool data normal original _ H group hr0 hH0 out)
    (TerminalGroup.pool_valid data normal original _ H group hr0 hH0 out cost good hvalid)
    ((TerminalGroup.pool_ids data normal original _ H group hr0 hH0 out cost good hparts hcorrect).nodup_iff.mpr (Finset.nodup_toList _))
    G (TerminalGroup.poolCache data normal original _ H group hr0 hH0 out)
    (fun root a => by rw [hG]; exact TerminalGroup.pool_cache_subset data normal original _ H group hr0 hH0 out cost c hsound good hparts root a)
    (TerminalGroup.pool_realizes data normal original _ H group hr0 hH0 out cost c hsound good hparts)
    (TerminalGroup.donor_mem data normal original _ H group hr0 hH0 out) i hi j

theorem TerminalGroup.exhausted_residue_dominance
    (htype : group.terminalClass = .inr group.terminalClass.participants)
    (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate)
    (J : ℕ) (hroots : Fintype.card RootId ≤ J) (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
    (hnH : (n : ℝ)+2 ≤ H)
    (i : Fin n) (hi : i ∉ group.terminalClass.participants) (j : group.terminalClass.participants) :
    (cost i).real (R ∪ Outer.privateUnion
      (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)) ≤
      (cost i).real (ComponentPhysical.bundle (Outer.closePool
        (TerminalGroup.pool data normal original r H group hr0 hH0 out))
        (TerminalGroup.poolCache data normal original r H group hr0 hH0 out) j) -
      (cost i).real (ComponentPhysical.bundle (Outer.closePool
        (TerminalGroup.pool data normal original r H group hr0 hH0 out))
        (TerminalGroup.poolCache data normal original r H group hr0 hH0 out) i) := by
  have hsmall := TerminalGroup.exhausted_offers_small data normal original r H group cost c hsound
    xs index horiginal R hsep hr hH hscale hr_eq htype
  have hprivate := TerminalGroup.pool_private_small data normal original r H group hr0 hH0 out cost c hsound
    good hparts oldPrivate hold hsmall
  have hu := (Terminal.full_residue_bounds (cost i) R
    (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate) J H hH0 hroots
    (fun root a => by simpa only [hr_eq] using hprivate root a i)).2
  exact (Terminal.exhausted_scalar_domination n J H ((cost i).real R) _ (hr i).le hnH hreserve hu).trans
    (TerminalGroup.exhausted_pool_margin data normal original r H group hr0 hH0 out cost c hsound good hparts
      xs index horiginal R hsep hr hH hscale hr_eq hcorrect hvalid G hG htype i hi j)

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.exhausted_residue_dominance
