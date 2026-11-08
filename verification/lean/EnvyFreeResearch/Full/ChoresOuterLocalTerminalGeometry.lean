import EnvyFreeResearch.Full.ChoresOuterLocalProgram
import EnvyFreeResearch.Full.ChoresTerminalExtractionResidue

/-! Exact atomic terminal domains and caches, derived from the actual
affine allocation and marked donor slots. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open ComponentRecording ComponentPayments ComponentExtraction
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (A : Finset (Fin n)) (out : ComponentClosed.Result (Root := Fin data.size) A)
  (oldPrivate : RootId → Fin n → List (Parent n))
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost r H)
  (hparts : PartsCorrect cost (domains (Terminal.blocks data original r H)
    data.pending.partition.representative) Subtype.val out)
  (hold : PrivateCorrect (measureProfile cost) (fun root p => (original root).piece p)
    data.cache oldPrivate)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(original root).piece p)
  (R : Set ℝ) (R0 : List (Parent n))
  (hR : CacheValid (measureProfile cost) R R0) (hd : ∀ root p, Disjoint R (G.piece root p))

include hsound good hparts hold hG hR hd

theorem atomic_remainder_cache :
    CacheValid (measureProfile cost)
      (R ∪ privateUnion (Terminal.remainingPrivate data original A out oldPrivate))
      (fullResidueCache R0 (Terminal.remainingPrivate data original A out oldPrivate)) := by
  let priv := terminalPrivateCache data original A out oldPrivate
  have hp := Terminal.residue_private_correct data original r H A out oldPrivate cost c hsound good hparts hold G hG
  have hv : ∀ root p, Valid (measureProfile cost) (priv root p) ∧ Ordered (priv root p) :=
    fun root p => ⟨(hp root p).1,(hp root p).2.1⟩
  have hs := private_subset (measureProfile cost) G (Terminal.updatedCache data original r H A out) priv hp
  have hc := full_removed_cache_correct (measureProfile cost) G priv (Terminal.extractedSlots data A out)
    hv hs R R0 hR hd
  rw [← full_removed_exact G priv (Terminal.extractedSlots data A out) hs R hd] at hc
  exact hc

omit hR hd R0 R hold oldPrivate in
theorem atomic_extracted_cache : CacheValid (measureProfile cost) (extracted out) (extractedCache out) := by
  apply extracted_cache_correct Subtype.val data.pending.partition.representative out cost
    (Terminal.blocks data original r H) hparts
  intro s t hst p q
  have hne : (data.source s,p) ≠ (data.source t,q) :=
    fun h => hst (source_injective data original cost r H good (congrArg Prod.fst h))
  apply (G.disjoint hne).mono
  · rw [hG,Terminal.blocks_complement data original r H cost c hsound]
    exact sdiff_subset
  · rw [hG,Terminal.blocks_complement data original r H cost c hsound]
    exact sdiff_subset

omit hR R0 in
theorem atomic_domain_partition :
    Disjoint (extracted out) (R ∪ privateUnion (Terminal.remainingPrivate data original A out oldPrivate)) ∧
    extracted out ∪ (R ∪ privateUnion (Terminal.remainingPrivate data original A out oldPrivate)) =
      R ∪ privateUnion (terminalPrivateCache data original A out oldPrivate) := by
  let priv := terminalPrivateCache data original A out oldPrivate
  have hp := Terminal.residue_private_correct data original r H A out oldPrivate cost c hsound good hparts hold G hG
  have hs := private_subset (measureProfile cost) G (Terminal.updatedCache data original r H A out) priv hp
  have he := Terminal.marked_private_eq_extracted data original A out oldPrivate
    (active_roots_injective data original cost r H good)
  have hdis := marked_remainder_disjoint G priv (Terminal.extractedSlots data A out) hs
  rw [he] at hdis
  have hRx : Disjoint R (extracted out) := by
    rw [← he]
    apply disjoint_iUnion_right.mpr
    intro a
    apply disjoint_iUnion_right.mpr
    intro _
    exact (hd a.1 a.2).mono_right (hs a.1 a.2)
  refine ⟨disjoint_union_right.mpr ⟨hRx.symm,hdis⟩,?_⟩
  have hu := marked_remainder_partition priv (Terminal.extractedSlots data A out)
  rw [he] at hu
  rw [union_left_comm]
  exact congrArg (fun S => R ∪ S) hu

end EnvyFreeResearch.Full.Chores.Outer
