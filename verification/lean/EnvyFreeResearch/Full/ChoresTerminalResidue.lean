import EnvyFreeResearch.Full.ChoresOuterPrivateTerminal
import EnvyFreeResearch.Full.ChoresOuterResidueAssembly

/-! The terminal residue is assembled from actual retained complementary
records. Its union with the allocated base is the entire original domain. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ComponentRecording ComponentPayments
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (A : Finset (Fin n)) (out : ComponentClosed.Result (Root := Fin data.size) A)
  (oldPrivate : RootId → Fin n → List (Parent n))
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost r H)
  (hparts : PartsCorrect cost (domains (blocks data original r H)
    data.pending.partition.representative) Subtype.val out)
  (hold : Outer.PrivateCorrect (measureProfile cost) (fun root p => (original root).piece p)
    data.cache oldPrivate)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(original root).piece p)

include hsound good hparts hold hG

theorem residue_private_correct : Outer.PrivateCorrect (measureProfile cost) G.piece
    (updatedCache data original r H A out) (Outer.terminalPrivateCache data original A out oldPrivate) := by
  intro root p
  rw [hG]
  exact Outer.terminal_private_correct data original r H A out cost c hsound good hparts oldPrivate hold root p

theorem residue_cache_correct (R : Set ℝ) (R0 : List (Parent n))
    (hR : CacheValid (measureProfile cost) R R0) (hd : ∀ root p, Disjoint R (G.piece root p)) :
    CacheValid (measureProfile cost)
      (R ∪ Outer.privateUnion (Outer.terminalPrivateCache data original A out oldPrivate))
      (Outer.fullResidueCache R0 (Outer.terminalPrivateCache data original A out oldPrivate)) :=
  Outer.full_residue_cache_correct (measureProfile cost) G (updatedCache data original r H A out) _
    (residue_private_correct data original r H A out oldPrivate cost c hsound good hparts hold G hG)
    R R0 hR hd

theorem residue_partition (R : Set ℝ) (hd : ∀ root p, Disjoint R (G.piece root p)) :
    Disjoint (Outer.privateUnion (updatedCache data original r H A out))
      (R ∪ Outer.privateUnion (Outer.terminalPrivateCache data original A out oldPrivate)) ∧
    Outer.privateUnion (updatedCache data original r H A out) ∪
      (R ∪ Outer.privateUnion (Outer.terminalPrivateCache data original A out oldPrivate)) =
      R ∪ (⋃ root, ⋃ p, G.piece root p) := by
  have hpriv := residue_private_correct data original r H A out oldPrivate cost c hsound good hparts hold G hG
  have hsub := updated_cache_subset data original r H A out cost c hsound good hparts G hG
  refine ⟨disjoint_union_right.mpr ⟨?_,Outer.retained_private_disjoint _ G _ _ hpriv hsub⟩,?_⟩
  · apply disjoint_iUnion_left.mpr
    intro root
    apply disjoint_iUnion_left.mpr
    intro p
    exact (hd root p).symm.mono_left (hsub root p)
  · rw [union_left_comm,Outer.private_union_partition _ G _ _ hpriv hsub]

end EnvyFreeResearch.Full.Chores.Terminal
