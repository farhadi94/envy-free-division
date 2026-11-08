import EnvyFreeResearch.Full.UpperShrinkCarveExecution
import EnvyFreeResearch.Full.UpperShrinkCarveMedianChain

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperEndpointCache

def pieceDomain (pieces : List (Piece k)) : Set ℝ := domain (pieces.flatMap Piece.cells)

theorem mem_pieceDomain {pieces : List (Piece k)} {x : ℝ} :
    x ∈ pieceDomain pieces ↔ ∃ p ∈ pieces, x ∈ domain p.cells := by
  simp only [pieceDomain, mem_domain, List.mem_flatMap]
  constructor
  · rintro ⟨c, ⟨p, hp, hc⟩, hx⟩
    exact ⟨p, hp, c, hc, hx⟩
  · rintro ⟨p, hp, c, hc, hx⟩
    exact ⟨c, ⟨p, hp, hc⟩, hx⟩

theorem pieceDomain_append (a b : List (Piece k)) :
    pieceDomain (a ++ b) = pieceDomain a ∪ pieceDomain b := by
  simp only [pieceDomain, List.flatMap_append, UpperDomainDifference.domain_append]

theorem pieceDomain_cons (p : Piece k) (rest : List (Piece k)) :
    pieceDomain (p :: rest) = domain p.cells ∪ pieceDomain rest := by
  simp only [pieceDomain, List.flatMap_cons, UpperDomainDifference.domain_append]

theorem piece_subset_domain (pieces : List (Piece k)) (p : Piece k) (hp : p ∈ pieces) :
    domain p.cells ⊆ pieceDomain pieces := fun _ hx => mem_pieceDomain.mpr ⟨p, hp, hx⟩

structure Mesh.Physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (U : Set ℝ) (mesh : Mesh n k) : Prop where
  truthful : Truthful μ mesh.history
  pieces : ∀ p ∈ mesh.pieces, WellFormed μ (⟨p.cells,mesh.history⟩ : State n)
  disjoint : mesh.pieces.Pairwise (fun p q => Disjoint (domain p.cells) (domain q.cells))
  cover : pieceDomain mesh.pieces = U

theorem wellFormed_history_extend (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (cells : List Component) (before after : History n)
    (hw : WellFormed μ (⟨cells,before⟩ : State n)) (ht : Truthful μ after) (he : before ⊆ after) :
    WellFormed μ (⟨cells,after⟩ : State n) :=
  ⟨hw.1,hw.2.1,ht,recordedHistory_mono cells hw.2.2.2 he⟩

theorem children_domain (p : Piece k) (state : State n) :
    pieceDomain (children p state) = domain state.cells := by
  simp [pieceDomain,children,List.flatMap_map]

theorem children_disjoint (p : Piece k) (state : State n) (hd : DisjointComponents state.cells) :
    (children p state).Pairwise (fun a b => Disjoint (domain a.cells) (domain b.cells)) := by
  simpa only [children,List.pairwise_map,domain,union_empty,DisjointComponents] using hd

theorem children_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (p : Piece k) (state : State n)
    (hw : WellFormed μ state) (after : History n) (ht : Truthful μ after) (he : state.history ⊆ after) :
    ∀ child ∈ children p state, WellFormed μ (⟨child.cells,after⟩ : State n) := by
  intro child hc
  change child ∈ state.cells.map (fun c => (⟨[c],p.fraction⟩ : Piece k)) at hc
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hc
  apply wellFormed_history_extend μ _ state.history after _ ht he
  refine ⟨by simp [UpperRecordedDomain.Ordered], by simp [DisjointComponents], hw.2.2.1, ?_⟩
  intro i x hx
  apply hw.2.2.2 i x
  rcases hx with ⟨d,hd,hx⟩
  have hdc : d = c := by simpa using hd
  exact ⟨c,hcm,hdc ▸ hx⟩

end EnvyFreeResearch.Full.UpperShrinkCarve
