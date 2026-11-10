import EnvyFreeResearch.Full.RefinedChoresTerminalAggregateExhausted
import EnvyFreeResearch.Full.RefinedChoresTerminalAggregatePhysical
import EnvyFreeResearch.Full.ChoresTerminalAggregateResidue

/-! Physical exhaustion margins for independently scanned source components. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
open Set MeasureTheory IntervalOracle
open Chores Chores.InitialPartition Chores.OrderedUnion Chores.Snapshot Chores.Frontier
open Chores.ComponentRecording Chores.ComponentPayments Chores.ComponentExtraction
open RefinedChoresTerminalScans
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (original : Root → Snapshot.Output n) (p : Fin n)
    (components : Root → Finset (Fin n))
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ s, ∃ U, Snapshot.Sound cost U c (original s))
    (xs : List (Snapshot.Output n)) (index : Root → Fin xs.length)
    (horiginal : ∀ s, original s = xs.get (index s)) (R : Set ℝ) (H : ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (A : Finset (Fin n)) (representatives : Root → Fin n → Fin n)
    (hclass : ∀ s, Reveal.classify (original s).equalizers p (fun i => (cost i).real R) H
      (components s) (representatives s) = .inl (.inr A))
    (out : RefinedChoresClosed.Result (Root := Root) A)
    (hparts : PartsCorrect cost (domains
      (blocks original p (fun i => (cost i).real R) H components) (fun _ => p)) Subtype.val out)

    (frames : Root → ChoreComposition.Frame (Fin n) RootId)
    (hframes : ∀ s, Chores.Outer.OriginalFrame (frames s) (original s))
    (hpath : ∀ s j, j ∈ A → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (pool : List (ChoreComposition.Package (Fin n) RootId))
    (hpool : ChoreComposition.PoolValid pool) (hdistinct : ChoreComposition.PoolDistinct pool)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n))
    (hsub : ∀ root a, material (cache root a) ⊆ G.piece root a)
    (hcost : ∀ a ∈ pool.flatMap ChoreComposition.Package.allocations, ∀ i q,
      a.cost i q=(cost i).real (material (cache a.root q)))
    (hmem : ∀ j : A, actualDonor A p frames hpath (gaps original) out j ∈
      pool.flatMap ChoreComposition.Package.allocations)
include hsound horiginal hsep hr hH hscale hclass hparts hframes hpool hdistinct hsub hcost hmem

theorem exhausted_full_pool_margin (i : Fin n) (hi : i ∉ A) (j : A) :
    (H-(n : ℝ)/H)*(cost i).real R ≤
      (cost i).real (Chores.ComponentPhysical.bundle (Chores.Outer.closePool pool) cache j)-
      (cost i).real (Chores.ComponentPhysical.bundle (Chores.Outer.closePool pool) cache i) := by
  have hblock (s : Root) : blocks original p (fun i => (cost i).real R) H components s p ⊆
      (original s).piece p := by
    have hs := (hsound s).choose_spec
    have hc : material (Terminal.offer (original s) p (fun i => (cost i).real R) H (components s)) =
        (original s).piece p \ material (Terminal.front (original s) p (fun i => (cost i).real R) H (components s)) :=
      Frontier.offer_complement cost _ _ (snapshot_parent_cache hs p) _ p _
        (snapshot_equalizers hs p) (hs.own_equalizers p).1 _
    change material (Terminal.offer _ _ _ _ _) ⊆ _
    rw [hc]
    exact sdiff_subset
  have hgap (s : Root) (i : Fin n) : gaps original s p i =
      (cost i).real ((original s).piece p)-(frames s).baseline i :=
    Chores.Outer.original_gap cost (hsound s).choose_spec (frames s) (hframes s) p i
  apply full_pool_margin A p frames hpath (gaps original) out cost
    (fun s => (original s).piece) (blocks original p (fun i => (cost i).real R) H components)
    hparts hblock hgap pool hpool hdistinct G cache hsub hcost j (hmem j) i
    (fun heq => hi (heq ▸ j.property)) ((H-(n : ℝ)/H)*(cost i).real R)
  rw [(hframes _).baseline]
  exact exhausted_donor_deviation original p components cost c hsound xs index horiginal R H
    hsep hr hH hscale A representatives hclass out hparts i hi j

/-- The literal entire residue is dominated, including private remnants
of every frozen ancestor, once its actual per-root slot bounds are supplied. -/
theorem exhausted_full_residue_dominance [Fintype RootId]
    (privateCache : RootId → Fin n → List (Parent n)) (J : ℕ)
    (hroots : Fintype.card RootId ≤ J)
    (hsmall : ∀ root a i, (cost i).real (material (privateCache root a)) ≤ (n : ℝ)*(cost i).real R/H)
    (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H) (hnH : (n : ℝ)+2 ≤ H)
    (i : Fin n) (hi : i ∉ A) (j : A) :
    (cost i).real (R ∪ Chores.Outer.privateUnion privateCache) ≤
      (cost i).real (Chores.ComponentPhysical.bundle (Chores.Outer.closePool pool) cache j)-
      (cost i).real (Chores.ComponentPhysical.bundle (Chores.Outer.closePool pool) cache i) := by
  have hu := (Terminal.full_residue_bounds (cost i) R privateCache J H
    (by linarith) hroots (fun root a => hsmall root a i)).2
  exact (Terminal.exhausted_scalar_domination n J H ((cost i).real R) _ (hr i).le
    hnH hreserve hu).trans
      (exhausted_full_pool_margin original p components cost c hsound xs index horiginal R H
        hsep hr hH hscale A representatives hclass out hparts frames hframes hpath pool hpool
        hdistinct G cache hsub hcost hmem i hi j)

end EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
#print axioms EnvyFreeResearch.Full.RefinedChoresTerminalAggregate.exhausted_full_residue_dominance
