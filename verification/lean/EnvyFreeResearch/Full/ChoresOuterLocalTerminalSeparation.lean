import EnvyFreeResearch.Full.ChoresOuterLocalTerminalGeometry
import EnvyFreeResearch.Full.ChoresTerminalExtraction
import EnvyFreeResearch.Full.ChoresTerminalAggregateSeparation

/-! The actual atomic terminal split satisfies the separation ratios of
the two-group recursive completion routine. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open ComponentRecording ComponentPayments ComponentExtraction
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) [Nonempty (Fin data.size)]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ) (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (p : Fin n) (A B : Finset (Fin n))
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl (.inl (A,B)))
  (hlabel : ∀ j ∈ A, data.pending.partition.representative j=p)
  (out : ComponentClosed.Result (Root := Fin data.size) A)
  (hparts : PartsCorrect cost
    (domains (Terminal.blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      data.pending.partition.representative) Subtype.val out)
  (hwhole : ∃ j : A, material (out.parts j).suffixParts=
    Terminal.blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H
      (out.allocation.assigned j) p)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (oldPrivate : RootId → Fin n → List (Parent n))
  (hold : PrivateCorrect (measureProfile cost) (fun root p => (xs.get (index root)).piece p)
    data.cache oldPrivate)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(xs.get (index root)).piece p)
  (J : ℕ) (hcard : Fintype.card RootId ≤ J)
  (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
  (hlarge : 2*(2 : ℝ)^(n+2) ≤ H)
  (hsmall : (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ H)

include hsound hsep hr hH hscale hclass hlabel hparts hwhole good hold hG hcard hreserve hlarge hsmall

theorem actual_atomic_separation :
    B.Nonempty ∧ B ≠ Finset.univ ∧
    (∀ i ∈ B, (2 : ℝ)^(n+2)*(cost i).real
      (R ∪ privateUnion (Terminal.remainingPrivate data (fun root => xs.get (index root)) A out oldPrivate)) ≤
        (cost i).real (extracted out)) ∧
    (∀ i, i ∉ B → (2 : ℝ)^(n+2)*(cost i).real (extracted out) ≤
      (cost i).real (R ∪ privateUnion (Terminal.remainingPrivate data (fun root => xs.get (index root)) A out oldPrivate))) := by
  have hx := Terminal.actual_atomic_extracted_bounds data cost xs index c hsound R H hsep hr hH hscale
    p A B hclass hlabel out hparts hwhole
  have hpos : 0 < H := lt_trans zero_lt_one hH
  have hu (i : Fin n) := Terminal.actual_atomic_residue_bounds data (fun root => xs.get (index root)) A out
    oldPrivate cost R H hpos c hsound good hparts hold G hG J hcard i
  refine ⟨hx.1,hx.2.1,?_,?_⟩
  · intro i hi
    exact Terminal.atomic_large_separation n J H ((2 : ℝ)^(n+2)) _ _ _
      hpos (by positivity) (hr i).le hreserve hlarge (hx.2.2.1 i hi) (hu i).2
  · intro i hi
    exact Terminal.atomic_small_separation n H ((2 : ℝ)^(n+2)) _ _ _
      hpos (by positivity) (hr i).le hsmall (hx.2.2.2 i hi) (hu i).1

end EnvyFreeResearch.Full.Chores.Outer
