import EnvyFreeResearch.Full.ChoresContinuous
import EnvyFreeResearch.R3ChoreAncestry

/-! Physical package allocations and exact original-measure accounting.
The finite credit/debit tables are computed from literal disjoint measurable
pieces; the own-cost identity is proved from the recipient permutations. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PackageGeometry
open Set MeasureTheory
open scoped Classical BigOperators

structure Pieces (Root Agent : Type*) where
  piece : Root → Agent → Set ℝ
  measurable : ∀ s p, MeasurableSet (piece s p)
  disjoint : Pairwise (fun a b : Root × Agent => Disjoint (piece a.1 a.2) (piece b.1 b.2))

variable {Root Agent : Type*} [Fintype Root] [Fintype Agent]

def Pieces.assigned (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent) (s : Root) (i : Agent) : Set ℝ :=
  G.piece s ((owner s).symm i)

def Pieces.bundle (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent) (i : Agent) : Set ℝ :=
  ⋃ s, G.assigned owner s i

omit [Fintype Root] [Fintype Agent] in
theorem Pieces.root_disjoint (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    {s t : Root} (hst : s ≠ t) (i j : Agent) : Disjoint (G.assigned owner s i) (G.assigned owner t j) :=
  @G.disjoint (s,(owner s).symm i) (t,(owner t).symm j) (fun h => hst (congrArg Prod.fst h))

theorem Pieces.bundles_disjoint (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent) :
    Pairwise (fun i j => Disjoint (G.bundle owner i) (G.bundle owner j)) := by
  intro i j hij
  apply disjoint_iUnion_left.mpr
  intro s
  apply disjoint_iUnion_right.mpr
  intro t
  by_cases hst : s = t
  · subst t
    apply @G.disjoint (s,(owner s).symm i) (s,(owner s).symm j)
    intro h
    exact hij ((owner s).symm.injective (congrArg Prod.snd h))
  · exact G.root_disjoint owner hst i j

omit [Fintype Agent] in
theorem Pieces.bundle_measurable (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent) (i : Agent) :
    MeasurableSet (G.bundle owner i) :=
  MeasurableSet.iUnion (fun s => G.measurable s ((owner s).symm i))

theorem Pieces.bundle_value (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] (i j : Agent) :
    (cost i).real (G.bundle owner j) = ∑ s, (cost i).real (G.assigned owner s j) := by
  exact measureReal_iUnion_fintype (fun s t hst => G.root_disjoint owner hst j j)
    (fun s => G.measurable s ((owner s).symm j)) (fun _ => measure_ne_top _ _)

omit [Fintype Root] [Fintype Agent] in
theorem Pieces.bundle_cover (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent) :
    (⋃ i, G.bundle owner i) = ⋃ s, ⋃ p, G.piece s p := by
  simp only [Pieces.bundle]
  rw [iUnion_comm]
  congr 1
  funext s
  exact (owner s).symm.surjective.iUnion_comp (G.piece s)

def Pieces.credit (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) (baseline : Root → Agent → ℝ) (s : Root) (i p : Agent) : ℝ :=
  if owner s p = i then baseline s i-(cost i).real (G.piece s p) else 0

def Pieces.debit (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) (baseline : Root → Agent → ℝ) (s : Root) (i j p : Agent) : ℝ :=
  if owner s p = j then max 0 (baseline s i-(cost i).real (G.piece s p)) else 0

omit [Fintype Root] in
theorem Pieces.credit_sum (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) (baseline : Root → Agent → ℝ) (s : Root) (i : Agent) :
    ∑ p, G.credit owner cost baseline s i p = baseline s i-(cost i).real (G.assigned owner s i) := by
  have hs : (∑ p, G.credit owner cost baseline s i p) =
      G.credit owner cost baseline s i ((owner s).symm i) := by
    apply Finset.sum_eq_single ((owner s).symm i)
    · intro p hp hne
      have howner : owner s p ≠ i := fun h => hne ((owner s).injective (by simpa using h))
      simp only [Pieces.credit,ite_eq_right howner]
    · simp
  rw [hs]
  simp [Pieces.credit,Pieces.assigned]

omit [Fintype Root] in
theorem Pieces.debit_sum (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) (baseline : Root → Agent → ℝ) (s : Root) (i j : Agent) :
    ∑ p, G.debit owner cost baseline s i j p = max 0 (baseline s i-(cost i).real (G.assigned owner s j)) := by
  have hs : (∑ p, G.debit owner cost baseline s i j p) =
      G.debit owner cost baseline s i j ((owner s).symm j) := by
    apply Finset.sum_eq_single ((owner s).symm j)
    · intro p hp hne
      have howner : owner s p ≠ j := fun h => hne ((owner s).injective (by simpa using h))
      simp only [Pieces.debit,ite_eq_right howner]
    · simp
  rw [hs]
  simp [Pieces.debit,Pieces.assigned]

/-- This exact identity follows from the literal union, disjointness and
recipient permutations. It is not an assumed package payment equation. -/
theorem Pieces.own_identity (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (baseline : Root → Agent → ℝ) (i : Agent) :
    (cost i).real (G.bundle owner i) = (∑ s, baseline s i)-∑ p, ∑ s, G.credit owner cost baseline s i p := by
  rw [G.bundle_value owner cost i i]
  calc
    (∑ s, (cost i).real (G.assigned owner s i)) =
        ∑ s, (baseline s i-∑ p, G.credit owner cost baseline s i p) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [G.credit_sum]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_comm]

/-- Paying the actual per-label negative deviations leaves every original
positive deviation in the final physical envy margin. The payment inequality
is the package invariant to be established by the separate transitions. -/
theorem Pieces.surplus (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (baseline : Root → Agent → ℝ) (i j : Agent)
    (hbudget : ∀ p, (∑ s, G.debit owner cost baseline s i j p) ≤ ∑ s, G.credit owner cost baseline s i p) :
    (∑ s, max 0 ((cost i).real (G.assigned owner s j)-baseline s i)) ≤
      (cost i).real (G.bundle owner j)-(cost i).real (G.bundle owner i) := by
  have htotal := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset Agent)) => hbudget p)
  have hdebit : (∑ p, ∑ s, G.debit owner cost baseline s i j p) =
      ∑ s, max 0 (baseline s i-(cost i).real (G.assigned owner s j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    exact G.debit_sum owner cost baseline s i j
  rw [hdebit] at htotal
  have hsurplus := R3ChoreAncestry.surplus_bound (Finset.univ : Finset Root)
    (fun s => (cost i).real (G.assigned owner s j)) (fun s => baseline s i)
    (∑ p, ∑ s, G.credit owner cost baseline s i p) htotal
  rw [G.bundle_value owner cost i j,G.own_identity owner cost baseline i]
  rw [Finset.sum_sub_distrib] at hsurplus
  linarith

theorem Pieces.envy_free (G : Pieces Root Agent) (owner : Root → Equiv.Perm Agent)
    (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (baseline : Root → Agent → ℝ)
    (hbudget : ∀ i j, i ≠ j → ∀ p,
      (∑ s, G.debit owner cost baseline s i j p) ≤ ∑ s, G.credit owner cost baseline s i p) :
    ∀ i j, (cost i).real (G.bundle owner i) ≤ (cost i).real (G.bundle owner j) := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact le_rfl
  · have h := G.surplus owner cost baseline i j (hbudget i j hij)
    have hnonneg : 0 ≤ ∑ s, max 0 ((cost i).real (G.assigned owner s j)-baseline s i) :=
      Finset.sum_nonneg (fun _ _ => le_max_left _ _)
    linarith

end EnvyFreeResearch.Full.Chores.PackageGeometry
