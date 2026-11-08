import EnvyFreeResearch.Full.ChoresEqualizerTable
import EnvyFreeResearch.Full.ChoresPackageLedger

/-! Initial packages are constructed from the actual recorded equalizer
table. Original envy-freeness makes every initial reserve zero. The live
allocation realizes the original whole shares, including null material. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PackageGeometry
open Set MeasureTheory ChoreComposition Equalizers OrderedUnion InitialPartition
open scoped Classical

variable {n : ℕ} {Root : Type*}

def initialFrame (root : Root) (parents : Fin n → List (Parent n)) (table : Table n) : Frame (Fin n) Root where
  root := root
  baseline := baselines parents
  owner := Equiv.refl _
  allowed := fun p => {p}
  forbidden := fun _ => ∅
  equalizerCost := fun i p j => (table (p,j)).values i
  frontierGap := fun i p => baselines parents i-cachedValue (parents p) i

theorem initial_frame_good (root : Root) (parents : Fin n → List (Parent n)) (table : Table n)
    (hvalue : ∀ p, (table (p,p)).values p = baselines parents p) :
    (initialFrame root parents table).Good := by
  refine ⟨fun _ => Finset.mem_singleton_self _,?_⟩
  intro p j hj
  have heq : j = p := Finset.mem_singleton.mp hj
  subst j
  exact hvalue p

theorem initial_reserve_zero (root : Root) (parents : Fin n → List (Parent n)) (table : Table n)
    (hwhole : ∀ p i, (table (p,p)).values i = cachedValue (parents p) i)
    (hEF : ∀ i p, baselines parents i ≤ cachedValue (parents p) i) (i j p : Fin n) :
    (initialFrame root parents table).reserve i j p = 0 := by
  by_cases hj : j = p
  · subst j
    simp only [Frame.reserve,Frame.gap,initialFrame,R7Chores.recipientReserve,
      Finset.mem_singleton_self,ite_true,hwhole,R7Chores.clipped]
    exact max_eq_left (sub_nonpos.mpr (hEF i p))
  · simp only [Frame.reserve,Frame.gap,initialFrame,R7Chores.recipientReserve,
      Finset.mem_singleton, hj, ite_false,Finset.notMem_empty,R7Chores.clipped]
    exact max_eq_left (sub_nonpos.mpr (hEF i p))

theorem initial_package_valid (root : Root) (parents : Fin n → List (Parent n)) (table : Table n)
    (hwhole : ∀ p i, (table (p,p)).values i = cachedValue (parents p) i)
    (hEF : ∀ i p, baselines parents i ≤ cachedValue (parents p) i) :
    (Package.seed (initialFrame root parents table)).Valid := by
  apply seed_valid
  · exact initial_frame_good root parents table (fun p => hwhole p p)
  · intro i j p _
    exact initial_reserve_zero root parents table hwhole hEF i j p

/-- Every table returned by the concrete recording program supplies the
literal initial package semantics. All reserve inequalities are derived. -/
theorem recorded_initial_package (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (root : Root) (pieces : Fin n → Set ℝ) (parents : Fin n → List (Parent n))
    (hc : ∀ p, CacheValid (measureProfile cost) (pieces p) (parents p))
    (hEF : ∀ i j, (cost i).real (pieces i) ≤ (cost i).real (pieces j)) (table : Table n)
    (hcorrect : ∀ p j, Correct cost (pieces p) (baselines parents) j (table (p,j)))
    (hown : ∀ p, (table (p,p)).parts.prefixParts = parents p) :
    (Package.seed (initialFrame root parents table)).Valid ∧
      (∀ i p, (initialFrame root parents table).allocation.cost i p = (cost i).real (pieces p)) := by
  have hv (p i : Fin n) : cachedValue (parents p) i = (cost i).real (pieces p) := by
    rw [← (hc p).2.2,material_value cost _ (hc p).1 (hc p).2.1]
  have hwhole (p i : Fin n) : (table (p,p)).values i = cachedValue (parents p) i := by
    have hmat := (hcorrect p p).2.1.2.2
    rw [hown p,(hc p).2.2] at hmat
    rw [(hcorrect p p).2.2.2.2 i,← hmat,← hv]
  refine ⟨initial_package_valid root parents table hwhole ?_,?_⟩
  · intro i p
    simpa only [baselines,hv] using hEF i p
  · intro i p
    change (table (p,p)).values i = _
    rw [hwhole,hv]

end EnvyFreeResearch.Full.Chores.PackageGeometry
