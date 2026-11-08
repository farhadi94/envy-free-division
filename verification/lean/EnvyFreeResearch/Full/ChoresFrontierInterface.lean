import EnvyFreeResearch.Full.ChoresFrontierTracked
import EnvyFreeResearch.Full.ChoresFrontierInvariant

/-! Physical prefix/suffix and old-matching interfaces for the scheduler.
The prefix passed to compensation and the offered suffix are literal
complements in the immutable original root. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers
open scoped Classical

variable {n : ℕ}

def Outcome.front (table : Table n) (p : Fin n) : Outcome n → List (Parent n)
  | .outside q | .exhausted q => (table (p,q)).parts.prefixParts
  | .atomic a => boundaryPrefix table p a.castSucc

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
  (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
  (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
  (hown : (table (p,p)).parts.prefixParts=cache)

include hc hcorrect hown

theorem front_material (out : Outcome n) :
    material (out.front table p)=atomMaterial P ((atomsFromTable table p).take (out.boundary table p)) := by
  cases out with
  | outside q | exhausted q =>
    exact (prefix_material_rank cost P cache hc table p baseline hcorrect hown q).symm
  | atomic a => exact (boundary_prefix_valid cost P cache hc table p baseline hcorrect a.castSucc).2.2

theorem front_cache_valid (out : Outcome n) :
    CacheValid (measureProfile cost) (material (out.front table p)) (out.front table p) := by
  cases out with
  | outside q | exhausted q => exact ⟨(hcorrect q).2.1.1,(hcorrect q).2.1.2.1,rfl⟩
  | atomic a =>
    have h := boundary_prefix_valid cost P cache hc table p baseline hcorrect a.castSucc
    exact ⟨h.1,h.2.1,rfl⟩

theorem offer_complement (out : Outcome n) :
    material (out.offer table p cache)=P \ material (out.front table p) := by
  obtain ⟨_,hd,hcover,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  rw [offer_material cost P cache hc table p baseline hcorrect hown,
    front_material cost P cache hc table p baseline hcorrect hown,
    atomMaterial_drop P _ hd,hcover]

theorem front_subset (out : Outcome n) : material (out.front table p) ⊆ P := by
  rw [front_material cost P cache hc table p baseline hcorrect hown]
  calc
    _ ⊆ atomMaterial P (atomsFromTable table p) := atomMaterial_mono (List.take_subset _ _)
    _ = P := (original_atom_table cost P cache hc table p baseline hcorrect hown).2.2.1

theorem offer_subset (out : Outcome n) : material (out.offer table p cache) ⊆ P := by
  rw [offer_complement cost P cache hc table p baseline hcorrect hown]
  exact sdiff_subset

theorem ranked_prefix_containment (i j : Fin n) (hij : rankOf table p i ≤ rankOf table p j) :
    material (table (p,i)).parts.prefixParts ⊆ material (table (p,j)).parts.prefixParts := by
  rw [← prefix_material_rank cost P cache hc table p baseline hcorrect hown i,
    ← prefix_material_rank cost P cache hc table p baseline hcorrect hown j]
  exact atomMaterial_take_mono P _ hij

theorem atomic_old_atom_retained (r : Fin n → ℝ) (H : ℝ) (C R F : Finset (Fin n)) (z : Fin n)
    (hinv : Invariant (weight table p) (rankOf table p) r H
      (eligible (weight table p) (rankOf table p) r H) C R F z)
    (t : ℕ) (a : Fin n) (hscan : largestBad (weight table p) r H t=some a)
    (i : Fin n) (hi : i ∈ R) :
    ((atomsFromTable table p).get (Fin.cast (atoms_from_table_length table p).symm a)).domain P ⊆
      material (table (p,i)).parts.prefixParts := by
  have hpart := atomic_allowed (weight table p) (rankOf table p) r H C R F z hinv t a hscan hi
  exact original_atom_in_equalizer cost P cache hc table p baseline hcorrect hown a i
    (Finset.mem_filter.mp hpart).2

theorem outside_old_equalizers_contain (r : Fin n → ℝ) (H : ℝ) (C R F : Finset (Fin n)) (z q : Fin n)
    (hinv : Invariant (weight table p) (rankOf table p) r H
      (eligible (weight table p) (rankOf table p) r H) C R F z)
    (hstop : (Stop.outside q).Valid (rankOf table p)
      (eligible (weight table p) (rankOf table p) r H) C)
    (i : Fin n) (hi : i ∈ R) :
    material (table (p,q)).parts.prefixParts ⊆ material (table (p,i)).parts.prefixParts := by
  have hqz := outside_before_frontier (weight table p) (rankOf table p) r H _ C R F z q hinv hstop.1
  exact ranked_prefix_containment cost P cache hc table p baseline hcorrect hown q i
    (hqz.trans (hinv.allowed_above i hi))

end EnvyFreeResearch.Full.Chores.Frontier
