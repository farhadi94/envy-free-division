import EnvyFreeResearch.Full.ChoresFrontierCache
import EnvyFreeResearch.Full.ChoresFrontierAtomic

/-! The reveal outcome and offered material are computed solely from the
immutable original table and the current finite component. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers
open scoped Classical

variable {n : ℕ}

inductive Outcome (n : ℕ)
  | outside : Fin n → Outcome n
  | atomic : Fin n → Outcome n
  | exhausted : Fin n → Outcome n

def scan (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ) (C : Finset (Fin n)) : Outcome n :=
  let s := stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p
  match largestBad (weight table p) r H (rankOf table p s.agent) with
  | some a => .atomic a
  | none => match s with
    | .outside q => .outside q
    | .exhausted q => .exhausted q

def Outcome.offer (table : Table n) (p : Fin n) (cache : List (Parent n)) : Outcome n → List (Parent n)
  | .outside q | .exhausted q => (table (p,q)).parts.suffixParts
  | .atomic a => boundaryCache table p cache a.castSucc

def Outcome.boundary (table : Table n) (p : Fin n) : Outcome n → ℕ
  | .outside q | .exhausted q => rankOf table p q
  | .atomic a => a.val

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
  (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
  (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
  (hown : (table (p,p)).parts.prefixParts=cache)

include hc hcorrect hown

theorem offer_material (out : Outcome n) :
    material (out.offer table p cache)=atomMaterial P ((atomsFromTable table p).drop (out.boundary table p)) := by
  cases out with
  | outside q | exhausted q =>
    exact (suffix_material_rank cost P cache hc table p baseline hcorrect hown q).symm
  | atomic a => exact boundary_cache_material cost P cache hc table p baseline hcorrect hown a.castSucc

theorem offer_cache_valid (out : Outcome n) :
    CacheValid (measureProfile cost) (material (out.offer table p cache)) (out.offer table p cache) := by
  cases out with
  | outside q | exhausted q =>
    exact ⟨(hcorrect q).2.2.1.1,(hcorrect q).2.2.1.2.1,rfl⟩
  | atomic a =>
    have h := boundary_cache_valid cost P cache hc table p baseline hcorrect hown a.castSucc
    exact ⟨h.1,h.2.1,rfl⟩

theorem offer_value (out : Outcome n) (i : Fin n) :
    (cost i).real (material (out.offer table p cache))=tailCost (weight table p) i (out.boundary table p) := by
  rw [offer_material cost P cache hc table p baseline hcorrect hown,weight_tail_sum]
  obtain ⟨hs,hd,_,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  have hP : MeasurableSet P := by rw [← hc.2.2]; exact material_measurable _
  exact atomMaterial_value cost P hP _ (fun a ha => hs a (List.mem_of_mem_drop ha)) hd.drop i

/-- The physical specification uses original measure costs and literal
material. Eligibility and atom masks are computed from the recorded table. -/
def PhysicalCorrect (r : Fin n → ℝ) (H : ℝ) (C : Finset (Fin n)) (out : Outcome n) : Prop :=
  let E := eligible (weight table p) (rankOf table p) r H
  let V := material (out.offer table p cache)
  let gap := fun i => (cost i).real P-baseline i
  match out with
  | .outside q =>
      q ∈ E ∧ q ∉ C ∧
      (∀ a : Fin n, rankOf table p q ≤ a.val → Small (weight table p) r H a) ∧
      (∀ i, i ∉ C → (cost i).real V ≤ gap i) ∧
      ∀ i, (cost i).real V ≤ (n : ℝ)*r i/H
  | .atomic a =>
      let A := atomicParticipants E (rankOf table p) a
      let B := largeMask (weight table p) r H a
      let F := ((atomsFromTable table p).get (Fin.cast (atoms_from_table_length table p).symm a)).domain P
      p ∈ A ∧ A ⊆ C ∧ A ≠ Finset.univ ∧ B.Nonempty ∧ B ≠ Finset.univ ∧
      F ⊆ V ∧
      (∀ i ∈ A, gap i ≤ (cost i).real V) ∧
      (∀ i, i ∉ A → (cost i).real V ≤ gap i) ∧
      (∀ i ∈ B, H*r i ≤ (cost i).real F) ∧
      (∀ i, i ∉ B → (cost i).real V ≤ (n : ℝ)*r i/H) ∧
      ∀ b : Fin n, a < b → Small (weight table p) r H b
  | .exhausted q =>
      E ⊆ C ∧
      (∀ a : Fin n, rankOf table p q ≤ a.val → Small (weight table p) r H a) ∧
      (∀ i ∈ E, gap i ≤ (cost i).real V) ∧
      (∀ i, i ∉ E → (cost i).real V ≤ gap i) ∧
      (∀ i, i ∉ E → H*r i ≤ gap i) ∧
      (∀ i, (cost i).real V ≤ (n : ℝ)*r i/H) ∧
      ∀ i, i ∉ E → (H-(n : ℝ)/H)*r i ≤ gap i-(cost i).real V

end EnvyFreeResearch.Full.Chores.Frontier
