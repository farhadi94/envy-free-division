import EnvyFreeResearch.Full.ChoresPackageGeometry

/-! Literal private complements and physical residue accounting. Repeated
resets are charged to the final union of immutable original atoms, not to
the number of times material was detached and reattached. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PackageGeometry
open Set MeasureTheory
open scoped Classical BigOperators

variable {Root Agent : Type*}

def Pieces.retained (G : Pieces Root Agent) (Y : Root → Agent → Set ℝ)
    (hsub : ∀ s p, Y s p ⊆ G.piece s p) (hm : ∀ s p, MeasurableSet (Y s p)) : Pieces Root Agent where
  piece := Y
  measurable := hm
  disjoint := fun a b hab => (G.disjoint hab).mono (hsub a.1 a.2) (hsub b.1 b.2)

def Pieces.material (G : Pieces Root Agent) : Set ℝ := ⋃ s, ⋃ p, G.piece s p
def Pieces.remainder (G : Pieces Root Agent) (Y : Root → Agent → Set ℝ) : Set ℝ :=
  ⋃ s, ⋃ p, G.piece s p \ Y s p

theorem Pieces.retained_disjoint_remainder (G : Pieces Root Agent) (Y : Root → Agent → Set ℝ)
    (hsub : ∀ s p, Y s p ⊆ G.piece s p) :
    Disjoint (⋃ s, ⋃ p, Y s p) (G.remainder Y) := by
  apply disjoint_iUnion_left.mpr
  intro s
  apply disjoint_iUnion_left.mpr
  intro p
  apply disjoint_iUnion_right.mpr
  intro t
  apply disjoint_iUnion_right.mpr
  intro q
  by_cases heq : (s,p) = (t,q)
  · have hs : s = t := congrArg Prod.fst heq
    have hp : p = q := congrArg Prod.snd heq
    subst t
    subst q
    exact disjoint_left.mpr (fun x hx hy => hy.2 hx)
  · exact (@G.disjoint (s,p) (t,q) heq).mono (hsub s p) sdiff_subset

theorem Pieces.retained_remainder_cover (G : Pieces Root Agent) (Y : Root → Agent → Set ℝ)
    (hsub : ∀ s p, Y s p ⊆ G.piece s p) :
    (⋃ s, ⋃ p, Y s p) ∪ G.remainder Y = G.material := by
  ext x
  simp only [Pieces.remainder,Pieces.material,mem_union,mem_iUnion,mem_sdiff]
  constructor
  · rintro (⟨s,p,hY⟩ | ⟨s,p,hP,hnot⟩)
    · exact ⟨s,p,hsub s p hY⟩
    · exact ⟨s,p,hP⟩
  · rintro ⟨s,p,hP⟩
    by_cases hY : x ∈ Y s p
    · exact Or.inl ⟨s,p,hY⟩
    · exact Or.inr ⟨s,p,hP,hY⟩

theorem Pieces.assigned_remainder_cover [Fintype Root] [Fintype Agent]
    (G : Pieces Root Agent) (Y : Root → Agent → Set ℝ)
    (hsub : ∀ s p, Y s p ⊆ G.piece s p) (hm : ∀ s p, MeasurableSet (Y s p))
    (owner : Root → Equiv.Perm Agent) :
    (⋃ i, (G.retained Y hsub hm).bundle owner i) ∪ G.remainder Y = G.material := by
  rw [(G.retained Y hsub hm).bundle_cover owner]
  exact G.retained_remainder_cover Y hsub

theorem Pieces.private_complement_subset (G : Pieces Root Agent) (Y : Root → Agent → Set ℝ)
    (s : Root) (p : Agent) : G.piece s p \ Y s p ⊆ G.piece s p := sdiff_subset

theorem Pieces.remainder_supported {Atom : Type*} (G : Pieces Root Agent)
    (Y : Root → Agent → Set ℝ) (atoms : Atom → Set ℝ)
    (hpassed : ∀ s p, G.piece s p \ Y s p ⊆ ⋃ a, atoms a) :
    G.remainder Y ⊆ ⋃ a, atoms a :=
  iUnion_subset (fun s => iUnion_subset (hpassed s))

/-- Final physical-union bound. Only the finite original atom family is
counted; overlaps and earlier repeated resets do not add charges. -/
theorem physical_residue_bounds {Atom : Type*} [Fintype Atom]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (outer released : Set ℝ) (atoms : Atom → Set ℝ)
    (H : ℝ) (hH : 0 < H) (hsupport : released ⊆ ⋃ a, atoms a)
    (hsmall : ∀ a, μ.real (atoms a) ≤ μ.real outer/H) :
    μ.real outer ≤ μ.real (outer ∪ released) ∧
    μ.real (outer ∪ released) ≤ (1+(Fintype.card Atom : ℝ)/H)*μ.real outer := by
  have hsum : (∑ a, μ.real (atoms a)) ≤ ∑ _a : Atom, μ.real outer/H :=
    Finset.sum_le_sum (fun a _ => hsmall a)
  refine ⟨measureReal_mono subset_union_left,?_⟩
  calc
    μ.real (outer ∪ released) ≤ μ.real outer+μ.real released := measureReal_union_le _ _
    _ ≤ μ.real outer+μ.real (⋃ a, atoms a) :=
      add_le_add le_rfl (measureReal_mono (μ := μ) hsupport)
    _ ≤ μ.real outer+∑ a, μ.real (atoms a) :=
      add_le_add le_rfl (measureReal_iUnion_fintype_le (μ := μ) atoms)
    _ ≤ μ.real outer+∑ _a : Atom, μ.real outer/H :=
      add_le_add le_rfl hsum
    _ = (1+(Fintype.card Atom : ℝ)/H)*μ.real outer := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end EnvyFreeResearch.Full.Chores.PackageGeometry
