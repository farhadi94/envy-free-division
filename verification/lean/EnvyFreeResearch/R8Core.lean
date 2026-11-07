import EnvyFreeResearch.R7Chores

/-!
# Round 8: physical finite-piece quota completion

The file proves a two-recipient three-parent construction and the implication
from supplied allocated quota allocations to full envy-freeness.  It does not
assert that the general quota allocations exist or can be found with bounded
ordinary queries.  Finite atoms represent disjoint physical records.
-/

noncomputable section

namespace EnvyFreeResearch.R8Core

open scoped BigOperators

section PieceCosts

variable {Atom Agent : Type*} [DecidableEq Atom]

def pieceCost (cost : Agent → Atom → ℝ) (i : Agent) (piece : Finset Atom) : ℝ :=
  ∑ x ∈ piece, cost i x

omit [DecidableEq Atom] in
theorem piece_cost_nonnegative (cost : Agent → Atom → ℝ)
    (hnonnegative : ∀ i x, 0 ≤ cost i x) (i : Agent) (piece : Finset Atom) :
    0 ≤ pieceCost cost i piece := by
  exact Finset.sum_nonneg (fun x _ => hnonnegative i x)

omit [DecidableEq Atom] in
theorem piece_cost_mono (cost : Agent → Atom → ℝ)
    (hnonnegative : ∀ i x, 0 ≤ cost i x) (i : Agent) (small large : Finset Atom)
    (hsubset : small ⊆ large) : pieceCost cost i small ≤ pieceCost cost i large := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x _ _ => hnonnegative i x)

theorem piece_cost_disjoint_union (cost : Agent → Atom → ℝ) (i : Agent)
    (A B : Finset Atom) (hdisjoint : Disjoint A B) :
    pieceCost cost i (A ∪ B) = pieceCost cost i A + pieceCost cost i B := by
  exact Finset.sum_union hdisjoint

/-- The recursive domain is the literal unused physical complement. -/
theorem literal_complement_coverage (parent allocated : Finset Atom) (h : allocated ⊆ parent) :
    allocated ∪ (parent \ allocated) = parent := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hx | ⟨hx, _⟩)
    · exact h hx
    · exact hx
  · intro hx
    by_cases hp : x ∈ allocated
    · exact Or.inl hp
    · exact Or.inr ⟨hx, hp⟩

theorem two_domain_coverage (X R Y Z : Finset Atom) (hY : Y ⊆ X) (hZ : Z ⊆ R) :
    (Y ∪ (X \ Y)) ∪ (Z ∪ (R \ Z)) = X ∪ R := by
  rw [literal_complement_coverage X Y hY, literal_complement_coverage R Z hZ]

end PieceCosts

section ThreeParents

variable {Atom : Type*} [DecidableEq Atom]

/-- The row-one equalization target fits inside the third parent. -/
theorem three_parent_target_fits (a b c : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) : 0 ≤ b-a ∧ b-a ≤ c := by
  constructor <;> linarith

/-- Two public bundles and their exact remainder are physically disjoint and exhaustive. -/
theorem three_parent_geometry (P₁ P₂ P₃ T : Finset Atom)
    (h12 : Disjoint P₁ P₂) (h13 : Disjoint P₁ P₃) (h23 : Disjoint P₂ P₃)
    (hT : T ⊆ P₃) :
    Disjoint (P₁ ∪ T) P₂ ∧
    Disjoint (P₁ ∪ T) (P₃ \ T) ∧
    Disjoint P₂ (P₃ \ T) ∧
    ((P₁ ∪ T) ∪ P₂) ∪ (P₃ \ T) = (P₁ ∪ P₂) ∪ P₃ := by
  have hT2 : Disjoint T P₂ := (h23.symm).mono_left hT
  have h1r : Disjoint P₁ (P₃ \ T) := h13.mono_right Finset.sdiff_subset
  have hTr : Disjoint T (P₃ \ T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hr
    exact (Finset.mem_sdiff.mp hr).2 hx
  have h2r : Disjoint P₂ (P₃ \ T) := h23.mono_right Finset.sdiff_subset
  refine ⟨Finset.disjoint_union_left.mpr ⟨h12, hT2⟩,
    Finset.disjoint_union_left.mpr ⟨h1r, hTr⟩, h2r, ?_⟩
  have heq := literal_complement_coverage P₃ T hT
  calc
    ((P₁ ∪ T) ∪ P₂) ∪ (P₃ \ T) = (P₁ ∪ P₂) ∪ (T ∪ (P₃ \ T)) := by
      ext x
      simp only [Finset.mem_union]
      tauto
    _ = _ := by rw [heq]

theorem three_parent_equal_cost (cost : Fin 2 → Atom → ℝ)
    (P₁ P₂ P₃ T : Finset Atom) (h13 : Disjoint P₁ P₃) (hT : T ⊆ P₃)
    (htarget : pieceCost cost 0 T = pieceCost cost 0 P₂ - pieceCost cost 0 P₁) :
    pieceCost cost 0 (P₁ ∪ T) = pieceCost cost 0 P₂ := by
  rw [piece_cost_disjoint_union cost 0 P₁ T (h13.mono_right hT), htarget]
  ring

/-- The second row chooses its cheaper bundle; the first row is indifferent. -/
theorem two_recipient_chooser (u v : Fin 2 → ℝ) (htie : u 0 = v 0) :
    (if u 1 ≤ v 1 then v 0 else u 0) ≤ (if u 1 ≤ v 1 then u 0 else v 0) ∧
    (if u 1 ≤ v 1 then u 1 else v 1) ≤ (if u 1 ≤ v 1 then v 1 else u 1) := by
  by_cases h : u 1 ≤ v 1
  · simp only [h, ite_true]
    exact ⟨htie.ge, trivial⟩
  · simp only [h, ite_false]
    exact ⟨htie.le, (lt_of_not_ge h).le⟩

/-- Each resulting public bundle retains a whole distinct original parent. -/
theorem three_parent_outsider_quota (cost : Unit → Atom → ℝ)
    (hnonnegative : ∀ i x, 0 ≤ cost i x) (P₁ P₂ T : Finset Atom) (quota : ℝ)
    (h1 : quota ≤ pieceCost cost () P₁) (h2 : quota ≤ pieceCost cost () P₂) :
    quota ≤ pieceCost cost () (P₁ ∪ T) ∧ quota ≤ pieceCost cost () P₂ := by
  exact ⟨h1.trans (piece_cost_mono cost hnonnegative () P₁ (P₁ ∪ T)
    Finset.subset_union_left), h2⟩

end ThreeParents

section QuotaCompletion

variable {Atom Agent : Type*} [DecidableEq Atom] [DecidableEq Agent]

/-- Separation and a soft quota imply the exact cross-domain payment inequality. -/
theorem quota_from_separation (alpha ownDomain oppositeDomain allocated : ℝ)
    (halpha : 0 < alpha) (hseparation : alpha*ownDomain ≤ oppositeDomain)
    (hquota : oppositeDomain/alpha ≤ allocated) : ownDomain ≤ allocated := by
  have h : oppositeDomain ≤ allocated*alpha := (div_le_iff₀ halpha).mp hquota
  nlinarith

def completedBundle (allocated recursive : Agent → Finset Atom) (i : Agent) : Finset Atom :=
  allocated i ∪ recursive i

/-- Within-group EF adds on literal disjoint pieces; cross-group EF follows from quotas. -/
theorem quota_completion_envy_free (cost : Agent → Atom → ℝ)
    (hnonnegative : ∀ i x, 0 ≤ cost i x) (group : Finset Agent)
    (X R : Finset Atom) (allocated recursive : Agent → Finset Atom)
    (hdisjoint : ∀ i, Disjoint (allocated i) (recursive i))
    (hplacement : ∀ i, completedBundle allocated recursive i ⊆ if i ∈ group then R else X)
    (hpartial : ∀ i j, (i ∈ group ↔ j ∈ group) →
      pieceCost cost i (allocated i) ≤ pieceCost cost i (allocated j))
    (hrecursive : ∀ i j, (i ∈ group ↔ j ∈ group) →
      pieceCost cost i (recursive i) ≤ pieceCost cost i (recursive j))
    (hquotaX : ∀ i ∈ group, ∀ j, j ∉ group →
      pieceCost cost i R ≤ pieceCost cost i (allocated j))
    (hquotaR : ∀ i, i ∉ group → ∀ j ∈ group,
      pieceCost cost i X ≤ pieceCost cost i (allocated j)) :
    ∀ i j, pieceCost cost i (completedBundle allocated recursive i) ≤
      pieceCost cost i (completedBundle allocated recursive j) := by
  intro i j
  by_cases hsame : i ∈ group ↔ j ∈ group
  · unfold completedBundle
    rw [piece_cost_disjoint_union cost i _ _ (hdisjoint i),
      piece_cost_disjoint_union cost i _ _ (hdisjoint j)]
    exact add_le_add (hpartial i j hsame) (hrecursive i j hsame)
  · by_cases hi : i ∈ group
    · have hj : j ∉ group := by intro hj; exact hsame ⟨fun _ => hj, fun _ => hi⟩
      have hplace : completedBundle allocated recursive i ⊆ R := by
        simpa only [hi, ite_true] using hplacement i
      calc
        _ ≤ pieceCost cost i R := piece_cost_mono cost hnonnegative i _ _ hplace
        _ ≤ pieceCost cost i (allocated j) := hquotaX i hi j hj
        _ ≤ _ := piece_cost_mono cost hnonnegative i _ _ Finset.subset_union_left
    · have hj : j ∈ group := by
        by_contra hj
        exact hsame ⟨fun h => False.elim (hi h), fun h => False.elim (hj h)⟩
      have hplace : completedBundle allocated recursive i ⊆ X := by
        simpa only [hi, ite_false] using hplacement i
      calc
        _ ≤ pieceCost cost i X := piece_cost_mono cost hnonnegative i _ _ hplace
        _ ≤ pieceCost cost i (allocated j) := hquotaR i hi j hj
        _ ≤ _ := piece_cost_mono cost hnonnegative i _ _ Finset.subset_union_left

omit [DecidableEq Agent] [DecidableEq Atom] in
/-- A quota below a whole-parent value survives adding any nonnegative extra material. -/
theorem whole_parent_implies_soft_quota (cost : Agent → Atom → ℝ)
    (hnonnegative : ∀ i x, 0 ≤ cost i x) (i : Agent) (whole bundle : Finset Atom)
    (hwhole : whole ⊆ bundle) (quota : ℝ) (hquota : quota ≤ pieceCost cost i whole) :
    quota ≤ pieceCost cost i bundle :=
  hquota.trans (piece_cost_mono cost hnonnegative i whole bundle hwhole)

end QuotaCompletion

end EnvyFreeResearch.R8Core
