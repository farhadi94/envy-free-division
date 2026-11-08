import EnvyFreeResearch.Full.PhysicalReflection

/-!
Finite piecewise-constant densities, with explicit finite breakpoint
witnesses. Equal comparisons with every breakpoint specify the open
interval cells and singleton boundary cells of a finite partition.
-/

namespace EnvyFreeResearch.Full.FiniteStepDensity
open Set MixedDensity PhysicalReflection
open scoped Classical

def SameCell (points : Finset ℝ) (x y : ℝ) : Prop :=
  ∀ b ∈ points, (x ≤ b ↔ y ≤ b) ∧ (x < b ↔ y < b)

def FiniteStep (f : ℝ → ℝ) : Prop :=
  ∃ points : Finset ℝ, ∀ x y, SameCell points x y → f x = f y

theorem SameCell.mono {a b : Finset ℝ} (hab : a ⊆ b) {x y : ℝ}
    (h : SameCell b x y) : SameCell a x y := fun p hp => h p (hab hp)

theorem sameCell_mem_Ioc {points : Finset ℝ} {a b x y : ℝ}
    (ha : a ∈ points) (hb : b ∈ points) (h : SameCell points x y) :
    x ∈ Ioc a b ↔ y ∈ Ioc a b := by
  have hl := (h a ha).1
  have hr := (h b hb).1
  constructor
  · rintro ⟨hax,hxb⟩
    refine ⟨?_,hr.mp hxb⟩
    by_contra hn
    have hxa := hl.mpr (le_of_not_gt hn)
    linarith
  · rintro ⟨hay,hyb⟩
    refine ⟨?_,hr.mpr hyb⟩
    by_contra hn
    have hya := hl.mp (le_of_not_gt hn)
    linarith

theorem finiteStep_const (c : ℝ) : FiniteStep (fun _ => c) := ⟨∅,fun _ _ _ => rfl⟩

theorem FiniteStep.add {f g : ℝ → ℝ} (hf : FiniteStep f) (hg : FiniteStep g) :
    FiniteStep (fun x => f x + g x) := by
  obtain ⟨B,hB⟩ := hf
  obtain ⟨C,hC⟩ := hg
  refine ⟨B ∪ C,?_⟩
  intro x y hxy
  change f x + g x = f y + g y
  rw [hB x y (hxy.mono Finset.subset_union_left),hC x y (hxy.mono Finset.subset_union_right)]

theorem FiniteStep.indicator {f : ℝ → ℝ} (hf : FiniteStep f) (a b : ℝ) :
    FiniteStep ((Ioc a b).indicator f) := by
  obtain ⟨B,hB⟩ := hf
  refine ⟨B ∪ {a,b},?_⟩
  intro x y hxy
  have hmem := sameCell_mem_Ioc (points := B ∪ {a,b}) (a := a) (b := b)
    (by simp) (by simp) hxy
  by_cases hx : x ∈ Ioc a b
  · rw [indicator_of_mem hx,indicator_of_mem (hmem.mp hx)]
    exact hB x y (hxy.mono Finset.subset_union_left)
  · rw [indicator_of_notMem hx,indicator_of_notMem (fun hy => hx (hmem.mpr hy))]

theorem FiniteStep.reflect {f : ℝ → ℝ} (hf : FiniteStep f) :
    FiniteStep (fun x => f (1-x)) := by
  obtain ⟨B,hB⟩ := hf
  refine ⟨B.image (fun b => 1-b),?_⟩
  intro x y hxy
  apply hB
  intro b hb
  have h := hxy (1-b) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have hxl : 1-x ≤ b ↔ ¬ x < 1-b := by constructor <;> intro h <;> linarith
  have hyl : 1-y ≤ b ↔ ¬ y < 1-b := by constructor <;> intro h <;> linarith
  have hxs : 1-x < b ↔ ¬ x ≤ 1-b := by constructor <;> intro h <;> linarith
  have hys : 1-y < b ↔ ¬ y ≤ 1-b := by constructor <;> intro h <;> linarith
  exact ⟨by rw [hxl,hyl,h.2],by rw [hxs,hys,h.1]⟩

theorem cell_finiteStep (a b d : ℝ) : FiniteStep (Row.cell a b d).density :=
  (finiteStep_const d).indicator a b

theorem add_finiteStep (R S : Row) (hR : FiniteStep R.density) (hS : FiniteStep S.density) :
    FiniteStep (R.add S).density := hR.add hS

theorem prefix_finiteStep (R : Row) (l : ℝ) (hR : FiniteStep R.density) :
    FiniteStep (R.prefixRow l).density := hR.indicator 0 l

theorem rebuilt_finiteStep (R : Row) (l h d : ℝ) (hR : FiniteStep R.density) :
    FiniteStep (R.rebuilt l h d).density :=
  (prefix_finiteStep R l hR).add ((cell_finiteStep l h d).add (cell_finiteStep h 1 _))

theorem reflectRow_finiteStep (R : Row) (hR : FiniteStep R.density) :
    FiniteStep (reflectRow R).density := hR.reflect

end EnvyFreeResearch.Full.FiniteStepDensity
