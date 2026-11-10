import EnvyFreeResearch.Full.RefinedUpperPeelingLocalEdit

/-! A local grid deletion controls both partial-cell linear functionals.
The statement permits arbitrary normalizations chosen after peeling. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperRepresentativeSupply
open scoped Classical
variable {Cell Parent Row : Type*} [DecidableEq Parent]

/-- If a local split/merge changes no selected cell and neither of the
final maximum-determinant witnesses, each original partial cell has signed
mass at most twice the largest surviving merged-grid cell mass. -/
theorem local_edit_partial_control (values : Row → Cell → ℝ)
    (hnonneg : ∀ r c, 0 ≤ values r c) (parent : Cell → Parent)
    (cells cells' : List Cell) (jobs : List (Row × Row)) (removed final final' : Finset Parent)
    (pairs pairs' : List (Cell × Cell)) (Q : Parent) (keep keep' : Cell → Bool)
    (hoff : cells.filter keep = cells'.filter keep')
    (hlocal : ∀ c, keep' c = false → parent c = Q)
    (hexec : run values parent cells jobs removed = some (pairs,final))
    (hexec' : run values parent cells' jobs removed = some (pairs',final'))
    (hQ' : Q ∉ final')
    (hkeep : ∀ pair ∈ pairs, keep pair.1 = true ∧ keep pair.2 = true)
    (i j : Row) (F G E : Cell)
    (hw : select (values i) (values j) (available parent final cells) = some (F,G))
    (hF : keep F = true) (hG : keep G = true)
    (hE : E ∈ cells) (hEQ : parent E = Q)
    (u v A : ℝ)
    (hA : ∀ c ∈ cells', parent c ∉ final' → |u*values i c-v*values j c| ≤ A) :
    |u*values i E-v*values j E| ≤ 2*A := by
  have hsame := local_edit_agrees values parent cells cells' jobs removed final final' pairs pairs'
    Q keep keep' hoff hlocal hexec hexec' hQ' hkeep
  have hnonempty : available parent final cells ≠ [] := by
    intro he
    simp [select,RefinedUpperWitnessSelector.select,he] at hw
  obtain ⟨F',G',hw',hF',hG',hb⟩ := select_spec (values i) (values j)
    (available parent final cells) hnonempty (fun c _ => hnonneg i c) (fun c _ => hnonneg j c)
  have heq : (F',G') = (F,G) := Option.some.inj (hw'.symm.trans hw)
  cases heq
  have hmF := (mem_available parent final cells F).mp hF'
  have hmG := (mem_available parent final cells G).mp hG'
  have hcF : F ∈ cells' := by
    have hm : F ∈ cells.filter keep := List.mem_filter.mpr ⟨hmF.1,hF⟩
    rw [hoff] at hm
    exact (List.mem_filter.mp hm).1
  have hcG : G ∈ cells' := by
    have hm : G ∈ cells.filter keep := List.mem_filter.mpr ⟨hmG.1,hG⟩
    rw [hoff] at hm
    exact (List.mem_filter.mp hm).1
  have hnF : parent F ∉ final' := by simpa [← hsame.2] using hmF.2
  have hnG : parent G ∉ final' := by simpa [← hsame.2] using hmG.2
  have hnE : parent E ∉ final := by simpa [hEQ,hsame.2] using hQ'
  have hbE := hb E ((mem_available parent final cells E).mpr ⟨hE,hnE⟩) u v
  exact hbE.trans (mul_le_mul_of_nonneg_left (max_le (hA F hcF hnF) (hA G hcG hnG)) (by norm_num))

end EnvyFreeResearch.Full.RefinedUpperPeeling
