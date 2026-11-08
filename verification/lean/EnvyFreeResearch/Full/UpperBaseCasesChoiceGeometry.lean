import EnvyFreeResearch.Full.UpperBaseCasesChoice

/-! Literal conservation and disjointness of the actual cached two-agent
choice, with empty pieces for every frozen recipient. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperBaseCases
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

theorem choice_pairwise (chores : Bool) (left right : State n) (cutter chooser : Fin n)
    (hdis : Disjoint (domain left.cells) (domain right.cells)) :
    Pairwise (fun i j => Disjoint (domain (choice chores left right cutter chooser i).cells)
      (domain (choice chores left right cutter chooser j).cells)) := by
  intro i j hij
  unfold choice
  split_ifs <;> simp_all [empty,domain,disjoint_comm]

theorem choice_complete (chores : Bool) (left right : State n) (cutter chooser : Fin n)
    (hne : chooser ≠ cutter) :
    (⋃ j, domain (choice chores left right cutter chooser j).cells) =
      domain left.cells ∪ domain right.cells := by
  ext x
  simp only [mem_iUnion,mem_union]
  constructor
  · rintro ⟨j,hj⟩
    unfold choice at hj
    split_ifs at hj <;> first | exact Or.inl hj | exact Or.inr hj | exact False.elim hj
  · intro hx
    by_cases h : chooseLeft chores left right chooser
    · rcases hx with hl | hr
      · exact ⟨chooser,by simpa [choice,h,hne] using hl⟩
      · exact ⟨cutter,by simpa [choice,h] using hr⟩
    · rcases hx with hl | hr
      · exact ⟨cutter,by simpa [choice,h] using hl⟩
      · exact ⟨chooser,by simpa [choice,h,hne] using hr⟩

theorem choice_frozen (chores : Bool) (left right : State n) (cutter chooser j : Fin n)
    (hj : j ∉ ({cutter,chooser} : Set (Fin n))) :
    choice chores left right cutter chooser j = empty left.history := by
  have hc : j ≠ cutter := fun h => hj (by simp [h])
  have hh : j ≠ chooser := fun h => hj (by simp [h])
  simp [choice,hc,hh]

theorem choice_history (chores : Bool) (left right : State n) (cutter chooser j : Fin n)
    (hh : right.history = left.history) :
    (choice chores left right cutter chooser j).history = left.history := by
  unfold choice
  split_ifs <;> first | exact hh | rfl

end EnvyFreeResearch.Full.UpperBaseCases
