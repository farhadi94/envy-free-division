import EnvyFreeResearch.Full.RefinedUpperPeelingRecorded

/-! Exact relabeling of the implemented selector and peeling loop.
The relabeling need not be injective: duplicate null interval labels are
permitted and retain their list order. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperWitnessSelector
open RefinedUpperDeterminant
open scoped Classical

lemma argmax_map {A B Key : Type*} [LinearOrder Key] (f : A → B) (score : B → Key) (xs : List A) :
    (xs.map f).argmax score = (xs.argmax (score ∘ f)).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.map_cons,List.argmax_cons,ih,List.argmax_cons]
    cases h : xs.argmax (score ∘ f) with
    | none => rfl
    | some b =>
      simp only [Option.map_some,Function.comp_apply]
      by_cases hs : score (f a) < score (f b) <;> simp [hs]

lemma product_map {A B : Type*} (f : A → B) (xs ys : List A) :
    (xs.map f) ×ˢ (ys.map f) = (xs ×ˢ ys).map (fun p => (f p.1,f p.2)) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.product_cons,ih,List.map_map,Function.comp_def]

/-- Physical interval relabeling commutes with deterministic tie breaking. -/
theorem select_map {A B : Type*} (f : A → B) (x : B → Vec) (xs : List A) :
    select x (xs.map f) = (select (x ∘ f) xs).map (fun p => (f p.1,f p.2)) := by
  unfold select
  rw [product_map,argmax_map]
  rfl

end EnvyFreeResearch.Full.RefinedUpperWitnessSelector

namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperRepresentativeSupply
open scoped Classical
variable {A B Parent Row : Type*} [DecidableEq Parent]

lemma available_map (f : A → B) (parent : B → Parent) (removed : Finset Parent) (cells : List A) :
    available parent removed (cells.map f) = (available (parent ∘ f) removed cells).map f := by
  simp only [available,List.filter_map,List.map_filter,Function.comp_def]

/-- The complete finite implementation transports to common physical labels,
including its final parent set and every selected pair. -/
theorem run_map (f : A → B) (values : Row → B → ℝ) (parent : B → Parent)
    (cells : List A) (jobs : List (Row × Row)) (removed : Finset Parent) :
    run values parent (cells.map f) jobs removed =
      (run (fun r => values r ∘ f) (parent ∘ f) cells jobs removed).map
        (fun result => (result.1.map (fun p => (f p.1,f p.2)),result.2)) := by
  induction jobs generalizing removed with
  | nil => rfl
  | cons job jobs ih =>
    rw [run,available_map]
    have hs : select (values job.1) (values job.2)
        ((available (parent ∘ f) removed cells).map f) =
        (select (values job.1 ∘ f) (values job.2 ∘ f)
          (available (parent ∘ f) removed cells)).map (fun p => (f p.1,f p.2)) :=
      RefinedUpperWitnessSelector.select_map f (fun c => (values job.1 c,values job.2 c)) _
    rw [hs]
    cases hc : select (values job.1 ∘ f) (values job.2 ∘ f)
      (available (parent ∘ f) removed cells) with
    | none => simp [run,hc]
    | some p =>
      simp only [Option.map_some,Option.bind_some]
      rw [ih]
      have hp : addParents parent (f p.1,f p.2) removed = addParents (parent ∘ f) p removed := rfl
      rw [hp]
      cases ht : run (fun r => values r ∘ f) (parent ∘ f) cells jobs
          (addParents (parent ∘ f) p removed) <;> simp [run,hc,ht]

end EnvyFreeResearch.Full.RefinedUpperPeeling
