import EnvyFreeResearch.Full.ChoresRevealCohorts

/-! Concrete deterministic selection of the next root cohort. The first
abundant terminal class takes exactly |A|+1 roots; otherwise an actual
largest outside target class is retained. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Reveal
open scoped Classical

variable {n : ℕ} {Root : Type*} [Fintype Root] [DecidableEq Root]

def firstAbundant (f : Root → TerminalClass n ⊕ Fin n) : Option (TerminalClass n) :=
  Finset.univ.toList.find? (fun t => decide (t.participants.card+1 ≤ (fiber f (.inl t)).card))

inductive Choice (n : ℕ) (Root : Type*)
  | terminal : TerminalClass n → List Root → Choice n Root
  | outside : Fin n → List Root → Choice n Root

def choose (f : Root → TerminalClass n ⊕ Fin n) (p : Fin n) : Choice n Root :=
  match firstAbundant f with
  | some t => .terminal t ((fiber f (.inl t)).toList.take (t.participants.card+1))
  | none =>
      let q := (Finset.univ.toList.argmax (fun q : Fin n => (fiber f (.inr q)).card)).getD p
      .outside q (fiber f (.inr q)).toList

def Choice.Correct (f : Root → TerminalClass n ⊕ Fin n) : Choice n Root → Prop
  | .terminal t roots => roots.Nodup ∧ roots.length=t.participants.card+1 ∧
      ∀ s ∈ roots, f s=.inl t
  | .outside q roots => roots.Nodup ∧
      (Fintype.card Root-n*(4^n+2^n))/n ≤ roots.length ∧
      ∀ s ∈ roots, f s=.inr q

theorem choose_correct (f : Root → TerminalClass n ⊕ Fin n) (p : Fin n) :
    (choose f p).Correct f := by
  unfold choose
  cases hf : firstAbundant f with
  | some t =>
    have hlarge : t.participants.card+1 ≤ (fiber f (.inl t)).card := by
      simpa only [decide_eq_true_eq] using List.find?_some hf
    refine ⟨(Finset.nodup_toList _).take,?_,?_⟩
    · simp only [List.length_take,Finset.length_toList,Nat.min_eq_left hlarge]
    · intro s hs
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp (List.mem_of_mem_take hs))).2
  | none =>
    have habsent : ¬ ∃ t : TerminalClass n, t.participants.card+1 ≤ (fiber f (.inl t)).card := by
      rintro ⟨t,ht⟩
      have hn := List.find?_eq_none.mp hf t (by simp)
      exact hn (by simpa only [decide_eq_true_eq] using ht)
    obtain ⟨q',hq'⟩ := (cohort_alternative f p).resolve_left habsent
    cases hm : Finset.univ.toList.argmax (fun q : Fin n => (fiber f (.inr q)).card) with
    | none =>
      have hempty := List.argmax_eq_none.mp hm
      have hp : p ∈ (Finset.univ : Finset (Fin n)).toList := by simp
      rw [hempty] at hp
      exact (List.not_mem_nil hp).elim
    | some q =>
      have hmax : (fiber f (.inr q')).card ≤ (fiber f (.inr q)).card :=
        List.le_of_mem_argmax (f := fun q : Fin n => (fiber f (.inr q)).card)
          (show q' ∈ (Finset.univ : Finset (Fin n)).toList from by simp) (by simp [hm])
      refine ⟨Finset.nodup_toList _,?_,?_⟩
      · simpa only [Option.getD_some,Finset.length_toList] using hq'.trans hmax
      · intro s hs
        exact (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2

def actualChoice (tables : Root → Equalizers.Table n) (p : Fin n)
    (r : Fin n → ℝ) (H : ℝ) (C : Finset (Fin n)) (representative : Fin n → Fin n) : Choice n Root :=
  choose (fun s => classify (tables s) p r H C representative) p

theorem actual_choice_correct (tables : Root → Equalizers.Table n) (p : Fin n)
    (r : Fin n → ℝ) (H : ℝ) (C : Finset (Fin n)) (representative : Fin n → Fin n) :
    (actualChoice tables p r H C representative).Correct
      (fun s => classify (tables s) p r H C representative) :=
  choose_correct _ p

end EnvyFreeResearch.Full.Chores.Reveal
