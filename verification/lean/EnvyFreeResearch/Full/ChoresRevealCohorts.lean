import EnvyFreeResearch.Full.ChoresFrontierOutcome
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Powerset

/-! Cross-root classification is computed from the actual scan outcomes.
Either one terminal type supplies |A|+1 roots, or an outside target keeps
at least floor((M-n(4^n+2^n))/n) roots. No scan-success certificate is an
input to this counting argument. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Reveal
open Frontier Equalizers
open scoped Classical BigOperators

abbrev TerminalClass (n : ℕ) := (Finset (Fin n) × Finset (Fin n)) ⊕ Finset (Fin n)

def TerminalClass.participants {n : ℕ} : TerminalClass n → Finset (Fin n)
  | .inl (A,_) => A
  | .inr A => A

theorem terminal_card (n : ℕ) : Fintype.card (TerminalClass n)=4^n+2^n := by
  simp only [TerminalClass,Fintype.card_sum,Fintype.card_prod,Fintype.card_finset,Fintype.card_fin]
  rw [← mul_pow]
  norm_num

def classify {n : ℕ} (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) (representative : Fin n → Fin n) : TerminalClass n ⊕ Fin n :=
  match scan table p r H C with
  | .outside q => .inr (representative q)
  | .atomic a => .inl (.inl (atomicParticipants (eligible (weight table p) (rankOf table p) r H)
      (rankOf table p) a,largeMask (weight table p) r H a))
  | .exhausted _ => .inl (.inr (eligible (weight table p) (rankOf table p) r H))

variable {n : ℕ} {Root : Type*} [Fintype Root] [DecidableEq Root]

def fiber (f : Root → TerminalClass n ⊕ Fin n) (label : TerminalClass n ⊕ Fin n) : Finset Root :=
  Finset.univ.filter (fun s => f s=label)

theorem fiber_sum (f : Root → TerminalClass n ⊕ Fin n) :
    Fintype.card Root =
      (∑ t : TerminalClass n, (fiber f (.inl t)).card)+(∑ q : Fin n, (fiber f (.inr q)).card) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset Root))
    (t := (Finset.univ : Finset (TerminalClass n ⊕ Fin n))) (f := f) (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.card_univ,Fintype.sum_sum_type,fiber] using h

theorem exists_ge_average (value : Fin n → ℕ) (p : Fin n) (b : ℕ)
    (h : n*b ≤ ∑ q, value q) : ∃ q, b ≤ value q := by
  by_contra hn
  push_neg at hn
  have hs : (∑ q, value q) < ∑ _q : Fin n, b :=
    Finset.sum_lt_sum (fun q _ => (hn q).le) ⟨p,Finset.mem_univ _,hn p⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  omega

theorem cohort_alternative (f : Root → TerminalClass n ⊕ Fin n) (p : Fin n) :
    (∃ t : TerminalClass n, t.participants.card+1 ≤ (fiber f (.inl t)).card) ∨
    ∃ q : Fin n, (Fintype.card Root-n*(4^n+2^n))/n ≤ (fiber f (.inr q)).card := by
  by_cases h : ∃ t : TerminalClass n, t.participants.card+1 ≤ (fiber f (.inl t)).card
  · exact Or.inl h
  · right
    have hf : ∀ t : TerminalClass n, (fiber f (.inl t)).card ≤ n := by
      intro t
      have hnot : ¬ t.participants.card+1 ≤ (fiber f (.inl t)).card := fun ht => h ⟨t,ht⟩
      have hcard : t.participants.card ≤ n := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ t.participants
      omega
    have hs : (∑ t : TerminalClass n, (fiber f (.inl t)).card) ≤ n*(4^n+2^n) := by
      calc
        _ ≤ ∑ _t : TerminalClass n, n := Finset.sum_le_sum (fun t _ => hf t)
        _ = n*(4^n+2^n) := by simp only [Finset.sum_const,Finset.card_univ,terminal_card,smul_eq_mul]; ring
    have htotal := fiber_sum f
    have hout : Fintype.card Root-n*(4^n+2^n) ≤ ∑ q : Fin n, (fiber f (.inr q)).card := by omega
    exact exists_ge_average (fun q => (fiber f (.inr q)).card) p _
      ((Nat.mul_div_le _ _).trans hout)

/-- Instantiation on the cached scanner, rather than a supplied collection
of terminal or outside correctness certificates. -/
theorem actual_cohort_alternative (tables : Root → Table n) (p : Fin n)
    (r : Fin n → ℝ) (H : ℝ) (C : Finset (Fin n)) (representative : Fin n → Fin n) :
    let f := fun s => classify (tables s) p r H C representative
    (∃ t : TerminalClass n, t.participants.card+1 ≤ (fiber f (.inl t)).card) ∨
    ∃ q : Fin n, (Fintype.card Root-n*(4^n+2^n))/n ≤ (fiber f (.inr q)).card :=
  cohort_alternative _ p

end EnvyFreeResearch.Full.Chores.Reveal
