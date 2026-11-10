import EnvyFreeResearch.Full.RefinedUpperStabilityProcedure

/-! The concrete Borel protection vector contains every witness endpoint. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperRepresentativeSupply
open scoped Classical
variable {Cell Parent Row : Type*} [DecidableEq Parent]

lemma run_length (values : Row → Cell → ℝ) (parent : Cell → Parent) (cells : List Cell)
    (jobs : List (Row × Row)) (removed final : Finset Parent) (pairs : List (Cell × Cell))
    (hexec : run values parent cells jobs removed = some (pairs,final)) : pairs.length = jobs.length := by
  induction jobs generalizing removed pairs final with
  | nil =>
    have heq : ([],removed) = (pairs,final) := by simpa only [run,Option.some.injEq] using hexec
    cases heq
    rfl
  | cons job jobs ih =>
    cases hs : select (values job.1) (values job.2) (available parent removed cells) with
    | none => simp [run,hs] at hexec
    | some pair =>
      cases ht : run values parent cells jobs (addParents parent pair removed) with
      | none => simp [run,hs,ht] at hexec
      | some result =>
        rcases result with ⟨tail,final'⟩
        have heq : (pair::tail,final') = (pairs,final) := by
          simpa only [run,hs,Option.bind_some,ht,Option.map_some,Option.some.injEq] using hexec
        cases heq
        simp only [List.length_cons,ih _ _ _ ht]

variable {a M : ℕ}

lemma protectedPairs_length (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs finalJobs : List (Row × Row)) (points : Fin (M+2) → ℝ)
    (pairs : List (Fin (M+1) × Fin (M+1))) (final : Finset (Fin (a+1)))
    (hexec : pointRun F coarse jobs points = some (pairs,final)) :
    (protectedPairs F coarse jobs finalJobs points).length = jobs.length+finalJobs.length := by
  have hl := run_length (pointValues F points) (pointParents coarse points) _ jobs ∅ final pairs hexec
  simp [protectedPairs,pointResult,hexec,hl]

/-- Every endpoint of every protected selected pair appears literally among
the fixed-length endpoint procedure outputs. No abstract coverage certificate
is assumed. -/
theorem endpointProcedure_pair_covered (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs finalJobs : List (Row × Row)) (points : Fin (M+2) → ℝ)
    (hlen : (protectedPairs F coarse jobs finalJobs points).length ≤ jobs.length+finalJobs.length)
    (pair : Fin (M+1) × Fin (M+1)) (hp : pair ∈ protectedPairs F coarse jobs finalJobs points)
    (z : ℝ) (hz : z = points pair.1.castSucc ∨ z = points pair.1.succ ∨
      z = points pair.2.castSucc ∨ z = points pair.2.succ) :
    ∃ k, endpointProcedure F coarse jobs finalJobs points k = z := by
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hp
  have hjN : j < jobs.length+finalJobs.length := hj.trans_le hlen
  have hget : (protectedPairs F coarse jobs finalJobs points).getD j (0,0) = pair := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    exact he
  have hformula (d : ℕ) (hd : d < 4) :
      endpointProcedure F coarse jobs finalJobs points ⟨4*j+d,by omega⟩ =
        if d%2 = 0 then points (if d < 2 then pair.1 else pair.2).castSucc
        else points (if d < 2 then pair.1 else pair.2).succ := by
    have hdiv : (4*j+d)/4 = j := by omega
    have hmod4 : (4*j+d)%4 = d := by omega
    have hmod2 : (4*j+d)%2 = d%2 := by omega
    simp only [endpointProcedure,hdiv,hmod4,hmod2,hget]
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨⟨4*j,by omega⟩,by simpa using hformula 0 (by omega)⟩
  · exact ⟨⟨4*j+1,by omega⟩,by simpa using hformula 1 (by omega)⟩
  · exact ⟨⟨4*j+2,by omega⟩,by simpa using hformula 2 (by omega)⟩
  · exact ⟨⟨4*j+3,by omega⟩,by simpa using hformula 3 (by omega)⟩

/-- An uncharged test point avoids every selected and final witness endpoint
on the actual successful run. The coverage count is proved by the run. -/
theorem uncharged_protected_endpoints (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs finalJobs : List (Row × Row)) (points : Fin (M+2) → ℝ)
    (pairs : List (Fin (M+1) × Fin (M+1))) (final : Finset (Fin (a+1)))
    (hexec : pointRun F coarse jobs points = some (pairs,final))
    (test : ℝ) (huncharged : ∀ k, endpointProcedure F coarse jobs finalJobs points k ≠ test)
    (pair : Fin (M+1) × Fin (M+1)) (hp : pair ∈ protectedPairs F coarse jobs finalJobs points) :
    points pair.1.castSucc ≠ test ∧ points pair.1.succ ≠ test ∧
      points pair.2.castSucc ≠ test ∧ points pair.2.succ ≠ test := by
  have hlen := (protectedPairs_length F coarse jobs finalJobs points pairs final hexec).le
  have hall (z : ℝ) (hz : z = points pair.1.castSucc ∨ z = points pair.1.succ ∨
      z = points pair.2.castSucc ∨ z = points pair.2.succ) : z ≠ test := by
    obtain ⟨k,hk⟩ := endpointProcedure_pair_covered F coarse jobs finalJobs points hlen pair hp z hz
    intro ht
    exact huncharged k (hk.trans ht)
  exact ⟨hall _ (Or.inl rfl),hall _ (Or.inr (Or.inl rfl)),
    hall _ (Or.inr (Or.inr (Or.inl rfl))),hall _ (Or.inr (Or.inr (Or.inr rfl)))⟩

end EnvyFreeResearch.Full.RefinedUpperPeeling
