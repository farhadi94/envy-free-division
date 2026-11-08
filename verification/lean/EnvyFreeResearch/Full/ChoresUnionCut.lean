import EnvyFreeResearch.Full.ChoresUnionGeometry

/-! An actual ordinary-query implementation of prefix cutting on a cached
finite union. Scanning cached components is free; at most one component is
cut, and every observer's new value is recorded. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram

structure Split (n : ℕ) where
  prefixParts : List (Parent n)
  suffixParts : List (Parent n)

def splitProgram {n : ℕ} (c : Fin n) :
    ℝ → List (Parent n) → Program (Query (Fin n)) ℝ (Split n)
  | _, [] => .returned ⟨[],[]⟩
  | t, p :: ps =>
    if t = 0 then .returned ⟨[],p::ps⟩
    else if p.value c ≤ t then
      (splitProgram c (t-p.value c) ps).bind
        (fun out => .returned ⟨p::out.prefixParts,out.suffixParts⟩)
    else (endpointProgram c p.left p.right t).bind
      (fun record => .returned
        ⟨[leftPart p record.point record.value],rightPart p record.point record.value::ps⟩)

/-- The physical prefix has the exact target cost and exact cached values
for all observers. Every call uses the full enclosing adaptive history. -/
theorem split_program_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (ps : List (Parent n)) (hp : Valid P ps)
    (t : ℝ) (ht : 0 ≤ t) (htop : t ≤ cachedValue ps c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Split n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (splitProgram c t ps) prior out trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      PrefixSplit ps out.prefixParts out.suffixParts ∧
      Valid P out.prefixParts ∧ Valid P out.suffixParts ∧ cachedValue out.prefixParts c = t := by
  classical
  induction ps generalizing t prior with
  | nil =>
    have ht0 : t = 0 := le_antisymm htop ht
    exact ⟨⟨[],[]⟩,[],Executes.returned _ _,Nat.zero_le _,by simp,
      PrefixSplit.zero [],trivial,trivial,ht0.symm⟩
  | cons p ps ih =>
    obtain ⟨hp,hps⟩ := hp
    by_cases ht0 : t = 0
    · refine ⟨⟨[],p::ps⟩,[],?_,Nat.zero_le _,by simp,
        PrefixSplit.zero _,trivial,⟨hp,hps⟩,ht0.symm⟩
      simpa only [splitProgram,ite_eq_left ht0] using
        (Executes.returned (oracle := oracle) (⟨[],p::ps⟩ : Split n) prior)
    · by_cases hwhole : p.value c ≤ t
      · have hrest : 0 ≤ t-p.value c := sub_nonneg.mpr hwhole
        have hrest_top : t-p.value c ≤ cachedValue ps c := by
          change t ≤ p.value c+cachedValue ps c at htop
          linarith
        obtain ⟨out,trace,hexec,hlen,hcuts,hsplit,hvalidpre,hvalidsuf,hvalue⟩ :=
          ih hps (t-p.value c) hrest hrest_top prior
        refine ⟨⟨p::out.prefixParts,out.suffixParts⟩,trace,?_,hlen,hcuts,
          PrefixSplit.cons p hsplit,⟨hp,hvalidpre⟩,hvalidsuf,?_⟩
        · simpa only [splitProgram,ite_eq_right ht0,ite_eq_left hwhole,List.append_nil] using
            hexec.bind (fun out => Program.returned (⟨p::out.prefixParts,out.suffixParts⟩ : Split n))
              (Executes.returned _ _)
        · change p.value c+cachedValue out.prefixParts c = t
          rw [hvalue]
          ring
      · have hpc : 0 ≤ p.value c := validPart_nonnegative P hmono hp c
        have htpc : t ≤ p.value c := (lt_of_not_ge hwhole).le
        have hlegal : Legal P (.cut c p.left p.right t) := by
          refine ⟨hp.1.1,hp.1.2.1,hp.1.2.2,?_⟩
          unfold ExtremalRoots.LegalTarget
          rw [← hp.2 c]
          simpa only [min_eq_left hpc,max_eq_right hpc] using And.intro ht htpc
        obtain ⟨record,trace,hexec,hlen,hcuts,hpoint,hvalues,hc⟩ :=
          endpoint_program_correct P oracle hpolicy c p.left p.right t hlegal prior
        have hv := split_parts_valid P hp record.point record.value hpoint hvalues
        let out : Split n :=
          ⟨[leftPart p record.point record.value],rightPart p record.point record.value::ps⟩
        refine ⟨out,trace,?_,hlen.le,hcuts.le,PrefixSplit.cut _ _ _ _ hpoint,
          ⟨hv.1,trivial⟩,⟨hv.2,hps⟩,?_⟩
        · simpa only [splitProgram,ite_eq_right ht0,ite_eq_right hwhole,List.append_nil] using
            hexec.bind (fun record => Program.returned
              (⟨[leftPart p record.point record.value],rightPart p record.point record.value::ps⟩ : Split n))
              (Executes.returned _ _)
        · simpa only [out,cachedValue,leftPart,add_zero] using hc

/-- The same actual program returns a disjoint physical partition of the
entire input union, with both component lists still in spatial order. -/
theorem split_program_physical {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (ps : List (Parent n)) (hp : Valid P ps) (ho : Ordered ps)
    (t : ℝ) (ht : 0 ≤ t) (htop : t ≤ cachedValue ps c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Split n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (splitProgram c t ps) prior out trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      material out.prefixParts ∪ material out.suffixParts = material ps ∧
      Disjoint (material out.prefixParts) (material out.suffixParts) ∧
      Ordered (out.prefixParts ++ out.suffixParts) ∧ Valid P out.prefixParts ∧ Valid P out.suffixParts ∧
      cachedValue out.prefixParts c = t ∧
      ∀ i, cachedValue out.prefixParts i+cachedValue out.suffixParts i = cachedValue ps i := by
  obtain ⟨out,trace,hexec,hlen,hcuts,hsplit,hvalidpre,hvalidsuf,hvalue⟩ :=
    split_program_correct P hmono oracle hpolicy c ps hp t ht htop prior
  exact ⟨out,trace,hexec,hlen,hcuts,hsplit.cover,hsplit.disjoint ho,hsplit.ordered ho,
    hvalidpre,hvalidsuf,hvalue,hsplit.cached_add⟩

structure SuffixSplit (n : ℕ) where
  suffixParts : List (Parent n)
  prefixParts : List (Parent n)

/-- A suffix target uses the complementary prefix target. The swap of the
two material lists is internal computation and makes no additional query. -/
def suffixProgram {n : ℕ} (c : Fin n) (t : ℝ) (ps : List (Parent n)) :
    Program (Query (Fin n)) ℝ (SuffixSplit n) :=
  (splitProgram c (cachedValue ps c-t) ps).bind
    (fun out => .returned ⟨out.suffixParts,out.prefixParts⟩)

theorem suffix_program_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (ps : List (Parent n)) (hp : Valid P ps)
    (t : ℝ) (ht : 0 ≤ t) (htop : t ≤ cachedValue ps c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : SuffixSplit n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (suffixProgram c t ps) prior out trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      PrefixSplit ps out.prefixParts out.suffixParts ∧
      Valid P out.suffixParts ∧ Valid P out.prefixParts ∧ cachedValue out.suffixParts c = t := by
  have htarget : 0 ≤ cachedValue ps c-t := sub_nonneg.mpr htop
  have hbound : cachedValue ps c-t ≤ cachedValue ps c := sub_le_self _ ht
  obtain ⟨out,trace,hexec,hlen,hcuts,hsplit,hvalidpre,hvalidsuf,hvalue⟩ :=
    split_program_correct P hmono oracle hpolicy c ps hp _ htarget hbound prior
  refine ⟨⟨out.suffixParts,out.prefixParts⟩,trace,?_,hlen,hcuts,hsplit,hvalidsuf,hvalidpre,?_⟩
  · simpa only [suffixProgram,List.append_nil] using hexec.bind
      (fun out => Program.returned (⟨out.suffixParts,out.prefixParts⟩ : SuffixSplit n))
      (Executes.returned _ _)
  · have hsum := hsplit.cached_add c
    change cachedValue out.suffixParts c = t
    linarith

end EnvyFreeResearch.Full.Chores.OrderedUnion
