import EnvyFreeResearch.Full.ChoresAugmentReverseInvariant

/-! Complete ordinary-query execution of reverse augmentation. Feasible
supplements are derived from untouched original public pieces at every
round, including arbitrary ties and zero costs. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n : ℕ} {Label : Type*} [LinearOrder Label]

theorem reverse_program_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (recipient : ℕ → Fin n) (available : List Label) (reserves : ℕ → List Label)
    (original : Label → List (Parent n)) (havailable : available.Nodup)
    (k : ℕ)
    (hres : ∀ i < k, (reserves i).length=2^i ∧ (reserves i).Nodup)
    (hcross : ∀ i < k, ∀ r ∈ reserves i, ∀ p ∈ available, r ≠ p)
    (hsep : ∀ i < k, ∀ j < k, i ≠ j → ∀ r ∈ reserves i, ∀ s ∈ reserves j, r ≠ s)
    (hdom : ∀ i < k, ∀ p ∈ available, ∀ r ∈ reserves i,
      OrderedUnion.cachedValue (original p) (recipient i) ≤ OrderedUnion.cachedValue (original r) (recipient i))
    (pieces : Label → List (Parent n)) (hv : FamilyValid P pieces)
    (touched : Finset Label) (hbudget : touched.card+totalQuota k < available.length)
    (hpublic : ∀ p ∈ available, p ∉ touched → pieces p=original p)
    (hreserved : ∀ i < k, ∀ r ∈ reserves i, pieces r=original r)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (reverseProgram recipient available reserves k pieces) prior out trace ∧
      trace.length ≤ totalQuota k*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ totalQuota k ∧
      FamilyValid P out.pieces ∧ familyMaterial out.pieces=familyMaterial pieces ∧
      out.Sound recipient available k ∧
      (∀ p ∈ available, p ∉ out.marked k → out.pieces p=pieces p) ∧
      (∀ p ∈ available, material (pieces p) ⊆ material (out.pieces p)) ∧
      ∀ p ∈ available, ∀ i, OrderedUnion.cachedValue (pieces p) i ≤ OrderedUnion.cachedValue (out.pieces p) i := by
  induction k generalizing pieces touched prior with
  | zero =>
    let out : ReverseOutput n Label := ⟨pieces,fun _ => [],fun _ => 0⟩
    refine ⟨out,[],Executes.returned _ _,by simp [totalQuota_zero],by simp [totalQuota_zero],
      hv,rfl,?_,?_,?_,?_⟩
    · constructor <;> simp
    · intro p hp hn; rfl
    · intro p hp; exact Subset.rfl
    · intro p hp i; exact le_rfl
  | succ k ih =>
    let low := available.toFinset \ touched
    have hlow : 2^k < low.card := by
      have hcard : available.toFinset.card ≤ low.card+touched.card := Finset.card_le_card_sdiff_add_card
      rw [List.toFinset_card_of_nodup havailable] at hcard
      rw [totalQuota_succ] at hbudget
      omega
    have hlowIn : ∀ p ∈ low, p ∈ available := fun p hp => List.mem_toFinset.mp (Finset.mem_sdiff.mp hp).1
    have hcap : ∀ p ∈ low, ∀ r ∈ reserves k,
        OrderedUnion.cachedValue (pieces p) (recipient k) ≤ OrderedUnion.cachedValue (pieces r) (recipient k) := by
      intro p hp r hr
      rw [hpublic p (hlowIn p hp) (Finset.mem_sdiff.mp hp).2,hreserved k (Nat.lt_succ_self k) r hr]
      exact hdom k (Nat.lt_succ_self k) p (hlowIn p hp) r hr
    obtain ⟨round,t1,hexec1,hQ1,hC1,hv1,hcover1,hcount,hnd,hinside,hother1,hsub1,hmon1,hfloor,hexact⟩ :=
      round_program_correct P hmono oracle hpolicy (recipient k) (2^k) available (reserves k)
        havailable (hres k (Nat.lt_succ_self k)).2 (hres k (Nat.lt_succ_self k)).1
        (hcross k (Nat.lt_succ_self k)) pieces hv low hlow hlowIn hcap prior
    have hpublicNot (p : Label) (hp : p ∈ available) : p ∉ reserves k :=
      fun hr => hcross k (Nat.lt_succ_self k) p hr p hp rfl
    let touched' := touched ∪ round.designated.toFinset
    have hbudget' : touched'.card+totalQuota k < available.length := by
      have hcard : touched'.card ≤ touched.card+round.designated.toFinset.card := Finset.card_union_le _ _
      rw [List.toFinset_card_of_nodup hnd,hcount] at hcard
      rw [totalQuota_succ] at hbudget
      omega
    have hpublic' : ∀ p ∈ available, p ∉ touched' → round.pieces p=original p := by
      intro p hp hnot
      have hnotD : p ∉ round.designated := fun hd => hnot (Finset.mem_union_right _ (List.mem_toFinset.mpr hd))
      have hnotOld : p ∉ touched := fun ht => hnot (Finset.mem_union_left _ ht)
      rw [hother1 p (hpublicNot p hp) hnotD,hpublic p hp hnotOld]
    have hreserved' : ∀ i < k, ∀ r ∈ reserves i, round.pieces r=original r := by
      intro i hi r hr
      have hnotR : r ∉ reserves k := fun h => hsep i (Nat.lt_succ_of_lt hi) k (Nat.lt_succ_self k)
        (Nat.ne_of_lt hi) r hr r h rfl
      have hnotD : r ∉ round.designated := fun h => hcross i (Nat.lt_succ_of_lt hi) r hr r (hinside r h) rfl
      rw [hother1 r hnotR hnotD,hreserved i (Nat.lt_succ_of_lt hi) r hr]
    obtain ⟨out,t2,hexec2,hQ2,hC2,hv2,hcover2,hsound,hother2,hsub2,hmon2⟩ :=
      ih (fun i hi => hres i (Nat.lt_succ_of_lt hi))
        (fun i hi => hcross i (Nat.lt_succ_of_lt hi))
        (fun i hi j hj => hsep i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj))
        (fun i hi => hdom i (Nat.lt_succ_of_lt hi))
        round.pieces hv1 touched' hbudget' hpublic' hreserved' (prior++t1)
    refine ⟨out.install k round,t1++t2,?_,?_,?_,hv2,hcover2.trans hcover1,
      install_sound recipient available k round out hsound hcount hnd hinside hfloor hexact hmon2 hother2,
      ?_,?_,?_⟩
    · have htail := hexec2.bind (fun out => Program.returned (out.install k round)) (Executes.returned _ _)
      simpa only [reverseProgram,List.append_nil] using
        hexec1.bind (fun round => (reverseProgram recipient available reserves k round.pieces).bind
          (fun out => Program.returned (out.install k round))) htail
    · simp only [List.length_append,totalQuota_succ,Nat.add_mul]
      omega
    · simp only [List.countP_append,totalQuota_succ]
      omega
    · intro p hp hnot
      rw [marked_install] at hnot
      have hnold : p ∉ out.marked k := fun h => hnot (Finset.mem_union_left _ h)
      have hnnew : p ∉ round.designated := fun h => hnot (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
      change out.pieces p=pieces p
      rw [hother2 p hp hnold,hother1 p (hpublicNot p hp) hnnew]
    · intro p hp
      exact (hsub1 p (hpublicNot p hp)).trans (hsub2 p hp)
    · intro p hp i
      exact (hmon1 p (hpublicNot p hp) i).trans (hmon2 p hp i)

end EnvyFreeResearch.Full.Chores.Augment
