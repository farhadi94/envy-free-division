import EnvyFreeResearch.Full.ChoresAugmentJobs

/-! One reverse augmentation round, using the actual order statistic of
current public bundles and its derived physical supplement feasibility. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n : ℕ} {Label : Type*} [DecidableEq Label]

structure RoundOutput (n : ℕ) (Label : Type*) where
  pieces : Label → List (Parent n)
  designated : List Label
  threshold : ℝ

def roundProgram (c : Fin n) (a : ℕ) (available reserves : List Label)
    (pieces : Label → List (Parent n)) : Program (Query (Fin n)) ℝ (RoundOutput n Label) :=
  let pick := quantile (fun p => OrderedUnion.cachedValue (pieces p) c) a available
  (transferBatch c (thresholdJobs c pick.2 pieces reserves pick.1) pieces).bind
    (fun next => .returned ⟨next,pick.1,pick.2⟩)

theorem round_program_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (a : ℕ) (available reserves : List Label)
    (havailable : available.Nodup) (hreserves : reserves.Nodup) (hcount : reserves.length=a)
    (hcross : ∀ s ∈ reserves, ∀ d ∈ available, s ≠ d)
    (pieces : Label → List (Parent n)) (hv : FamilyValid P pieces)
    (low : Finset Label) (hlow : a < low.card) (hinside : ∀ p ∈ low, p ∈ available)
    (hcap : ∀ p ∈ low, ∀ r ∈ reserves,
      OrderedUnion.cachedValue (pieces p) c ≤ OrderedUnion.cachedValue (pieces r) c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (roundProgram c a available reserves pieces) prior out trace ∧
      trace.length ≤ a*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ a ∧
      FamilyValid P out.pieces ∧ familyMaterial out.pieces=familyMaterial pieces ∧
      out.designated.length=a ∧ out.designated.Nodup ∧
      (∀ p ∈ out.designated, p ∈ available) ∧
      (∀ j, j ∉ reserves → j ∉ out.designated → out.pieces j=pieces j) ∧
      (∀ j, j ∉ reserves → material (pieces j) ⊆ material (out.pieces j)) ∧
      (∀ j, j ∉ reserves → ∀ i, OrderedUnion.cachedValue (pieces j) i ≤ OrderedUnion.cachedValue (out.pieces j) i) ∧
      (∀ p ∈ available, out.threshold ≤ OrderedUnion.cachedValue (out.pieces p) c) ∧
      ∀ p ∈ out.designated, OrderedUnion.cachedValue (out.pieces p) c=out.threshold := by
  have hlens : a+1 ≤ available.length := by
    have hsub : low ⊆ available.toFinset := fun p hp => List.mem_toFinset.mpr (hinside p hp)
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup havailable] at hcard
    omega
  obtain ⟨D,t,hquantile,hDlen,hDnd,hDin,hDcost,hthreshold,hwitness⟩ :=
    quantile_correct (fun p => OrderedUnion.cachedValue (pieces p) c) a available hlens havailable
  have htcap (r : Label) (hr : r ∈ reserves) : t ≤ OrderedUnion.cachedValue (pieces r) c := by
    apply threshold_le_of_many (fun p => OrderedUnion.cachedValue (pieces p) c) available D hDnd t
      (OrderedUnion.cachedValue (pieces r) c) hthreshold low
    · simpa only [hDlen] using hlow
    · exact hinside
    · exact fun p hp => hcap p hp r hr
  have hlen : reserves.length=D.length := hcount.trans hDlen.symm
  have hcross' : ∀ s ∈ reserves, ∀ d ∈ D, s ≠ d := fun s hs d hd => hcross s hs d (hDin d hd)
  obtain ⟨next,trace,hexec,hQ,hC,hv',hcover,hother,hsub,hmon,htarget⟩ :=
    threshold_batch_correct P hmono oracle hpolicy c t pieces hv reserves D hlen hreserves hDnd
      hcross' hDcost htcap prior
  let out : RoundOutput n Label := ⟨next,D,t⟩
  refine ⟨out,trace,?_,?_,?_,hv',hcover,hDlen,hDnd,hDin,hother,hsub,hmon,?_,htarget⟩
  · simpa only [roundProgram,hquantile,List.append_nil] using
      hexec.bind (fun next => Program.returned (⟨next,D,t⟩ : RoundOutput n Label)) (Executes.returned _ _)
  · simpa only [hcount] using hQ
  · simpa only [hcount] using hC
  · intro p hp
    by_cases hD : p ∈ D
    · change t ≤ OrderedUnion.cachedValue (next p) c
      rw [htarget p hD]
    · have hres : p ∉ reserves := fun hr => hcross p hr p hp rfl
      change t ≤ OrderedUnion.cachedValue (next p) c
      rw [hother p hres hD]
      exact hthreshold p hp hD

end EnvyFreeResearch.Full.Chores.Augment
