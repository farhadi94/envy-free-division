import EnvyFreeResearch.Full.ChoresAugmentTransfer

/-! A batch of disjoint reservation transfers. Sources and destinations
are distinct within a batch and have disjoint label sets. The literal
ordinary-query execution preserves the full family and pays every cached
target exactly; it never assumes the successful batch as a certificate. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n : ℕ} {Label : Type*} [DecidableEq Label]

structure TransferJob (Label : Type*) where
  source : Label
  destination : Label
  amount : ℝ

def transferBatch (c : Fin n) : List (TransferJob Label) →
    (Label → List (Parent n)) → Program (Query (Fin n)) ℝ (Label → List (Parent n))
  | [], pieces => .returned pieces
  | job::jobs, pieces => (transferProgram c job.amount pieces job.source job.destination).bind
      (transferBatch c jobs)

theorem transfer_batch_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (jobs : List (TransferJob Label))
    (hsource : (jobs.map TransferJob.source).Nodup)
    (hdest : (jobs.map TransferJob.destination).Nodup)
    (hcross : ∀ a ∈ jobs, ∀ b ∈ jobs, a.source ≠ b.destination)
    (pieces : Label → List (Parent n)) (hv : FamilyValid P pieces)
    (hfit : ∀ j ∈ jobs, 0 ≤ j.amount ∧ j.amount ≤ OrderedUnion.cachedValue (pieces j.source) c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ next trace, Executes oracle (transferBatch c jobs pieces) prior next trace ∧
      trace.length ≤ jobs.length*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ jobs.length ∧
      FamilyValid P next ∧ familyMaterial next=familyMaterial pieces ∧
      (∀ j, j ∉ jobs.map TransferJob.source → j ∉ jobs.map TransferJob.destination → next j=pieces j) ∧
      (∀ j, j ∉ jobs.map TransferJob.source → material (pieces j) ⊆ material (next j)) ∧
      (∀ j, j ∉ jobs.map TransferJob.source → ∀ i,
        OrderedUnion.cachedValue (pieces j) i ≤ OrderedUnion.cachedValue (next j) i) ∧
      ∀ job ∈ jobs, OrderedUnion.cachedValue (next job.destination) c=
        OrderedUnion.cachedValue (pieces job.destination) c+job.amount := by
  induction jobs generalizing pieces prior with
  | nil =>
    refine ⟨pieces,[],Executes.returned _ _,by simp,by simp,hv,rfl,?_,?_,?_,?_⟩ <;> simp
  | cons job jobs ih =>
    obtain ⟨hsourceNot,hsourceTail⟩ := List.nodup_cons.mp hsource
    obtain ⟨hdestNot,hdestTail⟩ := List.nodup_cons.mp hdest
    have hhead : job.source ≠ job.destination := hcross job (by simp) job (by simp)
    have hsource_ne (j : TransferJob Label) (hj : j ∈ jobs) : j.source ≠ job.source := by
      intro heq
      exact hsourceNot (List.mem_map.mpr ⟨j,hj,heq⟩)
    have hdest_ne (j : TransferJob Label) (hj : j ∈ jobs) : j.destination ≠ job.destination := by
      intro heq
      exact hdestNot (List.mem_map.mpr ⟨j,hj,heq⟩)
    have hcrossTail : ∀ a ∈ jobs, ∀ b ∈ jobs, a.source ≠ b.destination :=
      fun a ha b hb => hcross a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    obtain ⟨middle,t1,hexec1,hQ1,hC1,hv1,hcover1,hother1,hsub1,hmono1,htarget1⟩ :=
      transfer_program_correct P hmono oracle hpolicy c job.amount pieces hv job.source job.destination
        hhead (hfit job (by simp)).1 (hfit job (by simp)).2 prior
    have hsourceSame (j : TransferJob Label) (hj : j ∈ jobs) : middle j.source=pieces j.source :=
      hother1 j.source (hsource_ne j hj) (hcross j (List.mem_cons_of_mem _ hj) job (by simp))
    have hdestSame (j : TransferJob Label) (hj : j ∈ jobs) : middle j.destination=pieces j.destination :=
      hother1 j.destination (Ne.symm (hcross job (by simp) j (List.mem_cons_of_mem _ hj))) (hdest_ne j hj)
    have hfitTail : ∀ j ∈ jobs, 0 ≤ j.amount ∧ j.amount ≤ OrderedUnion.cachedValue (middle j.source) c := by
      intro j hj
      rw [hsourceSame j hj]
      exact hfit j (List.mem_cons_of_mem _ hj)
    obtain ⟨next,t2,hexec2,hQ2,hC2,hv2,hcover2,hother2,hsub2,hmono2,htarget2⟩ :=
      ih hsourceTail hdestTail hcrossTail middle hv1 hfitTail (prior++t1)
    refine ⟨next,t1++t2,hexec1.bind (transferBatch c jobs) hexec2,?_,?_,hv2,
      hcover2.trans hcover1,?_,?_,?_,?_⟩
    · simp only [List.length_append,List.length_cons,Nat.add_mul]
      omega
    · simp only [List.countP_append,List.length_cons]
      omega
    · intro j hs hd
      have hs' : j ∉ jobs.map TransferJob.source := fun h => hs (List.mem_cons_of_mem _ h)
      have hd' : j ∉ jobs.map TransferJob.destination := fun h => hd (List.mem_cons_of_mem _ h)
      rw [hother2 j hs' hd',hother1 j (fun h => hs (by simp [h])) (fun h => hd (by simp [h]))]
    · intro j hs
      have hs' : j ∉ jobs.map TransferJob.source := fun h => hs (List.mem_cons_of_mem _ h)
      exact (hsub1 j (fun h => hs (by simp [h]))).trans (hsub2 j hs')
    · intro j hs i
      have hs' : j ∉ jobs.map TransferJob.source := fun h => hs (List.mem_cons_of_mem _ h)
      exact (hmono1 j (fun h => hs (by simp [h])) i).trans (hmono2 j hs' i)
    · intro j hj
      rcases List.mem_cons.mp hj with heq | hj
      · subst j
        have hs' : job.destination ∉ jobs.map TransferJob.source := by
          rintro h
          obtain ⟨j,hj,heq⟩ := List.mem_map.mp h
          exact hcross j (List.mem_cons_of_mem _ hj) job (by simp) heq
        rw [hother2 job.destination hs' hdestNot]
        exact htarget1
      · rw [htarget2 j hj,hdestSame j hj]

end EnvyFreeResearch.Full.Chores.Augment
