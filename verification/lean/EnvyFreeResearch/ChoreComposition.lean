import EnvyFreeResearch.R7Chores
import EnvyFreeResearch.R8Chores

/-!
# Concrete finite chore ledger composition

Root allocations, resets, closure and donor modifications are explicit finite
objects. Credits and deficits are computed from their actual cost tables.
Continuous realizability of those tables and the scheduler's SCC geometry are
not asserted here. Pool transitions commit complete groups simultaneously.
-/

noncomputable section

namespace EnvyFreeResearch.ChoreComposition

open R7Chores
open scoped BigOperators

def total {α : Type*} (xs : List α) (f : α → ℝ) : ℝ :=
  (xs.map f).sum

@[simp] theorem total_nil {α : Type*} (f : α → ℝ) : total [] f = 0 := rfl

@[simp] theorem total_cons {α : Type*} (x : α) (xs : List α) (f : α → ℝ) :
    total (x::xs) f = f x + total xs f := rfl

theorem total_append {α : Type*} (xs ys : List α) (f : α → ℝ) :
    total (xs++ys) f = total xs f + total ys f := by
  simp [total, List.map_append, List.sum_append]

theorem total_add {α : Type*} (xs : List α) (f g : α → ℝ) :
    total xs (fun x => f x+g x) = total xs f+total xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [total_cons, ih]; ring

theorem total_mono {α : Type*} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : total xs f ≤ total xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem total_nonnegative {α : Type*} (xs : List α) (f : α → ℝ)
    (h : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ total xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact add_nonneg (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem total_flatMap {α β : Type*} (xs : List α) (ys : α → List β) (f : β → ℝ) :
    total (xs.flatMap ys) f = total xs (fun x => total (ys x) f) := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp only [List.flatMap_cons, total_append, total_cons, ih]

section Roots

variable {Agent Root : Type*} [DecidableEq Agent]

structure Allocation (Agent Root : Type*) where
  root : Root
  baseline : Agent → ℝ
  owner : Equiv.Perm Agent
  cost : Agent → Agent → ℝ

def Allocation.credit (a : Allocation Agent Root) (i p : Agent) : ℝ :=
  if a.owner p=i then a.baseline i-a.cost i p else 0

def Allocation.debit (a : Allocation Agent Root) (i j p : Agent) : ℝ :=
  if a.owner p=j then clipped (a.baseline i-a.cost i p) else 0

theorem allocation_debit_nonnegative (a : Allocation Agent Root) (i j p : Agent) :
    0 ≤ a.debit i j p := by
  unfold Allocation.debit
  split
  · exact clipped_nonnegative _
  · rfl

structure Frame (Agent Root : Type*) where
  root : Root
  baseline : Agent → ℝ
  owner : Equiv.Perm Agent
  allowed : Agent → Finset Agent
  forbidden : Agent → Finset Agent
  equalizerCost : Agent → Agent → Agent → ℝ
  frontierGap : Agent → Agent → ℝ

def Frame.gap (f : Frame Agent Root) (i j p : Agent) : ℝ :=
  f.baseline i-f.equalizerCost i p j

def Frame.reserve (f : Frame Agent Root) (i j p : Agent) : ℝ :=
  recipientReserve (f.allowed p) (f.forbidden p) (fun j => f.gap i j p)
    (f.frontierGap i p) j

def Frame.allocation (f : Frame Agent Root) : Allocation Agent Root where
  root := f.root
  baseline := f.baseline
  owner := f.owner
  cost := fun i p => f.equalizerCost i p (f.owner p)

def Frame.Good (f : Frame Agent Root) : Prop :=
  (∀ p, f.owner p ∈ f.allowed p) ∧
  (∀ p j, j ∈ f.allowed p → f.equalizerCost j p j=f.baseline j)

def Frame.reset (f : Frame Agent Root) (owner : Equiv.Perm Agent) : Frame Agent Root :=
  { f with owner := owner }

theorem frame_reserve_nonnegative (f : Frame Agent Root) (i j p : Agent) :
    0 ≤ f.reserve i j p := recipient_reserve_nonnegative _ _ _ _ _

theorem frame_credit_zero (f : Frame Agent Root) (hf : f.Good) (i p : Agent) :
    f.allocation.credit i p=0 := by
  unfold Allocation.credit Frame.allocation
  by_cases h : f.owner p=i
  · simp only [h, ite_true]
    rw [hf.2 p i (h ▸ hf.1 p)]
    ring
  · simp [h]

/-- An executed allowed equalizer's actual deficit is covered by the literal reserve. -/
theorem frame_debit_le_reserve (f : Frame Agent Root) (hf : f.Good) (i j p : Agent) :
    f.allocation.debit i j p ≤ f.reserve i j p := by
  by_cases h : f.owner p=j
  · have hj : j ∈ f.allowed p := h ▸ hf.1 p
    simp [Allocation.debit, Frame.allocation, Frame.reserve, Frame.gap,
      recipientReserve, h, hj]
  · simp only [Allocation.debit, Frame.allocation, h, ite_false]
    exact frame_reserve_nonnegative f i j p

omit [DecidableEq Agent] in
theorem reset_good (f : Frame Agent Root) (hf : f.Good) (owner : Equiv.Perm Agent)
    (hallowed : ∀ p, owner p ∈ f.allowed p) : (f.reset owner).Good :=
  ⟨hallowed, hf.2⟩

@[simp] theorem reset_reserve (f : Frame Agent Root) (owner : Equiv.Perm Agent)
    (i j p : Agent) : (f.reset owner).reserve i j p=f.reserve i j p := rfl

structure Proposal (Agent Root : Type*) where
  before : Frame Agent Root
  label : Agent
  recipient : Agent
  owner : Equiv.Perm Agent
  utility : Agent → ℝ
  execute : Bool

def Proposal.Good (d : Proposal Agent Root) : Prop :=
  d.before.Good ∧
  (d.execute=true → d.owner d.label=d.recipient) ∧
  (d.execute=true → ∀ p, p≠d.label → d.owner p ∈ d.before.allowed p) ∧
  (d.execute=true → 0 ≤ d.utility d.recipient)

def Proposal.output (d : Proposal Agent Root) : Allocation Agent Root :=
  if d.execute then
    { root := d.before.root
      baseline := d.before.baseline
      owner := d.owner
      cost := fun i p => if p=d.label then d.before.baseline i-d.utility i
        else d.before.equalizerCost i p (d.owner p) }
  else d.before.allocation

def Proposal.payment (d : Proposal Agent Root) (i p : Agent) : ℝ :=
  if d.execute=true ∧ i=d.recipient ∧ p=d.label then d.utility d.recipient else 0

def Proposal.extra (d : Proposal Agent Root) (i j p : Agent) : ℝ :=
  if d.execute=true ∧ j=d.recipient ∧ p=d.label then clipped (d.utility i) else 0

@[simp] theorem proposal_root (d : Proposal Agent Root) : d.output.root=d.before.root := by
  cases h : d.execute <;> simp [Proposal.output, h, Frame.allocation]

theorem proposal_zero_is_unchanged (d : Proposal Agent Root) (h : d.execute=false) :
    d.output=d.before.allocation := by simp [Proposal.output, h]

theorem proposal_payment_nonnegative (d : Proposal Agent Root) (hd : d.Good) (i p : Agent) :
    0 ≤ d.payment i p := by
  unfold Proposal.payment
  split_ifs with h
  · exact hd.2.2.2 h.1
  · rfl

/-- The actual own-baseline reduction equals the executed task's nonnegative payment. -/
theorem proposal_credit (d : Proposal Agent Root) (hd : d.Good) (i p : Agent) :
    d.output.credit i p=d.payment i p := by
  cases he : d.execute with
  | false => simp [Proposal.output, Proposal.payment, he, frame_credit_zero d.before hd.1]
  | true =>
    have howner := hd.2.1 he
    by_cases hp : p=d.label
    · subst p
      simp only [Proposal.output, he, ↓reduceIte, Allocation.credit,
        howner, Proposal.payment, true_and, and_true]
      by_cases hi : i=d.recipient
      · subst i
        simp
      · simp [hi, Ne.symm hi]
    · have hself := hd.1.2 p (d.owner p) (hd.2.2.1 he p hp)
      simp only [Proposal.output, he, ↓reduceIte, Allocation.credit,
        hp, Proposal.payment, and_false]
      by_cases hi : d.owner p=i
      · rw [hi] at hself
        simp [hi, hself]
      · simp [hi]

/-- Only the modified label can add a new deficit; all other labels use old allowed reserves. -/
theorem proposal_debit_bound (d : Proposal Agent Root) (hd : d.Good) (i j p : Agent) :
    d.output.debit i j p ≤ d.before.reserve i j p+d.extra i j p := by
  cases he : d.execute with
  | false =>
    simpa [Proposal.output, Proposal.extra, he] using frame_debit_le_reserve d.before hd.1 i j p
  | true =>
    have howner := hd.2.1 he
    by_cases hp : p=d.label
    · subst p
      have hnonneg := frame_reserve_nonnegative d.before i j d.label
      simp only [Proposal.output, he, ↓reduceIte, Allocation.debit,
        howner, Proposal.extra, true_and, and_true]
      by_cases hj : j=d.recipient
      · subst j
        have hid : d.before.baseline i-(d.before.baseline i-d.utility i)=d.utility i := by ring
        simpa [hid] using (le_add_of_nonneg_left (a := clipped (d.utility i)) hnonneg)
      · simp [hj, Ne.symm hj, hnonneg]
    · have hallow := hd.2.2.1 he p hp
      simp only [Proposal.output, he, ↓reduceIte, Allocation.debit,
        hp, Proposal.extra, and_false, add_zero]
      by_cases hj : d.owner p=j
      · have hjallow : j ∈ d.before.allowed p := hj ▸ hallow
        simp [hj, Frame.reserve, Frame.gap, recipientReserve, hjallow]
      · simp [hj, frame_reserve_nonnegative]

/-- Ordinary batches execute precisely positive own affine values, including zero as an unchanged root. -/
def ordinaryProposal (before : Frame Agent Root) (label recipient : Agent)
    (owner : Equiv.Perm Agent) (utility : Agent → ℝ) : Proposal Agent Root :=
  ⟨before, label, recipient, owner, utility, decide (0 < utility recipient)⟩

omit [DecidableEq Agent] in
theorem ordinary_proposal_good (before : Frame Agent Root) (hbefore : before.Good)
    (label recipient : Agent) (owner : Equiv.Perm Agent) (utility : Agent → ℝ)
    (howner : owner label=recipient)
    (hallowed : ∀ p, p≠label → owner p ∈ before.allowed p) :
    (ordinaryProposal before label recipient owner utility).Good := by
  refine ⟨hbefore, fun _ => howner, fun _ => hallowed, ?_⟩
  intro h
  have hpos : 0 < utility recipient := of_decide_eq_true h
  exact hpos.le

theorem ordinary_nonpositive_is_unchanged (before : Frame Agent Root) (label recipient : Agent)
    (owner : Equiv.Perm Agent) (utility : Agent → ℝ) (hzero : utility recipient ≤ 0) :
    (ordinaryProposal before label recipient owner utility).output=before.allocation := by
  simp [ordinaryProposal, Proposal.output, not_lt.mpr hzero]

/-- Closed affine batches execute own-zero assignments as well as positive ones. -/
def affineProposal (before : Frame Agent Root) (label recipient : Agent)
    (owner : Equiv.Perm Agent) (utility : Agent → ℝ) : Proposal Agent Root :=
  ⟨before, label, recipient, owner, utility, true⟩

omit [DecidableEq Agent] in
theorem affine_proposal_good (before : Frame Agent Root) (hbefore : before.Good)
    (label recipient : Agent) (owner : Equiv.Perm Agent) (utility : Agent → ℝ)
    (howner : owner label=recipient)
    (hallowed : ∀ p, p≠label → owner p ∈ before.allowed p)
    (hown : 0 ≤ utility recipient) :
    (affineProposal before label recipient owner utility).Good :=
  ⟨hbefore, fun _ => howner, fun _ => hallowed, fun _ => hown⟩

end Roots

section Packages

variable {Agent Root : Type*} [DecidableEq Agent]

structure Package (Agent Root : Type*) where
  frozen : List (Allocation Agent Root)
  live : Option (Frame Agent Root)

def Package.credit (s : Package Agent Root) (i p : Agent) : ℝ :=
  total s.frozen (fun a => a.credit i p)

def Package.debit (s : Package Agent Root) (i j p : Agent) : ℝ :=
  total s.frozen (fun a => a.debit i j p)

def Package.reserve (s : Package Agent Root) (i j p : Agent) : ℝ :=
  match s.live with
  | none => 0
  | some f => f.reserve i j p

def Package.ids (s : Package Agent Root) : List Root :=
  s.frozen.map Allocation.root ++ s.live.toList.map Frame.root

structure Package.Valid (s : Package Agent Root) : Prop where
  live_good : ∀ f, s.live=some f → f.Good
  frozen_nonnegative : ∀ a ∈ s.frozen, ∀ i p, 0 ≤ a.credit i p
  budget : ∀ i j p, i≠j → s.debit i j p+s.reserve i j p ≤ s.credit i p

theorem package_reserve_nonnegative (s : Package Agent Root) (i j p : Agent) :
    0 ≤ s.reserve i j p := by
  cases h : s.live with
  | none => simp [Package.reserve, h]
  | some f => simpa [Package.reserve, h] using frame_reserve_nonnegative f i j p

def Package.seed (f : Frame Agent Root) : Package Agent Root := ⟨[], some f⟩

theorem seed_valid (f : Frame Agent Root) (hf : f.Good)
    (hzero : ∀ i j p, i≠j → f.reserve i j p=0) : (Package.seed f).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    have : f=g := Option.some.inj hg
    simpa only [← this] using hf
  · simp [Package.seed]
  · intro i j p hij
    simp [Package.seed, Package.credit, Package.debit, Package.reserve, hzero i j p hij]

def Package.reset (s : Package Agent Root) (owner : Equiv.Perm Agent) : Package Agent Root :=
  { s with live := s.live.map (fun f => f.reset owner) }

def Package.close (s : Package Agent Root) : Package Agent Root :=
  match s.live with
  | none => s
  | some f => ⟨s.frozen++[f.allocation], none⟩

theorem package_reset_valid (s : Package Agent Root) (hs : s.Valid) (owner : Equiv.Perm Agent)
    (hallowed : ∀ f, s.live=some f → ∀ p, owner p ∈ f.allowed p) :
    (s.reset owner).Valid := by
  cases he : s.live with
  | none =>
    refine ⟨?_, hs.frozen_nonnegative, ?_⟩
    · intro g hg
      simp [Package.reset, he] at hg
    · intro i j p hij
      simpa [Package.reset, Package.reserve, Package.credit, Package.debit, he] using
        hs.budget i j p hij
  | some f =>
    refine ⟨?_, hs.frozen_nonnegative, ?_⟩
    · intro g hg
      have hg' : f.reset owner=g := by simpa [Package.reset, he] using hg
      rw [← hg']
      exact reset_good f (hs.live_good f he) owner (hallowed f he)
    · intro i j p hij
      simpa [Package.reset, Package.reserve, Package.credit, Package.debit, he] using
        hs.budget i j p hij

omit [DecidableEq Agent] in
@[simp] theorem package_reset_ids (s : Package Agent Root) (owner : Equiv.Perm Agent) :
    (s.reset owner).ids=s.ids := by
  cases he : s.live <;> simp [Package.ids, Package.reset, Frame.reset, he]

theorem package_close_credit (s : Package Agent Root) (hs : s.Valid) (i p : Agent) :
    s.close.credit i p=s.credit i p := by
  cases he : s.live with
  | none => simp [Package.close, he]
  | some f =>
    simp [Package.close, he, Package.credit, total_append,
      frame_credit_zero f (hs.live_good f he)]

theorem package_close_debit_bound (s : Package Agent Root) (hs : s.Valid) (i j p : Agent) :
    s.close.debit i j p ≤ s.debit i j p+s.reserve i j p := by
  cases he : s.live with
  | none => simp [Package.close, Package.reserve, he]
  | some f =>
    simpa [Package.close, Package.debit, Package.reserve, he, total_append] using
      add_le_add_left (frame_debit_le_reserve f (hs.live_good f he) i j p) (s.debit i j p)

omit [DecidableEq Agent] in
@[simp] theorem package_close_live (s : Package Agent Root) : s.close.live=none := by
  cases he : s.live <;> simp [Package.close, he]

omit [DecidableEq Agent] in
@[simp] theorem package_close_ids (s : Package Agent Root) : s.close.ids=s.ids := by
  cases he : s.live <;> simp [Package.close, Package.ids, Frame.allocation, he]

theorem package_close_valid (s : Package Agent Root) (hs : s.Valid) : s.close.Valid := by
  refine ⟨by simp, ?_, ?_⟩
  · intro a ha i p
    cases he : s.live with
    | none => exact hs.frozen_nonnegative a (by simpa [Package.close, he] using ha) i p
    | some f =>
      simp only [Package.close, he, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · exact hs.frozen_nonnegative a ha i p
      · subst a
        rw [frame_credit_zero f (hs.live_good f he)]
  · intro i j p hij
    have hdebit := package_close_debit_bound s hs i j p
    have hbudget := hs.budget i j p hij
    rw [package_close_credit s hs]
    have hr : s.close.reserve i j p=0 := by simp [Package.reserve]
    rw [hr, add_zero]
    exact hdebit.trans hbudget

structure Donation (Agent Root : Type*) where
  package : Package Agent Root
  proposal : Proposal Agent Root

def Donation.WellFormed (d : Donation Agent Root) : Prop :=
  d.package.live=some d.proposal.before ∧ d.proposal.Good

def Donation.frozen (d : Donation Agent Root) : List (Allocation Agent Root) :=
  d.package.frozen++[d.proposal.output]

theorem donation_credit (d : Donation Agent Root) (hd : d.WellFormed) (i p : Agent) :
    total d.frozen (fun a => a.credit i p) =
      d.package.credit i p+d.proposal.payment i p := by
  simp [Donation.frozen, total_append, Package.credit, proposal_credit d.proposal hd.2]

theorem donation_debit_bound (d : Donation Agent Root) (hd : d.WellFormed) (i j p : Agent) :
    total d.frozen (fun a => a.debit i j p) ≤
      d.package.debit i j p+d.package.reserve i j p+d.proposal.extra i j p := by
  have h := proposal_debit_bound d.proposal hd.2 i j p
  have hr : d.package.reserve i j p=d.proposal.before.reserve i j p := by
    simp [Package.reserve, hd.1]
  simp only [Donation.frozen, total_append, total_cons, total_nil, add_zero]
  change d.package.debit i j p+d.proposal.output.debit i j p ≤ _
  rw [hr]
  linarith

theorem donation_frozen_nonnegative (d : Donation Agent Root) (hd : d.WellFormed)
    (hv : d.package.Valid) : ∀ a ∈ d.frozen, ∀ i p, 0 ≤ a.credit i p := by
  intro a ha i p
  rcases List.mem_append.mp ha with ha | ha
  · exact hv.frozen_nonnegative a ha i p
  · have : a=d.proposal.output := by simpa using ha
    subst a
    rw [proposal_credit d.proposal hd.2]
    exact proposal_payment_nonnegative d.proposal hd.2 i p

theorem donation_ids (d : Donation Agent Root) (hd : d.WellFormed) :
    d.frozen.map Allocation.root=d.package.ids := by
  simp [Donation.frozen, Package.ids, hd.1]

def payments (donors : List (Donation Agent Root)) (i p : Agent) : ℝ :=
  total donors (fun d => d.proposal.payment i p)

def extras (donors : List (Donation Agent Root)) (i j p : Agent) : ℝ :=
  total donors (fun d => d.proposal.extra i j p)

def mergeOpen (survivor : Package Agent Root) (donors : List (Donation Agent Root))
    (next : Frame Agent Root) : Package Agent Root :=
  ⟨survivor.frozen++donors.flatMap Donation.frozen, some next⟩

def mergeClosed (survivor : Package Agent Root) (donors : List (Donation Agent Root)) :
    Package Agent Root :=
  ⟨survivor.close.frozen++donors.flatMap Donation.frozen, none⟩

theorem merge_open_credit (survivor : Package Agent Root) (donors : List (Donation Agent Root))
    (next : Frame Agent Root) (hd : ∀ d ∈ donors, d.WellFormed) (i p : Agent) :
    (mergeOpen survivor donors next).credit i p = survivor.credit i p+
      total donors (fun d => d.package.credit i p)+payments donors i p := by
  unfold Package.credit mergeOpen
  rw [total_append, total_flatMap]
  have heq : total donors (fun d => total d.frozen (fun a => a.credit i p)) =
      total donors (fun d => d.package.credit i p+d.proposal.payment i p) := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hdmem
    exact donation_credit d (hd d hdmem) i p
  rw [heq, total_add]
  unfold payments Package.credit
  ring

theorem merge_open_debit_bound (survivor : Package Agent Root)
    (donors : List (Donation Agent Root)) (next : Frame Agent Root)
    (hd : ∀ d ∈ donors, d.WellFormed) (i j p : Agent) :
    (mergeOpen survivor donors next).debit i j p ≤ survivor.debit i j p+
      total donors (fun d => d.package.debit i j p+d.package.reserve i j p)+extras donors i j p := by
  unfold Package.debit mergeOpen
  rw [total_append, total_flatMap]
  have h := total_mono donors _ _ (fun d hmem => donation_debit_bound d (hd d hmem) i j p)
  rw [total_add] at h
  simp only [Package.debit] at h
  change _ ≤ _+_+total donors (fun d => d.proposal.extra i j p)
  linarith

/-- This local certificate charges either a donor comparison or a future reserve, never both. -/
def ExclusivePayment (survivor : Package Agent Root) (donors : List (Donation Agent Root))
    (next : Frame Agent Root) : Prop := ∀ i j p, i≠j →
      (extras donors i j p ≤ payments donors i p ∧ next.reserve i j p ≤ survivor.reserve i j p) ∨
      (extras donors i j p=0 ∧ next.reserve i j p ≤ payments donors i p)

theorem exclusive_payment_local (survivor : Package Agent Root)
    (donors : List (Donation Agent Root)) (next : Frame Agent Root)
    (hpay : ExclusivePayment survivor donors next) (i j p : Agent) (hij : i≠j) :
    extras donors i j p+next.reserve i j p ≤ survivor.reserve i j p+payments donors i p := by
  have hnonneg := package_reserve_nonnegative survivor i j p
  rcases hpay i j p hij with ⟨he, hn⟩ | ⟨he, hn⟩ <;> linarith

/-- The generic finite batch theorem uses computed proposal payments and deficits, not a final invariant premise. -/
theorem merge_open_valid (survivor : Package Agent Root) (hs : survivor.Valid)
    (donors : List (Donation Agent Root)) (hd : ∀ d ∈ donors, d.WellFormed)
    (hv : ∀ d ∈ donors, d.package.Valid) (next : Frame Agent Root) (hn : next.Good)
    (hpay : ExclusivePayment survivor donors next) : (mergeOpen survivor donors next).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    have : next=f := Option.some.inj hf
    simpa only [← this] using hn
  · intro a ha i p
    rcases List.mem_append.mp ha with ha | ha
    · exact hs.frozen_nonnegative a ha i p
    · obtain ⟨d, hdmem, ha⟩ := List.mem_flatMap.mp ha
      exact donation_frozen_nonnegative d (hd d hdmem) (hv d hdmem) a ha i p
  · intro i j p hij
    have hD := merge_open_debit_bound survivor donors next hd i j p
    have hS := hs.budget i j p hij
    have hB := total_mono donors _ _ (fun d hmem => (hv d hmem).budget i j p hij)
    have hP := exclusive_payment_local survivor donors next hpay i j p hij
    rw [merge_open_credit survivor donors next hd]
    change (mergeOpen survivor donors next).debit i j p+next.reserve i j p ≤ _
    linarith

/-- With no surviving root, affine EF need only pay the aggregate actual new donor deficits. -/
theorem merge_closed_valid (survivor : Package Agent Root) (hs : survivor.Valid)
    (donors : List (Donation Agent Root)) (hd : ∀ d ∈ donors, d.WellFormed)
    (hv : ∀ d ∈ donors, d.package.Valid)
    (hpay : ∀ i j p, i≠j → extras donors i j p ≤ payments donors i p) :
    (mergeClosed survivor donors).Valid := by
  let closed := survivor.close
  have hc := package_close_valid survivor hs
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    simp [mergeClosed] at hf
  · intro a ha i p
    rcases List.mem_append.mp ha with ha | ha
    · exact hc.frozen_nonnegative a ha i p
    · obtain ⟨d, hdmem, ha⟩ := List.mem_flatMap.mp ha
      exact donation_frozen_nonnegative d (hd d hdmem) (hv d hdmem) a ha i p
  · intro i j p hij
    have hD : (mergeClosed survivor donors).debit i j p ≤ closed.debit i j p+
        total donors (fun d => d.package.debit i j p+d.package.reserve i j p)+extras donors i j p := by
      unfold Package.debit mergeClosed
      rw [total_append, total_flatMap]
      have h := total_mono donors _ _ (fun d hmem => donation_debit_bound d (hd d hmem) i j p)
      rw [total_add] at h
      simp only [Package.debit] at h
      simp only [closed, extras]
      linarith
    have hS := hc.budget i j p hij
    have hB := total_mono donors _ _ (fun d hmem => (hv d hmem).budget i j p hij)
    have hP := hpay i j p hij
    have hr : closed.reserve i j p=0 := by simp [closed, Package.reserve]
    rw [hr, add_zero] at hS
    have hCredit : (mergeClosed survivor donors).credit i p =
        closed.credit i p+total donors (fun d => d.package.credit i p)+payments donors i p := by
      unfold Package.credit mergeClosed
      rw [total_append, total_flatMap]
      have heq : total donors (fun d => total d.frozen (fun a => a.credit i p)) =
          total donors (fun d => d.package.credit i p+d.proposal.payment i p) := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro d hmem
        exact donation_credit d (hd d hmem) i p
      rw [heq, total_add]
      unfold closed Package.credit payments
      ring
    rw [hCredit]
    change (mergeClosed survivor donors).debit i j p+0 ≤ _
    linarith

end Packages

section ExplicitPayment

variable {Agent : Type*} [DecidableEq Agent]

/-- The two recipient cases are derived from actual masks and clipped EF comparisons. -/
theorem ordinary_component_cases (C allowed forbidden : Finset Agent)
    (pair : Agent → ℝ) (oldFrontier newFrontier : ℝ) (q i j : Agent)
    (u : Agent → Agent → ℝ) (hq : q∉C) (hallowed : allowed⊆C)
    (hforbidden : forbidden⊆C) (hnewowner : pair q=newFrontier)
    (hEF : ∀ a∈C, clipped (u i a) ≤ clipped (u i i))
    (hthreshold : clipped newFrontier ≤ clipped (u i i)) :
    (batchLoss C u i j ≤ retainedCredit u i ∧
      recipientReserve (insert q allowed) (forbidden∪(C\allowed)) pair newFrontier j ≤
        recipientReserve allowed forbidden pair oldFrontier j) ∨
    (batchLoss C u i j=0 ∧
      recipientReserve (insert q allowed) (forbidden∪(C\allowed)) pair newFrontier j ≤
        retainedCredit u i) := by
  by_cases hj : j∈C
  · exact Or.inl ⟨by simpa [batchLoss, hj] using stripped_comparison_payment u i j (hEF j hj),
      internal_skip_forbid_no_growth C allowed forbidden pair oldFrontier newFrontier q j hq hj⟩
  · refine Or.inr ⟨outside_batch_loss_zero C u i j hj, ?_⟩
    rw [external_skip_forbid_reserve C allowed forbidden pair newFrontier q j
      hallowed hforbidden hj hnewowner, retained_credit_exact]
    exact hthreshold

/-- A nonpositive observer row requires no own credit and creates no executed donor deficit. -/
theorem protected_component_zero (C : Finset Agent) (u : Agent → Agent → ℝ)
    (i j : Agent) (hprotected : ∀ a∈C, u i a≤0) : batchLoss C u i j=0 := by
  by_cases hj : j∈C
  · unfold batchLoss retainedDeficit
    simp only [hj, ite_true]
    split_ifs
    · exact clipped_zero_of_nonpositive _ (hprotected j hj)
    · rfl
  · exact outside_batch_loss_zero C u i j hj

/-- Affine zero-own assignments are executed, but EF still makes every positive deficit zero. -/
theorem affine_component_payment (own rival : ℝ) (hown : 0≤own) (hEF : rival≤own) :
    clipped rival≤own := affine_closed_payment own rival hown hEF

end ExplicitPayment

section PackagesContinued

variable {Agent Root : Type*} [DecidableEq Agent]

theorem merge_open_ids (survivor : Package Agent Root) (donors : List (Donation Agent Root))
    (before next : Frame Agent Root) (hs : survivor.live=some before)
    (hroot : next.root=before.root) (hd : ∀ d∈donors, d.WellFormed) :
    (mergeOpen survivor donors next).ids.Perm
      (survivor.ids++donors.flatMap (fun d => d.package.ids)) := by
  have hdids : (donors.flatMap Donation.frozen).map Allocation.root =
      donors.flatMap (fun d => d.package.ids) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro d hmem
    exact donation_ids d (hd d hmem)
  simp only [Package.ids, mergeOpen, List.map_append, hdids, Option.toList_some,
    List.map_cons, List.map_nil, hs, hroot]
  simpa only [List.append_assoc, Package.ids] using
    (List.perm_append_comm (l₁ := donors.flatMap (fun d => d.package.ids))
      (l₂ := [before.root])).append_left (survivor.frozen.map Allocation.root)

theorem merge_closed_ids (survivor : Package Agent Root) (donors : List (Donation Agent Root))
    (hd : ∀ d∈donors, d.WellFormed) :
    (mergeClosed survivor donors).ids=survivor.ids++donors.flatMap (fun d => d.package.ids) := by
  have hdids : (donors.flatMap Donation.frozen).map Allocation.root =
      donors.flatMap (fun d => d.package.ids) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro d hmem
    exact donation_ids d (hd d hmem)
  have hc : survivor.close.frozen.map Allocation.root=survivor.ids := by
    simpa [Package.ids, package_close_live] using package_close_ids survivor
  simp [Package.ids, mergeClosed, hdids, hc]

end PackagesContinued

section TaskIdentification

variable {Agent Root : Type*} [DecidableEq Agent]

def ordinaryTasks (tasks : Finset Agent) (packages : Agent → Package Agent Root)
    (frames : Agent → Frame Agent Root) (labels : Agent → Agent)
    (owners : Agent → Equiv.Perm Agent) (u : Agent → Agent → ℝ) : List (Donation Agent Root) :=
  tasks.toList.map (fun j => ⟨packages j,
    ordinaryProposal (frames j) (labels j) j (owners j) (fun i => u i j)⟩)

/-- Unique recipient indexing reduces the actual own-credit sum to the single designated task. -/
theorem ordinary_tasks_payments (tasks : Finset Agent) (packages : Agent → Package Agent Root)
    (frames : Agent → Frame Agent Root) (labels : Agent → Agent)
    (owners : Agent → Equiv.Perm Agent) (u : Agent → Agent → ℝ) (i p : Agent) :
    payments (ordinaryTasks tasks packages frames labels owners u) i p =
      if i∈tasks.filter (fun j => labels j=p) then retainedCredit u i else 0 := by
  unfold payments ordinaryTasks total
  rw [List.map_map, Finset.sum_map_toList]
  let f := fun j => (ordinaryProposal (frames j) (labels j) j (owners j)
    (fun a => u a j)).payment i p
  change (∑ j∈tasks, f j)=_
  have hz : ∀ j∈tasks, j≠i → f j=0 := by
    intro j _ hji
    simp [f, ordinaryProposal, Proposal.payment, Ne.symm hji]
  by_cases hi : i∈tasks
  · have hs : (∑ j∈tasks, f j)=f i := by
      apply Finset.sum_eq_single i
      · exact hz
      · intro hnot
        exact False.elim (hnot hi)
    rw [hs]
    by_cases hp : labels i=p <;> by_cases hu : 0<u i i <;>
      simp [f, ordinaryProposal, Proposal.payment, retainedCredit, hi, hp, hu, eq_comm]
  · have hs : (∑ j∈tasks, f j)=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply hz j hj
      intro heq
      exact hi (heq ▸ hj)
    rw [hs]
    simp [hi]

/-- The sum over all frozen donor roots has at most one new deficit for each recipient and label. -/
theorem ordinary_tasks_extras (tasks : Finset Agent) (packages : Agent → Package Agent Root)
    (frames : Agent → Frame Agent Root) (labels : Agent → Agent)
    (owners : Agent → Equiv.Perm Agent) (u : Agent → Agent → ℝ) (i j p : Agent) :
    extras (ordinaryTasks tasks packages frames labels owners u) i j p =
      batchLoss (tasks.filter (fun a => labels a=p)) u i j := by
  unfold extras ordinaryTasks total
  rw [List.map_map, Finset.sum_map_toList]
  let f := fun a => (ordinaryProposal (frames a) (labels a) a (owners a)
    (fun i => u i a)).extra i j p
  change (∑ a∈tasks, f a)=_
  have hz : ∀ a∈tasks, a≠j → f a=0 := by
    intro a _ haj
    simp [f, ordinaryProposal, Proposal.extra, Ne.symm haj]
  by_cases hj : j∈tasks
  · have hs : (∑ a∈tasks, f a)=f j := by
      apply Finset.sum_eq_single j
      · exact hz
      · intro hnot
        exact False.elim (hnot hj)
    rw [hs]
    by_cases hp : labels j=p <;> by_cases hu : 0<u j j <;>
      simp [f, ordinaryProposal, Proposal.extra, batchLoss, retainedDeficit, hj, hp, hu, eq_comm]
  · have hs : (∑ a∈tasks, f a)=0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply hz a ha
      intro heq
      exact hj (heq ▸ ha)
    rw [hs]
    simp [batchLoss, hj]

end TaskIdentification

section OwnCostIdentity

variable {Agent Root : Type*} [Fintype Agent] [DecidableEq Agent]

def Allocation.ownCost (a : Allocation Agent Root) (i : Agent) : ℝ :=
  a.cost i (a.owner.symm i)

/-- The permutation gives each observer exactly one own prefix, so summing label credits is exact. -/
theorem allocation_own_identity (a : Allocation Agent Root) (i : Agent) :
    ∑ p, a.credit i p = a.baseline i-a.ownCost i := by
  have hs : (∑ p, a.credit i p)=a.credit i (a.owner.symm i) := by
    apply Finset.sum_eq_single (a.owner.symm i)
    · intro p _ hp
      have howner : a.owner p≠i := by
        intro h
        apply hp
        exact a.owner.injective (by simpa using h)
      simp [Allocation.credit, howner]
    · simp
  rw [hs]
  simp [Allocation.credit, Allocation.ownCost]

theorem frozen_own_identity (frozen : List (Allocation Agent Root)) (i : Agent) :
    (∑ p, total frozen (fun a => a.credit i p)) =
      total frozen (fun a => a.baseline i)-total frozen (fun a => a.ownCost i) := by
  induction frozen with
  | nil => simp
  | cons a rest ih =>
    simp only [total_cons, Finset.sum_add_distrib, allocation_own_identity, ih]
    ring

omit [Fintype Agent] [DecidableEq Agent] in
theorem frame_own_cost (f : Frame Agent Root) (hf : f.Good) (i : Agent) :
    f.allocation.ownCost i=f.baseline i := by
  have ha : i∈f.allowed (f.owner.symm i) := by simpa using hf.1 (f.owner.symm i)
  simpa [Allocation.ownCost, Frame.allocation] using hf.2 (f.owner.symm i) i ha

/-- The exact frozen own-cost identity is a consequence of the allocation records, not an input. -/
theorem package_frozen_own_identity (s : Package Agent Root) (i : Agent) :
    total s.frozen (fun a => a.ownCost i) =
      total s.frozen (fun a => a.baseline i)-∑ p, s.credit i p := by
  have h := frozen_own_identity s.frozen i
  change _ = _-∑ p, total s.frozen (fun a => a.credit i p)
  linarith

def Package.allocations (s : Package Agent Root) : List (Allocation Agent Root) :=
  s.frozen++s.live.toList.map Frame.allocation

/-- All actual roots, including the live equalizer root, satisfy the exact own-cost identity. -/
theorem package_actual_own_identity (s : Package Agent Root) (hs : s.Valid) (i : Agent) :
    total s.allocations (fun a => a.ownCost i) =
      total s.allocations (fun a => a.baseline i)-∑ p, s.credit i p := by
  have h := package_frozen_own_identity s i
  cases he : s.live with
  | none => simpa [Package.allocations, he] using h
  | some f =>
    have hf := frame_own_cost f (hs.live_good f he) i
    simp only [Package.allocations, he, Option.toList_some, List.map_cons, List.map_nil,
      total_append, total_cons, total_nil, add_zero]
    change total s.frozen (fun a => a.ownCost i)+f.allocation.ownCost i =
      total s.frozen (fun a => a.baseline i)+f.baseline i-∑ p, s.credit i p
    rw [hf]
    linarith

end OwnCostIdentity

section CommittedRounds

variable {Agent Root : Type*} [DecidableEq Agent]

/-- A local group is computed in isolation. It is not inserted into an old active pool. -/
inductive GroupUpdate : List (Package Agent Root) → Package Agent Root → Prop
  | reset (s : Package Agent Root) (owner : Equiv.Perm Agent)
      (hallowed : ∀ f, s.live=some f → ∀ p, owner p∈f.allowed p) :
      GroupUpdate [s] (s.reset owner)
  | close (s : Package Agent Root) : GroupUpdate [s] s.close
  | ordinary (s : Package Agent Root) (donors : List (Donation Agent Root))
      (before next : Frame Agent Root) (hlive : s.live=some before)
      (hroot : next.root=before.root)
      (hbaseline : next.baseline=before.baseline)
      (hequalizer : next.equalizerCost=before.equalizerCost)
      (hd : ∀ d∈donors, d.WellFormed)
      (hmode : ∀ d∈donors, d.proposal.execute=decide (0<d.proposal.utility d.proposal.recipient))
      (hn : next.Good) (hpay : ExclusivePayment s donors next) :
      GroupUpdate (s::donors.map Donation.package) (mergeOpen s donors next)
  | affine (s : Package Agent Root) (donors : List (Donation Agent Root))
      (hd : ∀ d∈donors, d.WellFormed)
      (hmode : ∀ d∈donors, d.proposal.execute=true)
      (hpay : ∀ i j p, i≠j → extras donors i j p≤payments donors i p) :
      GroupUpdate (s::donors.map Donation.package) (mergeClosed s donors)

theorem group_update_valid {before : List (Package Agent Root)} {after : Package Agent Root}
    (step : GroupUpdate before after) (hbefore : ∀ s∈before, s.Valid) : after.Valid := by
  cases step with
  | reset s owner hallowed =>
    exact package_reset_valid s (hbefore s (by simp)) owner hallowed
  | close s => exact package_close_valid s (hbefore s (by simp))
  | ordinary s donors old next hlive hroot hbaseline hequalizer hd hmode hn hpay =>
    apply merge_open_valid s (hbefore s (by simp)) donors hd ?_ next hn hpay
    intro d hmem
    exact hbefore d.package (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hmem, rfl⟩))
  | affine s donors hd hmode hpay =>
    apply merge_closed_valid s (hbefore s (by simp)) donors hd ?_ hpay
    intro d hmem
    exact hbefore d.package (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hmem, rfl⟩))

/-- Nominal zero donors are still consumed exactly once: every input root ID is retained. -/
theorem group_update_ids {before : List (Package Agent Root)} {after : Package Agent Root}
    (step : GroupUpdate before after) : after.ids.Perm (before.flatMap Package.ids) := by
  cases step with
  | reset s owner hallowed => simp
  | close s => simp
  | ordinary s donors old next hlive hroot hbaseline hequalizer hd hmode hn hpay =>
    simpa [List.flatMap_map] using merge_open_ids s donors old next hlive hroot hd
  | affine s donors hd hmode hpay =>
    rw [merge_closed_ids s donors hd]
    simp [List.flatMap_map]

/-- All old inputs are reserved before group computations; all outputs commit together. -/
def CommittedRound (before after : List (Package Agent Root)) : Prop :=
  ∃ groups : List (List (Package Agent Root)),
    groups.flatten.Perm before ∧ List.Forall₂ GroupUpdate groups after

def PoolValid (pool : List (Package Agent Root)) : Prop := ∀ s∈pool, s.Valid

def PoolDistinct (pool : List (Package Agent Root)) : Prop :=
  (pool.flatMap Package.ids).Nodup

theorem groups_valid {groups : List (List (Package Agent Root))}
    {outputs : List (Package Agent Root)} (hgroups : List.Forall₂ GroupUpdate groups outputs)
    (hbefore : PoolValid groups.flatten) : PoolValid outputs := by
  induction hgroups with
  | nil => simp [PoolValid]
  | @cons group output groups outputs hstep htail ih =>
    intro s hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst s
      apply group_update_valid hstep
      intro p hp
      exact hbefore p (by simp [hp])
    · apply ih ?_ s hs
      intro p hp
      exact hbefore p (by simp [hp])

theorem groups_ids {groups : List (List (Package Agent Root))}
    {outputs : List (Package Agent Root)} (hgroups : List.Forall₂ GroupUpdate groups outputs) :
    (outputs.flatMap Package.ids).Perm (groups.flatten.flatMap Package.ids) := by
  induction hgroups with
  | nil => simp
  | @cons group output groups outputs hstep htail ih =>
    simpa [List.flatMap_append] using (group_update_ids hstep).append ih

theorem committed_round_valid {before after : List (Package Agent Root)}
    (step : CommittedRound before after) (hbefore : PoolValid before) : PoolValid after := by
  obtain ⟨groups, hpartition, hgroups⟩ := step
  apply groups_valid hgroups
  intro s hs
  exact hbefore s (hpartition.mem_iff.mp hs)

theorem committed_round_ids {before after : List (Package Agent Root)}
    (step : CommittedRound before after) :
    (after.flatMap Package.ids).Perm (before.flatMap Package.ids) := by
  obtain ⟨groups, hpartition, hgroups⟩ := step
  exact (groups_ids hgroups).trans (hpartition.flatMap_right Package.ids)

theorem committed_round_distinct {before after : List (Package Agent Root)}
    (step : CommittedRound before after) (hbefore : PoolDistinct before) : PoolDistinct after :=
  (committed_round_ids step).nodup_iff.mpr hbefore

/-- Executions are finite sequences of complete commits, not sequences of transient mixed-phase pools. -/
abbrev Execution := Relation.ReflTransGen (@CommittedRound Agent Root _)

theorem execution_valid {before after : List (Package Agent Root)}
    (run : Execution before after) (hbefore : PoolValid before) : PoolValid after := by
  induction run with
  | refl => exact hbefore
  | tail prior step ih => exact committed_round_valid step ih

theorem execution_ids {before after : List (Package Agent Root)}
    (run : Execution before after) :
    (after.flatMap Package.ids).Perm (before.flatMap Package.ids) := by
  induction run with
  | refl => rfl
  | tail prior step ih => exact (committed_round_ids step).trans ih

theorem execution_distinct {before after : List (Package Agent Root)}
    (run : Execution before after) (hbefore : PoolDistinct before) : PoolDistinct after :=
  (execution_ids run).nodup_iff.mpr hbefore

/-- Every committed package retains the actual frozen-deficit/live-reserve invariant. -/
theorem execution_budget {before after : List (Package Agent Root)}
    (run : Execution before after) (hbefore : PoolValid before)
    (s : Package Agent Root) (hs : s∈after) (i j p : Agent) (hij : i≠j) :
    s.debit i j p + s.reserve i j p ≤ s.credit i p :=
  (execution_valid run hbefore s hs).budget i j p hij

end CommittedRounds

end EnvyFreeResearch.ChoreComposition
