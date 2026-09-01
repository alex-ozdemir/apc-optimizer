import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! **The soundness argument's ordering on stateful state.** Nothing here is audited.

    `maintains_of_stateful_active` derives the memory byte invariant by strong induction, and an
    induction needs something to descend on. A `RankModel` is that something: a natural-number rank
    on bus messages.

    It is *not* part of the VM. No field of `Host` mentions it, and neither does `VmSat`,
    `CanProduce`, `VmEquivalent` — nor, since the layout redesign, `Circuit.legalGuest`. A reader
    checking what the correctness theorem *says*, or what it requires of a guest chip, never meets
    it. It appears only as a parameter of `Host.realizes`, which the argument discharges once per
    VM, and is inferred rather than written at every use site.

    What a chip promises is stated in `StepLayout`'s own coordinates: every stateful interaction
    sits at an integer offset from its step's base, and a send comes after everything it is
    justified by. Turning that into a rank order is this file's job and the VM's — see
    `Host.ordersRanks` — because only the VM knows where a step's base sits on the global clock. -/

variable {p : ℕ}

/-- A rank on stateful bus messages.

    For OpenVM: a message's timestamp, shifted into the naturals by the maximum lookback
    (`openVmRank`). A rank reads a field element as a natural number, so "the rank went up" is the
    order it looks like only while ranks stay inside a window too narrow to wrap — which is what
    `bound` records. -/
structure RankModel (p : ℕ) where
  /-- How the argument orders stateful state — for OpenVM, a shifted timestamp. -/
  rank : BusMessage p → ℕ
  /-- How far `rank` may reach in a run the VM will accept. -/
  bound : ℕ

/-- **Offsets order ranks.** Within one guest instance, an interaction placed earlier in its
    step's window has the smaller rank.

    This is the whole of what the soundness induction needs from the VM, and it is what replaced a
    *bound* on every rank: `StepLayout.sendsOk` hands a chip the interactions before its send, and
    the induction can only supply those at a strictly smaller rank.

    It is a genuinely multi-chip fact, which is why it is not a conjunct of `VmSat` and not a
    clause of legality: a step's offsets are relative to its own `base`, and only the execution
    bridge — walked across the whole run — says where that base sits on the global clock. See
    `Host.ordersRanks` and, for OpenVM, `openVmHost_ordersRanks`. -/
def VmAssignment.ordersRanks {vm : Vm p} (a : VmAssignment p vm) (rm : RankModel p)
    (r : GuestBusRules p) (maxWindow maxLookback : ℕ) : Prop :=
  ∀ (t : Fin vm.guest.length) (asg : ChipAssignment p), asg ∈ a.guestAssignments t →
    ∀ L : StepLayout (vm.guest.get t) r asg maxWindow maxLookback,
      ∀ i j : Fin (vm.guest.get t).busInteractions.length,
        (vm.guest.get t).activeStateful r asg i → (vm.guest.get t).activeStateful r asg j →
          L.tOffset j < L.tOffset i →
            rm.rank ((vm.guest.get t).msgAt asg j) < rm.rank ((vm.guest.get t).msgAt asg i)

/-- `Circuit.allEffects` as a guarded sum indexed by interaction position. -/
theorem allEffects_eq_sum_fin (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) :
    c.allEffects asg m
      = ∑ i : Fin c.busInteractions.length, (if c.msgAt asg i = m then c.multAt asg i else 0) := by
  have hmapIf : c.allEffects asg m = (c.busInteractions.map (fun bi =>
      if ((bi.eval asg).busId, (bi.eval asg).payload) = m then (bi.eval asg).multiplicity
      else 0)).sum := by
    simp only [Circuit.allEffects]
    induction c.busInteractions with
    | nil => simp
    | cons bi t ih =>
      simp only [List.map_cons, List.filter_cons, List.sum_cons, ← ih]
      by_cases h : ((bi.eval asg).busId, (bi.eval asg).payload) = m
      · rw [if_pos h, decide_eq_true h]; simp
      · rw [if_neg h, decide_eq_false h]; simp
  rw [hmapIf]
  conv_lhs => rw [← List.ofFn_get c.busInteractions, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl (fun i _ => by simp [Circuit.msgAt, Circuit.multAt])

/-- **A step's net memory receives sit strictly before its own window.** The other half of what
    `StepLayout.memSendsOk` needs: its hypothesis quantifies over messages the step *nets* a
    receive on, and the induction can only supply those at a strictly smaller rank.

    Like `ordersRanks` this is genuinely multi-chip, and for the same reason — it is exactly the
    fact `memSendsOk`'s docstring defers to the whole run. A message a step net-receives inside its
    own window would have to be sent by someone whose window overlaps it, and distinct steps'
    windows are disjoint (`VmChain.Chain.windows_disjoint`). See `Host.receivesArePast`; OpenVM has
    no instance of it yet, so every theorem taking one is currently conditional. -/
def VmAssignment.receivesArePast {vm : Vm p} (a : VmAssignment p vm)
    (r : GuestBusRules p) (maxWindow maxLookback : ℕ) : Prop :=
  ∀ (t : Fin vm.guest.length) (asg : ChipAssignment p), asg ∈ a.guestAssignments t →
    ∀ L : StepLayout (vm.guest.get t) r asg maxWindow maxLookback,
      ∀ k : Fin (vm.guest.get t).busInteractions.length,
        (vm.guest.get t).activeMem r asg k →
        (vm.guest.get t).allEffects asg ((vm.guest.get t).msgAt asg k) = -1 →
          L.tOffset k < 0

/-- **A step's own net memory receive is a genuine receive.** `StepLayout.memSendsOk`'s hypothesis
    is a bare fact about `allEffects` — no interaction index, no offset. This recovers a concrete
    witness: the unique interaction that carries the message, at multiplicity `-1`.

    Pure `StepLayout` bookkeeping — `statefulPolarity` pins every active stateful multiplicity to
    `0`/`1`/`-1`, and `memInteractionsUnique` rules out two distinct interactions both carrying `m`
    at the same multiplicity, so a net of `-1` can only come from one `-1` and no `1`. Nothing
    cross-step yet: `tOffset_neg_of_recv` is where the whole run enters. -/
theorem exists_recv_of_allEffects_neg_one {c : Circuit p} {r : GuestBusRules p}
    {asg : ChipAssignment p} {maxWindow maxLookback : ℕ}
    (L : StepLayout c r asg maxWindow maxLookback)
    (hpol : c.statefulPolarity r) (hsat : c.satisfiesAlgebraic asg)
    (hstateful : r.isStateful r.memBusId = true)
    (hne0 : (-1 : ZMod p) ≠ 0)
    {m : BusMessage p} (hmemBus : m.1 = r.memBusId) (hnet : c.allEffects asg m = -1) :
    ∃ k : Fin c.busInteractions.length,
      c.activeMem r asg k ∧ c.multAt asg k = -1 ∧ c.msgAt asg k = m := by
  classical
  have hone_ne_zero : (1 : ZMod p) ≠ 0 := fun h => hne0 (neg_eq_zero.mpr h)
  by_contra hcon
  -- Every active interaction on `m` other than a `-1` must be a `1`.
  have hone : ∀ i : Fin c.busInteractions.length, c.activeMem r asg i → c.msgAt asg i = m →
      c.multAt asg i = 1 := by
    intro i hact hmsg
    rcases hpol asg hsat _ (List.get_mem c.busInteractions i) hact.1.1 with h0 | h1 | hm1
    · exact absurd h0 hact.1.2
    · exact h1
    · exact absurd (⟨i, hact, hm1, hmsg⟩ : ∃ k : Fin c.busInteractions.length,
        c.activeMem r asg k ∧ c.multAt asg k = -1 ∧ c.msgAt asg k = m) hcon
  -- Hence at most one interaction is active on `m` at all.
  have huniq : ∀ i j : Fin c.busInteractions.length, c.activeMem r asg i → c.activeMem r asg j →
      c.msgAt asg i = m → c.msgAt asg j = m → i = j := fun i j hi hj hmi hmj =>
    L.memInteractionsUnique i j hi hj (hmi.trans hmj.symm) ((hone i hi hmi).trans (hone j hj hmj).symm)
  -- `msgAt = m` and a nonzero multiplicity is exactly `activeMem` here.
  have hmkActive : ∀ i : Fin c.busInteractions.length, c.msgAt asg i = m → c.multAt asg i ≠ 0 →
      c.activeMem r asg i := by
    intro i hmi hne
    have hbeq : (c.busInteractions.get i).busId = r.memBusId := by
      have hb : (c.msgAt asg i).1 = m.1 := congrArg Prod.fst hmi
      show (c.busInteractions.get i).busId = r.memBusId
      rw [show (c.busInteractions.get i).busId = (c.msgAt asg i).1 from rfl, hb, hmemBus]
    exact ⟨⟨by rw [hbeq]; exact hstateful, hne⟩, hbeq⟩
  have hf : ∀ i : Fin c.busInteractions.length,
      (if c.msgAt asg i = m then c.multAt asg i else 0) = 0 ∨
      (if c.msgAt asg i = m then c.multAt asg i else 0) = 1 := by
    intro i
    by_cases hmi : c.msgAt asg i = m
    · by_cases hz : c.multAt asg i = 0
      · exact Or.inl (by rw [if_pos hmi, hz])
      · exact Or.inr (by rw [if_pos hmi]; exact hone i (hmkActive i hmi hz) hmi)
    · exact Or.inl (if_neg hmi)
  have hcard : (Finset.univ.filter
      (fun i : Fin c.busInteractions.length =>
        (if c.msgAt asg i = m then c.multAt asg i else 0) = 1)).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr (fun {i j} hi hj => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have hmi : c.msgAt asg i = m := by by_contra h; rw [if_neg h] at hi; exact hone_ne_zero hi.symm
    have hmj : c.msgAt asg j = m := by by_contra h; rw [if_neg h] at hj; exact hone_ne_zero hj.symm
    rw [if_pos hmi] at hi
    rw [if_pos hmj] at hj
    have hai := hmkActive i hmi (by rw [hi]; exact hone_ne_zero)
    have haj := hmkActive j hmj (by rw [hj]; exact hone_ne_zero)
    exact huniq i j hai haj hmi hmj
  have hsum := allEffects_eq_sum_fin c asg m
  have hboole : ∑ i : Fin c.busInteractions.length,
      (if c.msgAt asg i = m then c.multAt asg i else 0)
      = ((Finset.univ.filter (fun i : Fin c.busInteractions.length =>
          (if c.msgAt asg i = m then c.multAt asg i else 0) = 1)).card : ZMod p) := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases hf i with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [hsum, hboole] at hnet
  have hn01 : (Finset.univ.filter (fun i : Fin c.busInteractions.length =>
      (if c.msgAt asg i = m then c.multAt asg i else 0) = 1)).card = 0 ∨
      (Finset.univ.filter (fun i : Fin c.busInteractions.length =>
      (if c.msgAt asg i = m then c.multAt asg i else 0) = 1)).card = 1 := by omega
  rcases hn01 with h0 | h1
  · rw [h0, Nat.cast_zero] at hnet; exact hne0 hnet.symm
  · -- One interaction carries `m`, at multiplicity `1`. The net says `1 = -1`, so that
    -- interaction is itself the receive we assumed absent — no `-1 ≠ 1` needed.
    rw [h1, Nat.cast_one] at hnet
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
    have hkmem : k ∈ Finset.univ.filter (fun i : Fin c.busInteractions.length =>
        (if c.msgAt asg i = m then c.multAt asg i else 0) = 1) := by rw [hk]; exact Finset.mem_singleton_self k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkmem
    have hmk : c.msgAt asg k = m := by
      by_contra h; rw [if_neg h] at hkmem; exact hone_ne_zero hkmem.symm
    rw [if_pos hmk] at hkmem
    exact hcon ⟨k, hmkActive k hmk (by rw [hkmem]; exact hone_ne_zero), hkmem.trans hnet, hmk⟩

/-- **A step that nets a receive on a memory message does not also send it.**
    `memInteractionsUnique` caps a step at one send and one receive of any given message, so a
    send would cancel the receive and leave a net of `0` rather than `-1`. -/
theorem not_memSend_of_allEffects_neg_one {c : Circuit p} {r : GuestBusRules p}
    {asg : ChipAssignment p} {maxWindow maxLookback : ℕ}
    (L : StepLayout c r asg maxWindow maxLookback)
    (hpol : c.statefulPolarity r) (hsat : c.satisfiesAlgebraic asg)
    (hstateful : r.isStateful r.memBusId = true)
    (hne0 : (-1 : ZMod p) ≠ 0) (hne1 : (-1 : ZMod p) ≠ 1)
    {m : BusMessage p} (hmemBus : m.1 = r.memBusId) (hnet : c.allEffects asg m = -1)
    {j : Fin c.busInteractions.length} (hactj : c.activeMem r asg j)
    (hmultj : c.multAt asg j = 1) (hmsgj : c.msgAt asg j = m) : False := by
  classical
  obtain ⟨k, hactk, hmultk, hmsgk⟩ :=
    exists_recv_of_allEffects_neg_one L hpol hsat hstateful hne0 hmemBus hnet
  have hjk : j ≠ k := fun h => hne1 (by rw [← hmultk, ← h, hmultj])
  -- Off `j` and `k` every guarded term vanishes: a `1` would be `j`, a `-1` would be `k`.
  have hrest : ∀ i : Fin c.busInteractions.length, i ∈ Finset.univ → i ≠ j ∧ i ≠ k →
      (if c.msgAt asg i = m then c.multAt asg i else 0) = 0 := by
    rintro i - ⟨hij, hik⟩
    by_cases hmi : c.msgAt asg i = m
    · rw [if_pos hmi]
      by_cases hz : c.multAt asg i = 0
      · exact hz
      have hbeq : (c.busInteractions.get i).busId = r.memBusId := by
        have hb : (c.msgAt asg i).1 = m.1 := congrArg Prod.fst hmi
        rw [show (c.busInteractions.get i).busId = (c.msgAt asg i).1 from rfl, hb, hmemBus]
      have hacti : c.activeMem r asg i := ⟨⟨by rw [hbeq]; exact hstateful, hz⟩, hbeq⟩
      rcases hpol asg hsat _ (List.get_mem c.busInteractions i) hacti.1.1 with h0 | h1 | hm1
      · exact absurd h0 hz
      · exact absurd (L.memInteractionsUnique i j hacti hactj (hmi.trans hmsgj.symm)
          (h1.trans hmultj.symm)) hij
      · exact absurd (L.memInteractionsUnique i k hacti hactk (hmi.trans hmsgk.symm)
          (hm1.trans hmultk.symm)) hik
    · exact if_neg hmi
  have hsum := allEffects_eq_sum_fin c asg m
  rw [Finset.sum_eq_add_of_mem j k (Finset.mem_univ j) (Finset.mem_univ k) hjk hrest,
    if_pos hmsgj, if_pos hmsgk, hmultj, hmultk, add_neg_cancel] at hsum
  exact hne0 (hnet.symm.trans hsum)
