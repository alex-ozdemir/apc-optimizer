import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity
import ApcOptimizer.VmSpec.Audit.Apc2105000
import ApcOptimizer.VmSpec.Implementation.Rank

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! **Static checks that a circuit's bus interactions carry distinct messages.**

    Two clauses of `StepLayout` need this, at two strengths, and both are decided from the circuit
    alone. `Expression.foldConstWith` is what makes either reach a real APC — powdr leaves the
    address as a column, and only the circuit's own constraints pin it to a literal.

    **`memInteractionsUnique` (`memSepAll`).** The clause compares two active memory interactions
    *at the same multiplicity*, so it never has to separate a read from the write that closes it.
    What is left splits into reasons a `Bool` can settle: an interaction whose multiplicity folds
    to `0` is never `activeMem`; two whose address column folds to different constants carry
    different messages; two whose multiplicities do are excluded by the clause's own hypothesis.
    The check is *incomplete by construction* — it says nothing about two interactions whose
    separation rests on their timestamps, and `apc2105000UnoptChained` needs exactly that and does
    not get it (see `agent-docs/vm-spec.md`).

    **The net at a message (`msgSepAllBut`).** `StepLayout.memSendsOk`'s flat hypothesis speaks of
    messages the step *nets* a receive on, so a receive has to be shown to be the only interaction
    carrying its message — separation of *messages*, not of messages-at-equal-multiplicity. That is
    strictly beyond a `Bool`: a read's echo repeats its address and data and differs only in a
    timestamp, which no static check can bound. So `msgSepAllBut` takes an `exempt` list of the
    pairs the caller separates by hand, off the lt gadget's own lookback bound. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- Two expressions that fold to *different* literal constants, hence differ under every
    assignment satisfying the pin rules. -/
def constDiff (rules : List (PinRule p)) (e f : Expression p) : Bool :=
  match e.foldConstWith rules, f.foldConstWith rules with
  | some a, some b => a != b
  | _, _ => false

theorem constDiff_sound {rules : List (PinRule p)} {e f : Expression p}
    {asg : Variable → ZMod p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (h : constDiff rules e f = true) : e.eval asg ≠ f.eval asg := by
  simp only [constDiff] at h
  cases he : e.foldConstWith rules with
  | none => rw [he] at h; cases h
  | some a =>
    cases hf : f.foldConstWith rules with
    | none => rw [he, hf] at h; cases h
    | some b =>
      rw [he, hf] at h
      simp only [bne_iff_ne, ne_eq] at h
      rw [Expression.foldConstWith_eq hrules he, Expression.foldConstWith_eq hrules hf]
      exact h

/-- An interaction whose multiplicity folds to `0` never satisfies `Circuit.activeMem`. -/
def inactive (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  bi.multiplicity.foldConstWith rules == some 0

/-- Reading a payload column commutes with evaluation, with `.const 0` as the default at both
    ends. -/
theorem getD_map_eval (L : List (Expression p)) (col : ℕ) (asg : Variable → ZMod p) :
    (L.map (fun e => e.eval asg)).getD col 0 = (L.getD col (.const 0)).eval asg := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[col]? <;> rfl

/-- Why two memory interactions cannot collide at the same multiplicity. -/
def memSepOne (rules : List (PinRule p)) (memBus : Nat) (col : ℕ)
    (bi bj : BusInteraction (Expression p)) : Bool :=
  bi.busId != memBus || bj.busId != memBus
    || inactive rules bi || inactive rules bj
    || constDiff rules (bi.payload.getD col (.const 0)) (bj.payload.getD col (.const 0))
    || constDiff rules bi.multiplicity bj.multiplicity

/-- Every distinct pair separated. -/
def memSepAll (rules : List (PinRule p)) (memBus : Nat) (col : ℕ)
    (L : List (BusInteraction (Expression p))) : Bool :=
  (List.finRange L.length).all fun i =>
    (List.finRange L.length).all fun j =>
      i == j || memSepOne rules memBus col (L.get i) (L.get j)

theorem memSepAll_get {rules : List (PinRule p)} {memBus col : ℕ}
    {L : List (BusInteraction (Expression p))} (h : memSepAll rules memBus col L = true)
    {i j : Fin L.length} (hij : i ≠ j) :
    memSepOne rules memBus col (L.get i) (L.get j) = true := by
  simp only [memSepAll, List.all_eq_true] at h
  have := (h i (List.mem_finRange i)) j (List.mem_finRange j)
  simpa [hij] using this

/-- **`StepLayout.memInteractionsUnique`, by static analysis.** -/
theorem memInteractionsUnique_of_sep {c : Circuit p} {r : GuestBusRules p}
    {asg : ChipAssignment p} {rules : List (PinRule p)} {col : ℕ}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (h : memSepAll rules r.memBusId col c.busInteractions = true) :
    ∀ i j : Fin c.busInteractions.length,
      c.activeMem r asg i → c.activeMem r asg j →
      c.msgAt asg i = c.msgAt asg j → c.multAt asg i = c.multAt asg j → i = j := by
  intro i j hi hj hmsg hmult
  by_contra hij
  have hsep := memSepAll_get h hij
  simp only [memSepOne, Bool.or_eq_true, bne_iff_ne, ne_eq, inactive, beq_iff_eq] at hsep
  rcases hsep with ((((hbi | hbj) | hzi) | hzj) | hcol) | hm
  · exact hbi hi.2
  · exact hbj hj.2
  · exact hi.1.2 (Expression.foldConstWith_eq hrules hzi)
  · exact hj.1.2 (Expression.foldConstWith_eq hrules hzj)
  · refine constDiff_sound hrules hcol ?_
    rw [← getD_map_eval, ← getD_map_eval]
    exact congrArg (fun L => L.getD col (0 : ZMod p)) (congrArg Prod.snd hmsg)
  · exact constDiff_sound hrules hm hmult

--------- Separating whole messages, with an escape hatch for the timestamp pairs ---------

/-- Why two interactions cannot both carry one message at a nonzero multiplicity: a different bus,
    a multiplicity folding to `0`, or *any* payload column folding to different constants. -/
def msgSepOne (rules : List (PinRule p)) (bi bj : BusInteraction (Expression p)) : Bool :=
  bi.busId != bj.busId || inactive rules bi || inactive rules bj
    || (List.range (max bi.payload.length bj.payload.length)).any fun col =>
        constDiff rules (bi.payload.getD col (.const 0)) (bj.payload.getD col (.const 0))

/-- Every interaction on `bus` separated from every other interaction, bar the pairs the caller
    names. Restricted to one bus because the guarantee is only ever wanted there — two range-check
    lookups may genuinely carry the same message, and asking the check to rule that out would fail
    on every real circuit. -/
def msgSepAllBut (rules : List (PinRule p)) (bus : Nat) (exempt : List (ℕ × ℕ))
    (L : List (BusInteraction (Expression p))) : Bool :=
  (List.finRange L.length).all fun i =>
    (L.get i).busId != bus ||
      (List.finRange L.length).all fun j =>
        i == j || decide ((i.val, j.val) ∈ exempt) || msgSepOne rules (L.get i) (L.get j)

theorem msgSepOne_sound {c : Circuit p} {asg : ChipAssignment p} {rules : List (PinRule p)}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) {i j : Fin c.busInteractions.length}
    (h : msgSepOne rules (c.busInteractions.get i) (c.busInteractions.get j) = true) :
    c.multAt asg i = 0 ∨ c.multAt asg j = 0 ∨ c.msgAt asg i ≠ c.msgAt asg j := by
  simp only [msgSepOne, Bool.or_eq_true, bne_iff_ne, ne_eq, inactive, beq_iff_eq,
    List.any_eq_true] at h
  rcases h with ((hbus | hzi) | hzj) | ⟨col, -, hcol⟩
  · exact Or.inr (Or.inr fun he => hbus (congrArg Prod.fst he))
  · exact Or.inl (Expression.foldConstWith_eq hrules hzi)
  · exact Or.inr (Or.inl (Expression.foldConstWith_eq hrules hzj))
  · refine Or.inr (Or.inr fun he => constDiff_sound hrules hcol ?_)
    rw [← getD_map_eval, ← getD_map_eval]
    exact congrArg (fun L => L.getD col (0 : ZMod p)) (congrArg Prod.snd he)

theorem msgSepAllBut_get {rules : List (PinRule p)} {bus : Nat} {exempt : List (ℕ × ℕ)}
    {L : List (BusInteraction (Expression p))} (h : msgSepAllBut rules bus exempt L = true)
    {i j : Fin L.length} (hbus : (L.get i).busId = bus) (hij : i ≠ j)
    (hex : (i.val, j.val) ∉ exempt) :
    msgSepOne rules (L.get i) (L.get j) = true := by
  simp only [msgSepAllBut, List.all_eq_true] at h
  have := h i (List.mem_finRange i)
  simp only [hbus, bne_self_eq_false, Bool.false_or, List.all_eq_true] at this
  simpa [hij, hex] using this j (List.mem_finRange j)

/-- **At most one active interaction per message**, from the `Bool` plus the exempt pairs. -/
theorem msgSep_of_sepAllBut {c : Circuit p} {asg : ChipAssignment p} {rules : List (PinRule p)}
    {bus : Nat} {exempt : List (ℕ × ℕ)} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (h : msgSepAllBut rules bus exempt c.busInteractions = true)
    (hex : ∀ i j : Fin c.busInteractions.length, (i.val, j.val) ∈ exempt → i ≠ j →
      c.msgAt asg i ≠ c.msgAt asg j) :
    ∀ i j : Fin c.busInteractions.length, (c.busInteractions.get i).busId = bus →
      c.multAt asg i ≠ 0 → c.multAt asg j ≠ 0 → c.msgAt asg i = c.msgAt asg j → i = j := by
  intro i j hbus hi hj hmsg
  by_contra hij
  by_cases hmem : (i.val, j.val) ∈ exempt
  · exact hex i j hmem hij hmsg
  · rcases msgSepOne_sound hrules (msgSepAllBut_get h hbus hij hmem) with h0 | h0 | h0
    · exact hi h0
    · exact hj h0
    · exact h0 hmsg

/-- **A message no other active interaction carries is netted by its own interaction alone.**
    With `msgSep_of_sepAllBut` this is what turns a memory receive into a net of `-1`, which is
    the form `StepLayout.memSendsOk`'s hypothesis is stated in. -/
theorem allEffects_msgAt_eq_multAt {c : Circuit p} {asg : ChipAssignment p}
    {i : Fin c.busInteractions.length}
    (h : ∀ j : Fin c.busInteractions.length, c.multAt asg j ≠ 0 →
      c.msgAt asg j = c.msgAt asg i → j = i) :
    c.allEffects asg (c.msgAt asg i) = c.multAt asg i := by
  classical
  rw [allEffects_eq_sum_fin, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    by_cases hm : c.msgAt asg j = c.msgAt asg i
    · by_cases hz : c.multAt asg j = 0
      · rw [if_pos hm, hz]
      · exact absurd (h j hz hm) hji
    · exact if_neg hm
  · exact fun hcon => absurd (Finset.mem_univ i) hcon

--------- Evidence: the check clears two of the three real APCs ---------

/-- OpenVM's memory payload is `[address_space, address, data₀..data₃, timestamp]`, so the address
    that separates two interactions sits at column `1`. -/
abbrev memAddrCol : ℕ := 1

def optSepRules : List (PinRule babyBear) :=
  apc2105000Opt.algebraicConstraints.filterMap pinRuleOf

def gatedSepRules : List (PinRule babyBear) :=
  apc2105000GatedPinned.algebraicConstraints.filterMap pinRuleOf

theorem optMemSep :
    memSepAll optSepRules openVmMemBusId memAddrCol apc2105000Opt.busInteractions = true := by
  decide

theorem gatedMemSep :
    memSepAll gatedSepRules openVmMemBusId memAddrCol
      apc2105000GatedPinned.busInteractions = true := by
  decide

/-- The five read/echo pairs, both orders: each is a memory receive and the send that repeats its
    address, which only the lt gadget's lookback bound separates. Every other memory pair carries a
    different literal address. -/
def optExempt : List (ℕ × ℕ) :=
  [(0, 1), (1, 0), (2, 8), (8, 2), (4, 9), (9, 4), (5, 6), (6, 5), (10, 11), (11, 10)]

theorem optMsgSep :
    msgSepAllBut optSepRules openVmMemBusId optExempt apc2105000Opt.busInteractions = true := by
  decide

theorem gatedMsgSep :
    msgSepAllBut gatedSepRules openVmMemBusId optExempt
      apc2105000GatedPinned.busInteractions = true := by
  decide

end ApcOptimizer.OpenVM
