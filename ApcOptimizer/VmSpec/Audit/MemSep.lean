import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity
import ApcOptimizer.VmSpec.Audit.Apc2105000
import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! **A static check for `StepLayout.memInteractionsUnique`.**

    The clause compares two active memory interactions *at the same multiplicity*, so it never has
    to separate a read from the write that closes it. What is left splits into reasons a `Bool` can
    settle on the circuit alone: an interaction whose multiplicity folds to `0` is never
    `activeMem`; two whose address column folds to different constants carry different messages; two
    whose multiplicities do are excluded by the clause's own hypothesis.

    `Expression.foldConstWith` is what makes this reach a real APC — powdr leaves the address as a
    column, and only the circuit's own constraints pin it to a literal.

    The check is *incomplete by construction*: it says nothing about two interactions whose
    separation rests on their timestamps. `apc2105000UnoptChained` needs exactly that and does not
    get it — see `agent-docs/vm-spec-memsep.md`. -/

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

end ApcOptimizer.OpenVM
