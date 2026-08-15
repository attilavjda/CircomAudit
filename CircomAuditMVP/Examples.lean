import CircomAuditMVP.Check

/-!
# CircomAudit MVP — two circuits: one safe, one under-constrained

Both circuits have three signals `x`, `y`, `out` (indices `0`, `1`, `2`) and
declare `x, y` as inputs.  They differ only in what the author wrote in Circom.

## The safe circuit

```circom
template Mul() {
  signal input x; signal input y; signal output out;
  out <== x * y;          // assign *and* constrain
}
```

`<==` emits the constraint `x * y - out = 0`, so `out` is pinned down:
`mul_deterministic` proves `Deterministic` over an arbitrary commutative ring,
and `checkDeterministic` also returns `true` by kernel computation over `ZMod 5`.

## The buggy circuit

```circom
template MulBug() {
  signal input x; signal input y; signal output out;
  out <-- x * y;          // assignment ONLY: no constraint is emitted
  x * 0 === 0;            // a constraint that says nothing
}
```

`<--` emits no constraint, so `out` is free: any value is accepted.  This is the
classic under-constrained bug.  `mulBug_not_deterministic` exhibits the exploit
concretely — two accepted witnesses with the same inputs — and
`mulBug_extra_witness_outside_generator` shows the same witness is one the
honest witness generator would never produce, instantiating the headline theorem
`not_deterministic_iff_exists_extra_witness`.
-/

namespace CircomAuditMVP

open Lin

/-- The two input signals of both circuits: `x` at index `0`, `y` at index `1`. -/
def inpXY : Fin 2 → Fin 3 := ![0, 1]

/-! ## The safe circuit `out <== x * y` -/

section Safe

variable {F : Type*} [CommRing F]

/-- The constraint `x * y - out = 0` emitted by `out <== x * y`. -/
def mulSystem : System 3 F := [⟨var 0, var 1, ⟨0, ![0, 0, -1]⟩⟩]

@[simp] lemma mulSystem_sat_iff (w : Fin 3 → F) :
    (mulSystem : System 3 F).sat w ↔ w 0 * w 1 = w 2 := by
  constructor
  · intro h
    have := h _ (List.mem_singleton_self _)
    simp [Constraint.sat, Lin.eval, Lin.var, Fin.sum_univ_three] at this
    linear_combination this
  · intro h con hcon
    simp only [mulSystem, List.mem_singleton] at hcon
    subst hcon
    simp [Constraint.sat, Lin.eval, Lin.var, Fin.sum_univ_three]
    linear_combination h

/-- **The safe circuit is not under-constrained**: the inputs `x, y` determine
every signal.  True over any commutative ring, hence over every scalar field a
Circom deployment might use. -/
theorem mul_deterministic : Deterministic (mulSystem : System 3 F) inpXY := by
  intro w w' hw hw' hp
  rw [mulSystem_sat_iff] at hw hw'
  have h0 : w 0 = w' 0 := congrFun hp 0
  have h1 : w 1 = w' 1 := congrFun hp 1
  have h2 : w 2 = w' 2 := by rw [← hw, ← hw', h0, h1]
  funext i
  fin_cases i <;> assumption

/-- The safe circuit is also complete: every input pair is accepted, witnessed
by the honest generator `⟨x, y⟩ ↦ ⟨x, y, x*y⟩`. -/
theorem mul_complete : Complete (mulSystem : System 3 F) inpXY := by
  refine complete_of_generator _ inpXY (fun x => ![x 0, x 1, x 0 * x 1]) ?_ ?_
  · intro x; simp [mulSystem_sat_iff]
  · intro x; funext j; fin_cases j <;> simp [proj, inpXY]

/-- Functional correctness against the auditor's specification "`out` is the
product of the inputs". -/
theorem mul_correct :
    CorrectWrt (mulSystem : System 3 F) inpXY (fun x w => w 2 = x 0 * x 1) := by
  intro w hw
  rw [mulSystem_sat_iff] at hw
  simp [proj, inpXY, ← hw]

end Safe

set_option maxRecDepth 100000 in
/-- The decidable checker agrees with `mul_deterministic`, by kernel
computation over `ZMod 5`. -/
theorem mul_check_true : checkDeterministic (mulSystem : System 3 (ZMod 5)) inpXY = true := by
  decide

/-! ## The buggy circuit `out <-- x * y` -/

/-- The buggy circuit's only constraint, `x * 0 === 0`: it constrains nothing,
and `out` is never mentioned. -/
def mulBugSystem : System 3 (ZMod 5) := [⟨var 0, ⟨0, ![0, 0, 0]⟩, ⟨0, ![0, 0, 0]⟩⟩]

/-- Every assignment satisfies the buggy system. -/
lemma mulBugSystem_sat (w : Fin 3 → ZMod 5) : mulBugSystem.sat w := by
  intro con hcon
  simp only [mulBugSystem, List.mem_singleton] at hcon
  subst hcon
  simp [Constraint.sat, Lin.eval, Lin.var, Fin.sum_univ_three]

/-- The honest witness generator the Circom compiler emits for `out <-- x * y`. -/
def mulBugGen (x : Fin 2 → ZMod 5) : Fin 3 → ZMod 5 := ![x 0, x 1, x 0 * x 1]

lemma mulBugGen_sound : GenSound mulBugSystem mulBugGen := fun _ => mulBugSystem_sat _

lemma mulBugGen_faithful : GenFaithful inpXY mulBugGen := by
  intro x; funext j; fin_cases j <;> simp [proj, inpXY, mulBugGen]

/-- **The bug, exhibited.**  On inputs `x = y = 0` the verifier accepts both
`out = 0` and `out = 1`: the circuit is under-constrained. -/
theorem mulBug_not_deterministic : ¬ Deterministic mulBugSystem inpXY := by
  intro h
  have hcol := h ![0, 0, 0] ![0, 0, 1] (mulBugSystem_sat _) (mulBugSystem_sat _) (by decide)
  have h2 : (0 : ZMod 5) = 1 := by simpa using congrFun hcol 2
  exact absurd h2 (by decide)

/-- The same fact as the checker sees it: the decision procedure returns
`false`, and by `not_deterministic_of_check_false` that answer is a proof. -/
theorem mulBug_check_false : checkDeterministic mulBugSystem inpXY = false := by
  have : ¬ Deterministic mulBugSystem inpXY := mulBug_not_deterministic
  simpa [checkDeterministic] using this

/-- **The exploit witness.**  `⟨x, y, out⟩ = ⟨0, 0, 1⟩` is accepted by the
verifier but is outside the range of the honest witness generator: a prover can
claim `0 * 0 = 1`. -/
theorem mulBug_extra_witness_outside_generator :
    mulBugSystem.sat ![0, 0, 1] ∧ (![0, 0, 1] : Fin 3 → ZMod 5) ∉ Set.range mulBugGen := by
  refine ⟨mulBugSystem_sat _, ?_⟩
  rintro ⟨x, hx⟩
  have h0 : x 0 = 0 := by simpa using congrFun hx 0
  have h1 : x 1 = 0 := by simpa using congrFun hx 1
  have h2 := congrFun hx 2
  rw [mulBugGen] at h2
  simp [h0, h1] at h2
  exact absurd h2 (by decide)

/-- Instantiating the headline theorem: for this circuit, "under-constrained"
and "the solution set is strictly bigger than what the generator produces" are
literally the same statement. -/
theorem mulBug_gap :
    ¬ Deterministic mulBugSystem inpXY ↔
      ∃ w, mulBugSystem.sat w ∧ w ∉ Set.range mulBugGen :=
  not_deterministic_iff_exists_extra_witness mulBugSystem inpXY mulBugGen
    mulBugGen_sound mulBugGen_faithful

end CircomAuditMVP
