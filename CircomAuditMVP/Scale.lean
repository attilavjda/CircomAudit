import CircomAuditMVP.Examples
import CircomAuditMVP.Propagate

/-!
# CircomAudit MVP — the two checkers side by side

`CircomAuditMVP.Check` decides `Deterministic` exactly by exhausting the witness
space; `CircomAuditMVP.Propagate` proves it, one-sidedly, by a linear number of
syntactic passes.  This file exercises both on the same circuits and shows where
each is the right tool.

* On the two-signal multiplier of `CircomAuditMVP.Examples` the two checkers
  agree (`mul_check_true` and `mul_checkPropagate_true`).
* On a chain of ten multiplications (twelve signals) the exhaustive checker is
  already hopeless — it would have to range over `5^12 ≈ 2.4 · 10^8` witnesses,
  i.e. `≈ 6 · 10^16` pairs — while propagation proves determinism by kernel
  computation in a fraction of a second (`chain_deterministic`).
* On the under-constrained circuit, propagation answers `false`.  That answer is
  *not* a proof of a bug (the propagation checker is deliberately one-sided);
  the exhaustive checker is what turns it into one, via
  `not_deterministic_of_check_false`.  The two are complementary, which is the
  intended architecture: a scalable sound pass, backed by a decidable reference
  semantics that acts as ground truth on small instances.
-/

namespace CircomAuditMVP

/-- `ZMod 5` is the toy scalar field used in these examples; the propagation
checker needs it to be a field, and nothing else. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ## The multiplier: both checkers say `true` -/

theorem mul_checkPropagate_true :
    checkPropagate (mulSystem : System 3 (ZMod 5)) inpXY = true := by decide

/-- Determinism of the multiplier, obtained from the *scalable* checker rather
than from exhaustive search. -/
theorem mul_deterministic_via_propagation :
    Deterministic (mulSystem : System 3 (ZMod 5)) inpXY :=
  deterministic_of_checkPropagate mul_checkPropagate_true

/-! ## A circuit far beyond exhaustive search -/

/-- Signal index `i` of a chain circuit with `m + 2` signals. -/
def chainIdx (m i : ℕ) : Fin (m + 2) := ⟨i % (m + 2), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The chain circuit `s(i+2) <== s(i) * s(i+1)` for `i < m`: `m` constraints on
`m + 2` signals, of which the first two are the inputs.  This is the shape of a
Circom template that folds a value through a sequence of multiplications. -/
def chainSystem (m : ℕ) : System (m + 2) (ZMod 5) :=
  (List.range m).map (fun i =>
    ⟨Lin.var (chainIdx m i), Lin.var (chainIdx m (i + 1)),
      ⟨0, fun t => if t = chainIdx m (i + 2) then -1 else 0⟩⟩)

/-- The two inputs of the chain circuit. -/
def chainInp (m : ℕ) : Fin 2 → Fin (m + 2) := ![chainIdx m 0, chainIdx m 1]

set_option maxRecDepth 20000 in
/-- Propagation proves the ten-multiplication chain determined, by kernel
computation. -/
theorem chain_checkPropagate_true : checkPropagate (chainSystem 10) (chainInp 10) = true := by
  decide

/-- **The scalability point**: a twelve-signal circuit, whose witness space has
`5^12` elements, is proved not under-constrained without ever enumerating a
witness. -/
theorem chain_deterministic : Deterministic (chainSystem 10) (chainInp 10) :=
  deterministic_of_checkPropagate chain_checkPropagate_true

/-! ## One-sidedness, stated honestly -/

/-- On the under-constrained circuit the propagation checker declines to certify
determinism. -/
theorem mulBug_checkPropagate_false : checkPropagate mulBugSystem inpXY = false := by decide

/-- A `false` from propagation is only a refusal to certify, so the bug report
still comes from the exact checker.  Here both point the same way. -/
theorem mulBug_bug_confirmed_by_exact_checker : ¬ Deterministic mulBugSystem inpXY :=
  not_deterministic_of_check_false _ _ mulBug_check_false

end CircomAuditMVP
