import CircomAuditMVP.Semantics

/-!
# CircomAudit MVP — a decidable checker for under-constrainedness

Over a *finite* field `ZMod p` the whole state space of a small circuit is
finite, so each of the three audit properties of `CircomAuditMVP.Semantics` is
decidable: the checker is a `Bool`-valued function computed by `decide`, and its
correctness statement is an **iff**, so the checker is both

* **sound**   — `check = true` implies the property, and
* **complete** — the property implies `check = true`; a `false` answer is a real
  bug, never a false alarm.

Both directions are kernel-checked.  No `native_decide` is used anywhere here,
so the results below rest only on Lean's kernel, not on a compiled evaluator.

The price is exhaustive search over `(ZMod p)^n`, which is why this MVP checker
is honest about its scope: it is a *reference semantics* and a ground-truth
oracle for tiny circuits and for testing scalable tools, not a production
analyser.  See `SPEC.md`, "Scope tiers".
-/

namespace CircomAuditMVP

variable {n k p : ℕ} [NeZero p]

/-- Decidable version of constraint satisfaction over `ZMod p`. -/
instance (con : Constraint n (ZMod p)) (w : Fin n → ZMod p) : Decidable (con.sat w) := by
  unfold Constraint.sat; infer_instance

instance (S : System n (ZMod p)) (w : Fin n → ZMod p) : Decidable (S.sat w) := by
  unfold System.sat; infer_instance

instance (S : System n (ZMod p)) (inp : Fin k → Fin n) : Decidable (Deterministic S inp) := by
  unfold Deterministic; infer_instance

instance (S : System n (ZMod p)) (inp : Fin k → Fin n) : Decidable (Complete S inp) := by
  unfold Complete; infer_instance

/-- **The checker.**  `true` means "this system is not under-constrained: the
declared inputs determine every signal". -/
def checkDeterministic (S : System n (ZMod p)) (inp : Fin k → Fin n) : Bool :=
  decide (Deterministic S inp)

/-- **Soundness and completeness of the checker**, in one statement. -/
theorem checkDeterministic_eq_true_iff (S : System n (ZMod p)) (inp : Fin k → Fin n) :
    checkDeterministic S inp = true ↔ Deterministic S inp := by
  simp [checkDeterministic]

/-- Sound: a `true` answer is a proof of determinism. -/
theorem deterministic_of_check (S : System n (ZMod p)) (inp : Fin k → Fin n)
    (h : checkDeterministic S inp = true) : Deterministic S inp :=
  (checkDeterministic_eq_true_iff S inp).1 h

/-- Complete: a `false` answer is a proof of under-constrainedness — no false
alarms. -/
theorem not_deterministic_of_check_false (S : System n (ZMod p)) (inp : Fin k → Fin n)
    (h : checkDeterministic S inp = false) : ¬ Deterministic S inp := by
  simpa [checkDeterministic] using h

/-- The companion checker for completeness (every input vector is accepted). -/
def checkComplete (S : System n (ZMod p)) (inp : Fin k → Fin n) : Bool :=
  decide (Complete S inp)

theorem checkComplete_eq_true_iff (S : System n (ZMod p)) (inp : Fin k → Fin n) :
    checkComplete S inp = true ↔ Complete S inp := by
  simp [checkComplete]

/-- When the checker rejects, an explicit pair of distinct accepted witnesses
agreeing on the inputs exists: that pair *is* the exploit an auditor reports. -/
theorem exists_collision_of_check_false (S : System n (ZMod p)) (inp : Fin k → Fin n)
    (h : checkDeterministic S inp = false) :
    ∃ w w' : Fin n → ZMod p, S.sat w ∧ S.sat w' ∧ proj inp w = proj inp w' ∧ w ≠ w' := by
  have := not_deterministic_of_check_false S inp h
  unfold Deterministic at this
  push_neg at this
  obtain ⟨w, w', hw, hw', hp, hne⟩ := this
  exact ⟨w, w', hw, hw', hp, hne⟩

end CircomAuditMVP
