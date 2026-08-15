This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# CircomAuditMVP — start here

The smallest complete version of this project's circuit-audit story: five Lean
files and two pages of prose.

```
lake build CircomAuditMVP
```

* `CircomAuditMVP/Semantics.lean` — R1CS over `ZMod p`; solutions `Sol`; the
  input projection `proj` (`π`); the properties `Deterministic` (not
  under-constrained), `DeterministicOn` (outputs only), `Complete`,
  `CorrectWrt R`; the bridge `Constraint.ofStandard_sat_iff` to the deployed
  `A · B = C` form of `.r1cs`; and the headline theorem
  `deterministic_iff_sol_eq_range_gen`: with a sound, faithful witness
  generator, `Deterministic ↔ Sol = Set.range gen` — **under-constrainedness is
  exactly the gap between the constraint system and the witness generator**.
* `CircomAuditMVP/Check.lean` — `checkDeterministic`, a `decide`-based exact
  checker, with `checkDeterministic_eq_true_iff` proving it **sound and
  complete**. Kernel checked; no `native_decide`. Exponential, so it is a
  reference oracle for tiny circuits.
* `CircomAuditMVP/Propagate.lean` — `checkPropagate`, a **polynomial**,
  field-agnostic checker by constraint propagation, with soundness proved
  (`deterministic_of_checkPropagate`). Deliberately one-sided: `false` means
  "not certified", never "buggy".
* `CircomAuditMVP/Examples.lean` — `out <== x*y` proved safe (over any
  commutative ring, and by the exact checker over `ZMod 5`); `out <-- x*y`
  proved under-constrained, with the accepted-but-impossible witness
  `(x, y, out) = (0, 0, 1)` exhibited.
* `CircomAuditMVP/Scale.lean` — the two checkers side by side, and
  `chain_deterministic`: a twelve-signal circuit, `5^12` witnesses, proved not
  under-constrained by propagation without enumerating anything.
* `SPEC.md` — the specification: theorem statements verbatim, the trust list,
  scope tiers, and a five-axis comparison with Picus, circomspect, Coda, and
  published Circom/Poseidon formalisations.
* `REVIEW.md` — an honest review of this MVP against the three questions asked
  at open office hours: what it answers, what it does not, and where the
  remaining weaknesses are.

Nothing here uses `sorry`, added axioms, or `native_decide`; the principal
theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
