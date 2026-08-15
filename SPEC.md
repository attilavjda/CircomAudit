# CircomAudit MVP — one-page specification

Five Lean files (`lake build CircomAuditMVP`) plus this page. They answer three
questions: *what does the checker prove*, *what artifacts and languages are in
scope*, and *how does this compare to existing work*.

Entry point: `CircomAuditMVP.lean`. Files: `CircomAuditMVP/Semantics.lean`,
`Check.lean`, `Examples.lean`, `Propagate.lean`, `Scale.lean`. A review of this
document against the code, and the answers to give to each of the three
questions, is in `REVIEW.md`.

---

## 1. What the checker proves, and how circuit semantics are formalized

**The object.** A Circom circuit compiles to a rank-1 constraint system over the
scalar field `F = ZMod p`. With `n` signals, a *witness* is `w : Fin n → F`, and
each constraint is `A(w) * B(w) + C(w) = 0` with `A, B, C` affine in the signals
(`Lin`, `Constraint`, `System` in `Semantics.lean`). `Sol S = {w | S.sat w}` is
the set of witnesses a verifier accepts — exactly the R1CS relation that a
Groth16/Plonk verifier is checking, before any cryptography.

**The inputs.** A list of signal indices `inp : Fin k → Fin n` designates the
circuit's inputs; `proj inp w = w ∘ inp` (written `π`) reads them off a witness.

**The three properties** (verbatim from `Semantics.lean`):

```lean
def Deterministic (S : System n F) (inp : Fin k → Fin n) : Prop :=
  ∀ w w' : Fin n → F, S.sat w → S.sat w' → proj inp w = proj inp w' → w = w'

def Complete (S : System n F) (inp : Fin k → Fin n) : Prop :=
  ∀ x : Fin k → F, ∃ w, S.sat w ∧ proj inp w = x

def CorrectWrt (S : System n F) (inp : Fin k → Fin n)
    (R : (Fin k → F) → (Fin n → F) → Prop) : Prop :=
  ∀ w : Fin n → F, S.sat w → R (proj inp w) w
```

`Deterministic` is `π` injective on `Sol S` (`deterministic_iff_injOn`);
`Complete` is `π` surjective (`complete_iff_surjOn`). **Under-constrained =
`¬ Deterministic`.** `CorrectWrt` is the functional-spec layer: the only place a
human-written specification `R` enters.

**The headline theorem.** Let `gen : (Fin k → F) → (Fin n → F)` model the
witness generator Circom emits (`.wasm`/C++ witness calculator), assumed sound
(`GenSound`: `S.sat (gen x)`) and faithful on inputs (`GenFaithful`:
`π (gen x) = x`). Then

```lean
theorem deterministic_iff_sol_eq_range_gen (hs : GenSound S gen) (hf : GenFaithful inp gen) :
    Deterministic S inp ↔ Sol S = Set.range gen

theorem not_deterministic_iff_exists_extra_witness (hs : GenSound S gen) (hf : GenFaithful inp gen) :
    ¬ Deterministic S inp ↔ ∃ w, S.sat w ∧ w ∉ Set.range gen
```

In words: **under-constrainedness is exactly the gap between the constraint
system (what the verifier checks) and the witness generator (what the honest
prover does).** A solution outside `Set.range gen` is a proof the verifier
accepts and the honest prover would never produce — the shape of every
under-constrained exploit.

**The deployed form.** `Constraint.ofStandard a b c` is the `.r1cs` / snarkjs
form, and `Constraint.ofStandard_sat_iff` proves that satisfying it is literally
`A(w) * B(w) = C(w)`: the `A * B + C = 0` normal form used here *is* the
artifact format, up to a proved change of sign.

**Weaker determinism, for circuits with advice signals.** `DeterministicOn S inp
out` asks only that the listed output signals are pinned down by the inputs;
`deterministicOn_of_deterministic` proves the property checked here implies it,
and `deterministic_of_deterministicOn_id` proves the two coincide when every
signal is listed.

**The exact checker** (`Check.lean`). Over `ZMod p` every property above is
decidable:

```lean
def checkDeterministic (S : System n (ZMod p)) (inp : Fin k → Fin n) : Bool :=
  decide (Deterministic S inp)

theorem checkDeterministic_eq_true_iff (S) (inp) :
    checkDeterministic S inp = true ↔ Deterministic S inp
```

The `iff` is the point: the checker is **sound** (`true` ⇒ safe) *and*
**complete** (`false` ⇒ genuinely under-constrained; no false alarms), and when
it says `false`, `exists_collision_of_check_false` yields two distinct accepted
witnesses with identical inputs — the counterexample an auditor reports.
Everything is checked by the Lean kernel; `native_decide` is not used.

**Worked examples** (`Examples.lean`), the two-line version of the classic bug:

| Circom source | result |
| --- | --- |
| `out <== x * y;` | `mul_deterministic` (safe, over *any* commutative ring), `mul_complete`, `mul_correct`, and `mul_check_true` by kernel computation over `ZMod 5` |
| `out <-- x * y;` (assignment only) | `mulBug_not_deterministic`, `mulBug_check_false`, and `mulBug_extra_witness_outside_generator`: `(x,y,out) = (0,0,1)` is accepted, so a prover can claim `0 * 0 = 1` |

## 2. Trust assumptions (the TCB, in full)

A statement proved here is only as good as this list.

1. **Lean 4 kernel + Mathlib.** All results are kernel-checked; axioms used are
   `propext`, `Classical.choice`, `Quot.sound` only. No `native_decide`, no
   added `axiom`, no `sorry` in this MVP.
2. **The parser / ingestion step is outside Lean.** In this MVP the constraint
   system is written down by hand as a Lean term. Turning a `.r1cs` file into
   that term is *not* verified here; a Lean-verified `.r1cs` reader is the
   obvious next milestone. (The larger `CircomAudit/` library narrows this gap
   with pinned, hash-checked artifacts and a proved front-end translation.)
3. **The Circom compiler is trusted.** We reason about the constraint system it
   emitted, not about compilation from Circom source.
4. **The witness generator is modelled, not verified.** `GenSound`/`GenFaithful`
   are hypotheses about the emitted witness calculator, not proofs about it.
5. **`p` is the intended prime.** Field arithmetic is `ZMod p`; primality (and
   that `p` is the curve's scalar field) is an assumption of the caller.
6. **`R` is human-written.** `CorrectWrt R` proves conformance to `R`; whether
   `R` says what the protocol wanted is a human judgement.
7. **Nothing is claimed at the proof-system level.** No statement about
   Groth16/Plonk, trusted setup, Fiat–Shamir, or implementation side channels.
8. **Scale.** The decidable checker is exhaustive over `(ZMod p)^n`: it is a
   reference semantics and ground-truth oracle for tiny circuits, not a
   production analyser (see §3). It is `decide (Deterministic S inp)`, so its
   correctness theorem is decidability made explicit rather than the
   verification of an algorithm; the algorithmic content lives in
   `checkPropagate` below.

### 2b. The scalable, one-sided checker (`Propagate.lean`)

`checkPropagate` grows a set of signals known to be determined by the inputs: a
constraint `A * B + C = 0` *resolves* a signal `j` when `A` and `B` mention only
already-determined signals and `C` mentions only determined signals besides `j`,
with a nonzero coefficient on `j` — whereupon `w j` is forced. Iterate; if every
signal is determined, the system is not under-constrained:

```lean
theorem deterministic_of_checkPropagate (h : checkPropagate S inp = true) :
    Deterministic S inp
```

It is polynomial (one pass per signal), needs only that `F` is a field — so it
applies over BN254, not just over toy moduli — and is **sound but deliberately
not complete**: `false` means "not certified", never "buggy". `Scale.lean` proves
a twelve-signal chain circuit deterministic this way (`chain_deterministic`),
whose `5^12` witness space puts it far beyond the exhaustive checker.

## 3. Artifact formats, circuit languages, and scope tiers

| Tier | Status in this MVP |
| --- | --- |
| **R1CS over a prime field** — the compiled form of Circom 2.x (`.r1cs` binary, snarkjs JSON export), BN254 and any other `ZMod p` | Targeted. This is what `System n (ZMod p)` *is*. |
| **Circom source semantics** — `<==` (assign + constrain) vs `<--` (assign only) vs `===` | Modelled at the level that matters for soundness: `<--` contributes no constraint, which is precisely the bug in `Examples.lean`. |
| **Other constraint algebras** — gate/AIR/Plonkish, custom gates | *Not* in the MVP, but the property layer (`Deterministic`, `Complete`, `CorrectWrt`, and the generator-gap theorem) is stated in terms of `Sol` and `π` only, so it instantiates at any relation `Sol ⊆ (I → F) × States`; only `Constraint.sat` changes. |
| **Other languages** — Noir, Cairo, halo2, gnark, zkVMs | Out of scope. |
| **Proof-system / cryptographic properties** | Out of scope: this is about the constraint system, not the SNARK. |

The deliberate design choice is that the *deployed artifact format* (R1CS), not a
bespoke DSL, is the object of proof — so results transfer to what is actually
deployed on-chain, and so the same statements can be reused by other tools.

## 4. How this compares to existing work

| | object of proof | under-constrained detection | functional spec | trust base | scale |
| --- | --- | --- | --- | --- | --- |
| **Picus / Ecne** | compiled R1CS | automated, the main goal; uniqueness via SMT / propagation | no | SMT solver + tool implementation | large real circuits |
| **circomspect** | Circom source | heuristic lints, no proof | no | linter implementation | large, fast |
| **Coda** (Coq) | circuits in its own embedded language | via refinement types / proofs | yes | Coq kernel + the embedding matches Circom | medium, needs manual proof |
| **Published Circom / Poseidon formalisations** (Lean, Coq) | usually a hand-written model of the circuit | usually not the focus | yes — functional correctness | proof-assistant kernel + model fidelity | per-circuit, manual |
| **This MVP** | the compiled R1CS relation itself | yes — *defined*, decided by a sound **and complete** kernel-checked procedure, plus a proved-sound polynomial propagation pass | yes (`CorrectWrt`) | Lean kernel + the ingestion step listed in §2 | exhaustive checker: tiny circuits; propagation checker: polynomial, any field |

Honest reading: Picus is far more scalable, and Coda is a far more mature
framework. What this MVP contributes is different and complementary — a *tiny,
auditable reference semantics* in which "under-constrained" has a one-line
definition, a checker whose correctness is an `iff` rather than one-sided, a
machine-checked soundness proof for the propagation technique that fast tools
implement, a theorem tying under-constrainedness to the
constraint/witness-generator gap, and a written-down trust boundary. That makes it usable as (i) ground truth for
testing scalable tools such as Picus, (ii) a specification other Lean/Coq work
can share, and (iii) a teaching artifact a newcomer can read end to end.

## 5. Why this is public-goods work

Circuit soundness bugs are unmonetisable to fix and catastrophic to miss: every
rollup and bridge depends on circuits nobody individually owns. This MVP is
verification tooling plus a reusable specification for a deployed artifact
format, with the trust boundary stated rather than implied — audit and
bug-finding infrastructure, not a general category-theoretic formalisation.
