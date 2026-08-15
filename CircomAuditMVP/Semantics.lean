import Mathlib

/-!
# CircomAudit MVP — R1CS semantics and the three audit properties

This is the **minimal** core of the CircomAudit development: a single, small file
that says what a rank-1 constraint system *is*, what it means for a witness to
satisfy it, and what the three properties an auditor cares about are.

Everything here is elementary on purpose.  A newcomer should be able to read the
whole file in one sitting; every later, larger module in this repository is an
elaboration of exactly these definitions.

## The object of study

A Circom circuit compiles to a **rank-1 constraint system** (R1CS) over the
scalar field `F = ZMod p`.  The circuit has `n` *signals*; an assignment of
values to all of them is a **witness** `w : Fin n → F`.  Each compiled
constraint has the rank-1 shape

  `A(w) * B(w) + C(w) = 0`

where `A`, `B`, `C` are affine (degree ≤ 1) combinations of the signals.  A
system is a list of such constraints, and `Sol S` is its set of satisfying
witnesses.

## The three properties

Some of the signals are the circuit's *inputs*; `proj inp w` reads them off a
witness.  Writing `π = proj inp`:

* `Deterministic` — `π` is injective on `Sol S`: the inputs pin down the whole
  witness.  Its failure is precisely an **under-constrained** circuit, the
  classic soundness bug in ZK circuits.
* `Complete`      — `π` is surjective onto all input vectors: every input is
  accepted by some witness (no accidental exclusion).
* `CorrectWrt R`  — every solution satisfies the auditor's functional
  specification `R` relating inputs to the whole witness.

## The headline theorem

`deterministic_iff_sol_eq_range_gen`: given a witness generator `gen` (the
`.wasm`/C++ witness calculator that Circom emits) which is sound (`gen x`
satisfies the system) and faithful on inputs (`π (gen x) = x`),

  `Deterministic S inp ↔ Sol S = Set.range gen`.

That is: **under-constrainedness is exactly the gap between the constraint
system and the witness generator.**  A prover who follows `gen` produces a
member of `Set.range gen`; the verifier only checks membership in `Sol S`.  Any
solution outside the range of `gen` is a witness the verifier accepts but the
honest prover would never produce — an exploit.
-/

namespace CircomAuditMVP

variable {n k : ℕ} {F : Type*} [CommRing F]

/-! ## Syntax -/

/-- An affine combination of the `n` signals: a constant plus one coefficient
per signal.  Circom's linear expression `2*x + 3*y + 2` over two signals is
`⟨2, ![2, 3]⟩`. -/
structure Lin (n : ℕ) (F : Type*) where
  /-- The constant term. -/
  const : F
  /-- The coefficient of each signal. -/
  coeff : Fin n → F

/-- One rank-1 constraint `A * B + C = 0`. -/
structure Constraint (n : ℕ) (F : Type*) where
  /-- The left factor `A`. -/
  a : Lin n F
  /-- The right factor `B`. -/
  b : Lin n F
  /-- The additive part `C`. -/
  c : Lin n F

/-- A constraint system: the list of constraints the compiler emits. -/
abbrev System (n : ℕ) (F : Type*) := List (Constraint n F)

/-! ## Semantics -/

namespace Lin

/-- Value of an affine combination at a witness. -/
def eval (l : Lin n F) (w : Fin n → F) : F := l.const + ∑ i, l.coeff i * w i

@[simp] lemma eval_def (l : Lin n F) (w : Fin n → F) :
    l.eval w = l.const + ∑ i, l.coeff i * w i := rfl

/-- The affine combination reading a single signal. -/
def var (j : Fin n) : Lin n F := ⟨0, fun i => if i = j then 1 else 0⟩

@[simp] lemma eval_var (j : Fin n) (w : Fin n → F) : (var j : Lin n F).eval w = w j := by
  simp [var, eval]

/-- Negation of an affine combination. -/
def neg (l : Lin n F) : Lin n F := ⟨-l.const, fun i => -l.coeff i⟩

@[simp] lemma eval_neg (l : Lin n F) (w : Fin n → F) : (l.neg).eval w = -(l.eval w) := by
  simp [neg, eval, Finset.sum_neg_distrib, add_comm]

end Lin

/-- A witness satisfies a constraint when `A(w) * B(w) + C(w) = 0`. -/
def Constraint.sat (con : Constraint n F) (w : Fin n → F) : Prop :=
  con.a.eval w * con.b.eval w + con.c.eval w = 0

/-- A witness satisfies a system when it satisfies every constraint. -/
def System.sat (S : System n F) (w : Fin n → F) : Prop := ∀ con ∈ S, con.sat w

/-- The constraint written in the standard R1CS form `A * B = C` used by the
`.r1cs` binary format and by snarkjs' JSON export.  It is the same object as
`Constraint`: only the sign of the third component differs. -/
def Constraint.ofStandard (a b c : Lin n F) : Constraint n F := ⟨a, b, c.neg⟩

/-- The two presentations agree: `Constraint.sat` on `ofStandard a b c` is
literally the `.r1cs` condition `A(w) * B(w) = C(w)`.  This is the bridge
between the deployed artifact format and the `A * B + C = 0` normal form used
throughout this development. -/
@[simp] lemma Constraint.ofStandard_sat_iff (a b c : Lin n F) (w : Fin n → F) :
    (Constraint.ofStandard a b c).sat w ↔ a.eval w * b.eval w = c.eval w := by
  show a.eval w * b.eval w + (Lin.neg c).eval w = 0 ↔ _
  rw [Lin.eval_neg, ← sub_eq_add_neg, sub_eq_zero]

/-- The solution set of a system: exactly the witnesses a verifier accepts. -/
def Sol (S : System n F) : Set (Fin n → F) := {w | S.sat w}

@[simp] lemma mem_Sol {S : System n F} {w : Fin n → F} : w ∈ Sol S ↔ S.sat w := Iff.rfl

/-! ## Inputs and the three audit properties -/

/-- The circuit's input signals, given as a list of `k` signal indices; `proj`
reads their values off a witness.  This is the map `π` of the documentation. -/
def proj (inp : Fin k → Fin n) (w : Fin n → F) : Fin k → F := fun j => w (inp j)

/-- **Deterministic** (= *not* under-constrained): the inputs determine the
entire witness.  Two accepted witnesses agreeing on the inputs are equal. -/
def Deterministic (S : System n F) (inp : Fin k → Fin n) : Prop :=
  ∀ w w' : Fin n → F, S.sat w → S.sat w' → proj inp w = proj inp w' → w = w'

/-- **Complete**: every input vector is accepted by at least one witness. -/
def Complete (S : System n F) (inp : Fin k → Fin n) : Prop :=
  ∀ x : Fin k → F, ∃ w, S.sat w ∧ proj inp w = x

/-- **Correct with respect to a specification** `R`: every accepted witness
relates its inputs to the rest of the witness the way the auditor says it
should.  `R` is the human-written part of the trust base. -/
def CorrectWrt (S : System n F) (inp : Fin k → Fin n)
    (R : (Fin k → F) → (Fin n → F) → Prop) : Prop :=
  ∀ w : Fin n → F, S.sat w → R (proj inp w) w

/-- **Deterministic on a chosen set of signals**: the inputs determine the
signals listed in `out`.  This is the property an auditor actually needs when a
circuit legitimately contains non-deterministic advice signals: soundness only
requires the *outputs* to be pinned down, not every intermediate wire.
`Deterministic` is the special case `out = id`. -/
def DeterministicOn {m : ℕ} (S : System n F) (inp : Fin k → Fin n) (out : Fin m → Fin n) : Prop :=
  ∀ w w' : Fin n → F, S.sat w → S.sat w' → proj inp w = proj inp w' → proj out w = proj out w'

/-- Full determinism implies determinism on any chosen output signals: the
strong property checked by this MVP is a safe over-approximation. -/
lemma deterministicOn_of_deterministic {m : ℕ} (S : System n F) (inp : Fin k → Fin n)
    (out : Fin m → Fin n) (h : Deterministic S inp) : DeterministicOn S inp out :=
  fun w w' hw hw' hp => by rw [h w w' hw hw' hp]

/-- Conversely, determinism on *all* signals is full determinism, so the two
notions really are the same property at the two ends of the spectrum. -/
lemma deterministic_of_deterministicOn_id (S : System n F) (inp : Fin k → Fin n)
    (h : DeterministicOn S inp (id : Fin n → Fin n)) : Deterministic S inp :=
  fun w w' hw hw' hp => h w w' hw hw' hp

/-- `Deterministic` is exactly injectivity of `π` on the solution set. -/
lemma deterministic_iff_injOn (S : System n F) (inp : Fin k → Fin n) :
    Deterministic S inp ↔ Set.InjOn (proj inp) (Sol S) :=
  ⟨fun h w hw w' hw' hp => h w w' hw hw' hp, fun h _ _ hw hw' hp => h hw hw' hp⟩

/-- `Complete` is exactly surjectivity of `π` from the solution set. -/
lemma complete_iff_surjOn (S : System n F) (inp : Fin k → Fin n) :
    Complete S inp ↔ Set.SurjOn (proj inp) (Sol S) Set.univ := by
  constructor
  · intro h x _
    obtain ⟨w, hw, hx⟩ := h x
    exact ⟨w, hw, hx⟩
  · intro h x
    obtain ⟨w, hw, hx⟩ := h (Set.mem_univ x)
    exact ⟨w, hw, hx⟩

/-! ## The headline: under-constrainedness is the constraints-vs-generator gap -/

section Generator

variable (S : System n F) (inp : Fin k → Fin n) (gen : (Fin k → F) → Fin n → F)

/-- A witness generator is *sound* when everything it produces is accepted. -/
def GenSound : Prop := ∀ x, S.sat (gen x)

/-- A witness generator is *faithful* when it puts its argument on the input
signals. -/
def GenFaithful : Prop := ∀ x, proj inp (gen x) = x

/-- **Main theorem.**  For a sound, faithful witness generator, the system is
deterministic (not under-constrained) if and only if the verifier's solution set
is exactly the set of witnesses the generator can produce. -/
theorem deterministic_iff_sol_eq_range_gen
    (hs : GenSound S gen) (hf : GenFaithful inp gen) :
    Deterministic S inp ↔ Sol S = Set.range gen := by
  constructor
  · intro hdet
    apply Set.eq_of_subset_of_subset
    · intro w hw
      refine ⟨proj inp w, hdet _ _ (hs _) hw ?_⟩
      rw [hf]
    · rintro _ ⟨x, rfl⟩
      exact hs x
  · intro hEq w w' hw hw' hp
    obtain ⟨x, rfl⟩ : w ∈ Set.range gen := hEq ▸ hw
    obtain ⟨x', rfl⟩ : w' ∈ Set.range gen := hEq ▸ hw'
    rw [hf, hf] at hp
    exact congrArg gen hp

/-- The contrapositive, in the form an auditor reports it: a circuit is
under-constrained exactly when some accepted witness is one the honest witness
generator would never produce. -/
theorem not_deterministic_iff_exists_extra_witness
    (hs : GenSound S gen) (hf : GenFaithful inp gen) :
    ¬ Deterministic S inp ↔ ∃ w, S.sat w ∧ w ∉ Set.range gen := by
  rw [deterministic_iff_sol_eq_range_gen S inp gen hs hf]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h (Set.eq_of_subset_of_subset (fun w hw => hcon w hw)
      (fun _ hx => by obtain ⟨x, rfl⟩ := hx; exact hs x))
  · rintro ⟨w, hw, hnot⟩ hEq
    exact hnot (hEq ▸ hw)

/-- A sound, faithful generator already witnesses completeness: the interesting
audit question is determinism, not completeness. -/
theorem complete_of_generator (hs : GenSound S gen) (hf : GenFaithful inp gen) :
    Complete S inp := fun x => ⟨gen x, hs x, hf x⟩

end Generator

end CircomAuditMVP
