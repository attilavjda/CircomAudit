import CircomAuditMVP.Semantics

/-!
# CircomAudit MVP — a scalable, one-sided checker by constraint propagation

`CircomAuditMVP.Check` decides `Deterministic` exactly, by exhausting
`(ZMod p)^n`.  That is a ground-truth oracle, but it is exponential and it is
useless on a real scalar field such as BN254.

This file provides the complementary checker an analyser would actually run: a
**syntactic propagation** pass that is linear in the size of the constraint
system, independent of the field size, and **sound but not complete** — it may
answer "don't know" (`false`) on a circuit that is in fact deterministic, but
when it answers `true` that answer is a proof of `Deterministic`.

The idea is the standard one used by R1CS analysers (Ecne, and the propagation
front-end of Picus), here with a machine-checked soundness proof:

* keep a set `D` of signals already known to be determined by the inputs;
* a constraint `A * B + C = 0` *resolves* a signal `j` when `A` and `B` involve
  only signals of `D`, and `C` involves only signals of `D` besides `j`, with a
  nonzero coefficient on `j`.  Then `w j = -(A(w) * B(w) + C_{≠j}(w)) / C_j`, so
  `j` is determined too;
* iterate to a fixpoint; if every signal ends up in `D`, the system is not
  under-constrained.

The soundness theorem is `deterministic_of_checkPropagate`.  Nothing here is
exponential, and nothing here needs the field to be small — only that it *is* a
field (a nonzero coefficient is invertible).
-/

namespace CircomAuditMVP

variable {n k : ℕ} {F : Type*} [Field F]

/-! ## Determined sets -/

/-- Two witnesses agree on a set of signals. -/
def AgreeOn (D : Finset (Fin n)) (w w' : Fin n → F) : Prop := ∀ j ∈ D, w j = w' j

/-- `D` is a *determined set* for `S` and `inp`: any two accepted witnesses with
the same inputs agree on all of `D`.  `Deterministic` is the case `D = univ`. -/
def Determines (S : System n F) (inp : Fin k → Fin n) (D : Finset (Fin n)) : Prop :=
  ∀ w w' : Fin n → F, S.sat w → S.sat w' → proj inp w = proj inp w' → AgreeOn D w w'

/-- The input signals are determined, trivially: that is what `π w = π w'` says. -/
lemma determines_inputs (S : System n F) (inp : Fin k → Fin n) :
    Determines S inp (Finset.image inp Finset.univ) := by
  intro w w' _ _ hp j hj
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hj
  exact congrFun hp t

/-- Determinacy of *every* signal is exactly `Deterministic`. -/
lemma deterministic_of_determines_univ (S : System n F) (inp : Fin k → Fin n)
    (h : Determines S inp Finset.univ) : Deterministic S inp := by
  intro w w' hw hw' hp
  funext j
  exact h w w' hw hw' hp j (Finset.mem_univ j)

/-- Determined sets only get better as they grow: a subset of a determined set is
determined. -/
lemma Determines.mono {S : System n F} {inp : Fin k → Fin n} {D D' : Finset (Fin n)}
    (h : Determines S inp D) (hsub : D' ⊆ D) : Determines S inp D' :=
  fun w w' hw hw' hp j hj => h w w' hw hw' hp j (hsub hj)

/-! ## Evaluating affine forms on agreeing witnesses -/

/-- An affine form supported on `D` takes the same value on witnesses agreeing
on `D`. -/
lemma Lin.eval_congr_of_support {D : Finset (Fin n)} {l : Lin n F} {w w' : Fin n → F}
    (hsup : ∀ i, i ∉ D → l.coeff i = 0) (hag : AgreeOn D w w') : l.eval w = l.eval w' := by
  simp only [Lin.eval]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : i ∈ D
  · rw [hag i hi]
  · rw [hsup i hi]; ring

/-- An affine form supported on `D ∪ {j}` takes the same value on witnesses
agreeing on `D`, once the `j`-term is removed. -/
lemma Lin.eval_sub_congr_of_support {D : Finset (Fin n)} {l : Lin n F} {j : Fin n}
    {w w' : Fin n → F} (hsup : ∀ i, i ∉ D → i ≠ j → l.coeff i = 0) (hag : AgreeOn D w w') :
    l.eval w - l.coeff j * w j = l.eval w' - l.coeff j * w' j := by
  have hsplit : ∀ v : Fin n → F,
      l.eval v - l.coeff j * v j = l.const + ∑ i ∈ Finset.univ.erase j, l.coeff i * v i := by
    intro v
    have : ∑ i, l.coeff i * v i
        = l.coeff j * v j + ∑ i ∈ Finset.univ.erase j, l.coeff i * v i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    simp only [Lin.eval, this]
    ring
  rw [hsplit, hsplit]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  by_cases hiD : i ∈ D
  · rw [hag i hiD]
  · rw [hsup i hiD hij]; ring

/-! ## The propagation step -/

/-- The syntactic side condition: constraint `con` *resolves* signal `j` relative
to the determined set `D`. -/
def Resolves (con : Constraint n F) (D : Finset (Fin n)) (j : Fin n) : Prop :=
  (∀ i, i ∉ D → con.a.coeff i = 0) ∧ (∀ i, i ∉ D → con.b.coeff i = 0) ∧
    (∀ i, i ∉ D → i ≠ j → con.c.coeff i = 0) ∧ con.c.coeff j ≠ 0

instance [DecidableEq F] (con : Constraint n F) (D : Finset (Fin n)) (j : Fin n) :
    Decidable (Resolves con D j) := by unfold Resolves; infer_instance

/-- **The propagation lemma.**  If a constraint of the system resolves `j`
relative to a determined set `D`, then `j` is determined too. -/
lemma agree_of_resolves {con : Constraint n F} {D : Finset (Fin n)} {j : Fin n}
    {w w' : Fin n → F} (hres : Resolves con D j) (hw : con.sat w) (hw' : con.sat w')
    (hag : AgreeOn D w w') : w j = w' j := by
  obtain ⟨ha, hb, hc, hj⟩ := hres
  have hA : con.a.eval w = con.a.eval w' := Lin.eval_congr_of_support ha hag
  have hB : con.b.eval w = con.b.eval w' := Lin.eval_congr_of_support hb hag
  have hC : con.c.eval w - con.c.coeff j * w j = con.c.eval w' - con.c.coeff j * w' j :=
    Lin.eval_sub_congr_of_support hc hag
  have hsat : con.a.eval w * con.b.eval w + con.c.eval w = 0 := hw
  have hsat' : con.a.eval w' * con.b.eval w' + con.c.eval w' = 0 := hw'
  have hcoeff : con.c.coeff j * (w j - w' j) = 0 := by
    have : con.c.eval w = con.c.eval w' := by
      rw [hA, hB] at hsat
      linear_combination hsat - hsat'
    linear_combination this - hC
  rcases mul_eq_zero.mp hcoeff with h | h
  · exact absurd h hj
  · exact sub_eq_zero.mp h

/-- All signals a single constraint resolves relative to `D`. -/
def resolvedBy [DecidableEq F] (con : Constraint n F) (D : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Resolves con D j)

/-- One constraint's contribution to the determined set. -/
def stepCon [DecidableEq F] (con : Constraint n F) (D : Finset (Fin n)) : Finset (Fin n) :=
  D ∪ resolvedBy con D

/-- One left-to-right pass over the whole system. -/
def stepSystem [DecidableEq F] (S : System n F) (D : Finset (Fin n)) : Finset (Fin n) :=
  S.foldl (fun D con => stepCon con D) D

/-- `fuel` passes over the system. -/
def propagate [DecidableEq F] (S : System n F) (D : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => D
  | fuel + 1 => propagate S (stepSystem S D) fuel

section Sound

variable [DecidableEq F] {S : System n F} {inp : Fin k → Fin n}

lemma determines_stepCon {con : Constraint n F} {D : Finset (Fin n)} (hmem : con ∈ S)
    (hD : Determines S inp D) : Determines S inp (stepCon con D) := by
  intro w w' hw hw' hp j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · exact hD w w' hw hw' hp j hj
  · have hres : Resolves con D j := (Finset.mem_filter.mp hj).2
    exact agree_of_resolves hres (hw con hmem) (hw' con hmem) (hD w w' hw hw' hp)

lemma determines_foldl (T : System n F) (hT : ∀ con ∈ T, con ∈ S) :
    ∀ D : Finset (Fin n), Determines S inp D →
      Determines S inp (T.foldl (fun D con => stepCon con D) D) := by
  induction T with
  | nil => intro D hD; exact hD
  | cons con T ih =>
      intro D hD
      exact ih (fun c hc => hT c (List.mem_cons_of_mem _ hc)) _
        (determines_stepCon (hT con List.mem_cons_self) hD)

lemma determines_stepSystem {D : Finset (Fin n)} (hD : Determines S inp D) :
    Determines S inp (stepSystem S D) :=
  determines_foldl S (fun _ hc => hc) D hD

lemma determines_propagate : ∀ (fuel : ℕ) {D : Finset (Fin n)}, Determines S inp D →
    Determines S inp (propagate S D fuel)
  | 0, _, hD => hD
  | fuel + 1, _, hD => determines_propagate fuel (determines_stepSystem hD)

/-- **The scalable checker.**  `true` means "propagation proved that the inputs
determine every signal".  `false` means "propagation could not prove it" — which
is *not* a claim that the circuit is under-constrained. -/
def checkPropagate (S : System n F) (inp : Fin k → Fin n) : Bool :=
  decide (propagate S (Finset.image inp Finset.univ) n = Finset.univ)

/-- **Soundness of the propagation checker.**  A `true` answer is a proof that
the system is not under-constrained.  Unlike `checkDeterministic`, this holds
over an arbitrary field — in particular over BN254 — and costs one pass per
signal, not an exhaustive search. -/
theorem deterministic_of_checkPropagate (h : checkPropagate S inp = true) :
    Deterministic S inp := by
  apply deterministic_of_determines_univ
  have hEq : propagate S (Finset.image inp Finset.univ) n = Finset.univ := of_decide_eq_true h
  exact hEq ▸ determines_propagate n (determines_inputs S inp)

end Sound

/-! ## Relating the two checkers

The propagation checker is a one-sided approximation of the exact one: whenever
it says `true`, the exhaustive checker of `CircomAuditMVP.Check` would also say
`true`.  The converse fails (propagation is incomplete), which is the price of
being polynomial. -/

lemma determines_of_deterministic (S : System n F) (inp : Fin k → Fin n)
    (h : Deterministic S inp) (D : Finset (Fin n)) : Determines S inp D :=
  fun w w' hw hw' hp j _ => congrFun (h w w' hw hw' hp) j

end CircomAuditMVP
