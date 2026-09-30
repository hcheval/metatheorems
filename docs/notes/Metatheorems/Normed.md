# Normed.lean

## module header

### Why `−` is primitive — the majorant, and what it says about encodings

`smulMajorant f n = (f 0 + 1)·n`, so with `−x := (−1)·x` negation would be majorized by
`(negOne(0) + 1)·n`, where `negOne(0)` is **the ℚ-code for `−1` under the sign-magnitude
Cantor-pairing encoding of `Terms/Rational.lean`**. That factor is an artifact of the coding
with no mathematical content whatever, and it would appear verbatim in every extracted bound
that so much as subtracts. With `−` primitive the majorant is

    negMajorant = fun (n : ℕ) => n

**exactly**, because `‖−x‖ = ‖x‖` and base-majorization at `X` *is* `‖x‖ ≤ n`. The lesson
generalises past this file: **a defined operation inherits the majorant of its definiens, so
anything routed through the real/rational encoding pays an encoding-sized constant.** When the
mathematics has a tight majorant, make the operation a constant and axiomatise it.

### Checked against Kohlenbach's `A^ω[X,‖·‖]`

(Applied Proof Theory §17.3, pp. 411–412.)
His signature is `0_X, 1_X, +_X, −_X, ·_X, ‖·‖_X`, with `x =_X y :≡ ‖x −_X y‖ =ℝ 0`
and no `d_X`; his axioms are **(0)** "the purely universal vector space axioms formulated with
`=_X`" — exactly our (1)–(8) — followed by nine norm axioms in *difference* form, (1)–(3)
`‖x−x‖=0`, `‖x−y‖=‖y−x‖`, the triangle inequality, (4) `‖αx−αy‖=|α|‖x−y‖`,
(5) `‖αx−βx‖=|α−β|‖x‖`, (6) `‖(x+y)−(u+v)‖≤‖x−u‖+‖y−v‖`, (7) `‖(−x)−(−y)‖=‖x−y‖`,
(8) `|‖x‖−‖y‖|≤‖x−y‖`, (9) `‖1_X‖=1`. His (4)–(8) are the *extensionality of the operations
w.r.t. `=_X`* in purely universal form (he says so, p. 412); ours (9)–(10) are the "usual"
norm axioms he notes are derivable from them. The converse derivation — his (4)–(8) from our
list — goes through because every `=_X` fact it needs is a closed theorem, so `qfer` supplies
the congruences; it has been checked on paper, **not in Lean**. His (1)–(3) are our `Derivable`
pseudometric constructors carried across the link (13).

**Both former omissions are now closed.** The signature is his, modulo his `−_X`
being binary-sugar `x −_X y :≡ +_X(x, −_X y)`, which we spell out at the two use sites:

* **`1_X` and (9) are in.** `ax_norm_one : ‖1_X‖ =ℝ 1ℝ` — Kohlenbach's (9), "a Skolemized form
  of expressing that the normed space is nontrivial". A book statement mentioning `1_X` is now
  transcribable verbatim, and the model must be nontrivial.
* **`−_X` is a primitive constant.** *Which axiomatisation:* **Kohlenbach's.** He has `−_X` in
  the signature and axiomatises it *directly* — inside (0), the vector-space axioms, as
  `x +_X (−_X x) =_X 0_X`, plus the norm axiom (7) `‖(−x) − (−y)‖ = ‖x−y‖`. He does **not**
  relate `−` to `·_X` by an axiom `−x =_X (−1)·x`; in his theory, as in ordinary algebra, that
  is a *derived* identity. We follow him: our (4) is `x + (−x) =_X 0_X` at the primitive `−`,
  and our (12) `‖−x‖ =ℝ ‖x‖` is his (7) in the "usual" form, the same relation ours (9)/(10)
  bear to his (4)–(8).

  One honest consequence, since our (4) *replaces* the old `x + (−1)·x =_X 0_X` rather than
  joining it: the new theory is not literally a superset of the old one along that single
  formula. It is a consequence on paper (`(−1)x = −x` in any vector space) but the object-level
  derivation would need extensionality of `·_X` in its *scalar* argument w.r.t. `=ℝ`, which
  `qfer` does not supply (`qfer` is `=₀`). Both formulas are true in every normed model, so
  nothing about the *models* changed; only what is derivable from the axiom list, and only in
  that one direction. Adding `−x =_X (−1)·x` as a further axiom would close it, at the price
  of an axiom Kohlenbach does not have.

## `NormedModel`

Nontriviality is carried as an *instance field* rather than as an explicit unit vector plus
`‖·‖ = 1`, because that is what keeps `NormedModel` a pure bundling of Mathlib typeclasses:
`Instances.lean`'s `ofNormed` stays the identity `{ E := E }`, gaining only a `[Nontrivial E]`
binder, instead of having to construct and verify a witness at the instantiation site. The unit
vector is built once, here, by `NormedModel.unitVec`.

## `negMajorant`

Contrast `smulMajorant`: had `−x` stayed `(−1)·x`, this would be `λn. (negOne(0) + 1)·n`, whose
factor is a ℚ-encoding artifact.
Compare `WHyperbolicModel.WMajorant = λn₁ n₂ _. max n₁ n₂`.
