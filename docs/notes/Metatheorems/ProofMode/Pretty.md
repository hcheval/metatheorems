# ProofMode/Pretty.lean

## module header

### Named variables without a name environment

The usual way to print de Bruijn syntax with names is to thread a name stack through the
printer. That is awkward here, because delaborators are dispatched per-constant by Lean and
there is no natural place to keep the stack.

It is also unnecessary. The syntax is *intrinsically typed*: a variable's expression carries
its context, `Var Γ τ`, so the printer can read the context off the term itself. Naming a
variable by its **distance from the end of the context** rather than by its de Bruijn index
then gives names that do not shift when you go under a binder — which is the entire problem
with printing indices.

Concretely, in `ρ₂ :: ρ₁ :: ρ₀ :: Γ` the innermost variable (index 0) prints as `x₂`, and
under one more binder it still prints as `x₂` while the new one becomes `x₃`. Variables
reaching into an abstract tail `Γ` print as `y₀, y₁, …`, indexed from the top of the tail,
which is stable for the same reason.

### Open formulas print applied

A Lean variable `P : Formula F (ρ :: Γ)` is an object-level formula with a free object
variable — a predicate. Printing it as bare `P` hides that, and makes `∀ᶠ x₀ : ρ, P` look as
though the binder were vacuous. It prints as `P x₀`, and `P.subst0 t` prints as `P t`, so a
substitution reads as the application it is.

### Weakening

Weakening an *atom* is invisible: an atom binds nothing, so all its variables are shared with
the ambient context and already carry the ambient names. Weakening a structured formula is
marked `↑ᶜ`, because its own binders are fresh and must be kept clear of the ambient names —
see the two counters below.

These are *generated* names. Names the user chose — `pforall n` — would be better, and would
mean threading a second name list through `SeqD` beside the hypothesis names. That is a
separate change; this one costs no API.

## the `⬝` notation

The precedences must stay *below* `max`
and must differ between the two operands. Written as `syntax:max term:max ⬝ term:max` the
production is itself `max`, so a nested application needs no
parentheses in *either* operand and `(f ⬝ a) ⬝ b` and `f ⬝ (a ⬝ b)` print identically. That
defeats the copy-from-goal purpose above, and it made `#check` output on `RealNumbers.lean`
unreadable.
