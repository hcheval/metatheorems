# Probes/WHyperbolicLemmasDemo.lean

## module header

Nothing here consults `M.W1`–`M.W4` directly. The route is always

    object derivation  →  WHyperbolicModel.soundness  →  codeReal bridge  →  Mathlib ℝ

so a wrong object-level statement would surface here as a type error, and the model facts
enter only inside `WHyperbolicModel.axiomsHold`, which `soundness` already used.

**The parameter.** Every object statement is at `clamp01 λ` for a free code `λ`, and the
model interprets `W(x,y,r)` as `M.W x y (clampReal (codeReal r))`. So the model-side
parameter is `t := clampReal (codeReal r)`, an arbitrary element of `[0,1]` — and for
`W_zero`/`W_one` the code is the closed `0ℝ`/`1ℝ`, whose `codeReal` is `0`/`1` and whose
clamp is therefore the identity. That is the `[0,1]`-retraction doing its job: the object
theory quantifies over *all* codes, the model sees only `[0,1]`.
