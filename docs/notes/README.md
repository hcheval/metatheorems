# Notes moved out of the code

The `.lean` sources of this project used to carry long prose comments: findings,
measurements, design reasons, traps, and rejected alternatives, written where the
declaration they concerned was defined.

That prose has been moved here. Each file under `docs/notes/` mirrors a module path —
`docs/notes/Metatheorems/ProofMode/Tactics.md` holds what used to live in
`Metatheorems/ProofMode/Tactics.lean` — and each section is headed by the declaration
it belonged to (or "module header").

Nothing was discarded except pure noise (banner comments, restatements of the code,
narration of a proof's obvious structure). The code keeps ordinary docstrings: what a
declaration is, and when to use it.

For the project-level picture see `CLAUDE.md` and `ARCHITECTURE.md`; these notes are the
local, declaration-level layer beneath them.
