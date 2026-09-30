# Dialectica/MfiMemoAttr.lean

## module header

An attribute cannot be used in the module that declares it (see `SimpSets.lean`), and
`SimpSets.lean` sits below everything — touching it rebuilds the whole tree — so this one
lives in its own module.
