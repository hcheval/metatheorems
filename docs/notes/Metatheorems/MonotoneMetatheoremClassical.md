# MonotoneMetatheoremClassical.lean

## module header

`monotone_general_metatheorem_classical_at` has the **same statement** as
`syntactic_general_metatheorem_classical_at` (`SyntacticMetatheorem.lean`) but computes the
bound through the monotone functional interpretation of the *classical* derivation, avoiding
`negTrans_sound`'s ×230 blow-up (`ARCHITECTURE.md` §14.5, `Probes/ClassicalMfiProbe.lean`
part C0):

1. `prenexify` under `∀x` — a closed classical derivation applied **once** (it uses LEM), so
   `monotone_nd_soundness` interprets it as an ordinary sub-derivation, not per-node;
2. `monotone_nd_soundness` (`Dialectica/MonotoneND.lean`) — the fused negative-translation +
   MFI recursion, giving a monotone realizer of `(∀ρ E)ᴺᵀ = ¬¬(∀ρ ¬¬E)`, `E := ∃u∃v(B₀'→C₀')`;
3. `nn_all_nn` at the `MRealizer` level (a leaf composition), giving a realizer of `∀ρ ¬¬E`;
4. the `¬¬∃u∃v` projection — the MFI analogue of `extractUTermP`/`extractVTermP`
   (`interpret_extractUTermP`): challenge the surviving `¬¬` with the default `¬E`-witness,
   read the `∃u`/`∃v` index off the resulting witness. Legitimate because `B₀'→C₀'` is QF and
   ∨-free, so `dialecticaMatrix_iff_interpFormula` reduces its matrix for **every** counter —
   the argument written for the term route (`extraction_of_prenex_realizer`), followed here on
   the semantic realizer;
5. `metatheorem_core_of_majorants_at`, unchanged.

`mfiU_cl`/`mfiV_cl` read the two majorants off the monotone realizer's `tstar`; the semantic
`U`/`V` are the same projection off its existential realizer, and the two are related by the
`MRealizer` majorization clause.

## `monotone_general_metatheorem_classical_at`

No `negTrans_sound`, no realizer term — the ×230 classical blow-up is not incurred at
elaboration (`ARCHITECTURE.md` §14.5).
