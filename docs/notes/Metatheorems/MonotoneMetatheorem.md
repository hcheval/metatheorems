# MonotoneMetatheorem.lean

## module header

`metatheorem_core_of_majorants_at` is consumed unchanged. The existential realizer in
`MRealizer` is eliminated into the `Prop` conclusion, which is why the `∃`-valued and the
`_at` version collapse into one statement here: `cm` is an input, `Φ` is data, and nothing
`Prop`-shaped has to be turned into `Type`.

`general_metatheorem_extract` (`Metatheorem.lean`) is **not** reused. It builds `U`, `V` from
`dialectica_soundness_ctx'` — a *specific* realizer — whereas here the realizer is whatever the
monotone realizer's existential provides, and the majorization fact is about *that* realizer.
Reusing the semantic extraction half would mean proving that the two realizers coincide, which
is neither true nor needed. What is reused is its *shape*: `mfi_extract_core` below is
`general_metatheorem_extract` stated over an abstract realizer, plus the two majorization
facts.

**Statement over an abstract realizer first, then applied** (`mfi_bound_property` is about an
arbitrary `r : MRealizer cm _`, and `monotone_general_metatheorem_at` instantiates it). This
is the trap `extraction_of_prenex_realizer` paid for once: a `simp only [dialecticaMatrix]`
run against the *applied* recursion tries to reduce the realizer itself.

## `monotone_general_metatheorem_at`

No realizer term is built anywhere on the bound path (ARCHITECTURE.md §14.3).
