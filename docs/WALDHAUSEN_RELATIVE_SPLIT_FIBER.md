# The actual zero-tail split-fiber inclusion

Three sources are frozen in `logs/relative-rows-split-fiber-sources.sha256`:
`SConstruction/Rows/OneRow` and `Fibration/RelativeRows/{SplitFiber,SplitFiberZero}`.
All three compile without warnings. The own audit checks **35 declaration
origins** and **20 actual-map consumers**, with only the three standard axioms.
Both the full initial audit and the fixed35 rerun passed warning-free; final evidence is `logs/relative-rows-split-fiber-audit-final.log`. The independent review also accepted the three-source boundary, with24 strengthened consumers; see `docs/REVIEW_20261009_RELATIVE_SPLIT_FIBER.md`.

The genuine one-step row has the literal original three objects `0, X, 0`.
Its relative cofibration tests are proved using the genuine exact identity-
arrow and zero-arrow embeddings. Its pushouts are the actual component
pushouts. No global cocompleteness is assumed.

For relative degree n, the added vertex maps to0 and every tail vertex maps
to1. Pullback of the one-step row gives the genuinely exact `fiber N n`.
Its first quotient is the original object and its first map is the original
morphism. Every tail object is the actual chosen zero and every tail map is
its identity. The following are strict functor equalities:

- `fiber_first`: first evaluation is the identity functor.
- `fiber_tail`: the actual tail is the constant chosen-zero row functor.
- `fiber_reindex`: the original split inclusion commutes with every outer ordinal restriction.
- `fiber_firstTail`: the original first/tail triangle is exactly `(id, 0)`.

`fiber_zero` also retains the actual chosen relative zero row, including all
its component maps. The structural statements allow independent object/hom
universes. Applying the existing raw S-map and realization API still requires
an honest common realization universe; no cross-universe comparison is claimed.

This boundary supplies the strict split inclusion and constant-path coherence.
The genuine first/tail realization equivalence from relative additivity and
the global connected-row fiber theorem remain separate obligations.
