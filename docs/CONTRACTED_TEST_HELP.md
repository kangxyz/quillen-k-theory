# Strict HELP on compact contracted tests

## Proved contract

`Quillen/Topology/HELP/ContractibleTest.lean` proves
`strictHELP_on_contracted_test` for an original map `f : E → F` over `B`,
where the original projections `p : E → B` and `q : F → B` have genuine
homotopy lifting. Given:

- a compact HEP pair `i : A ⟶ D`;
- an actual point `d₀ : D` and a displayed homotopy `id_D ~ const d₀`;
- actual maps `α : A → E`, `β : D → F` with `f ∘ α = β ∘ i`;
- compact HELP for the original strict-fiber map over `q(β(d₀))`;

there is an actual `c : D → E` extending `α` exactly, and an actual homotopy
`f ∘ c ~ β` relative to the whole image of `i`.

The first theorem needs only that one actual fiber. The wrapper
`strictHELP_on_contracted_test_of_all_fibers` uses the customary assumption
that every strict-fiber map has compact HELP. The endpoint
`strictHELP_on_contracted_test_boundary` spells out the complete constant
boundary track literally: `K(t,i(x)) = f(α(x))` for every time and boundary
point. The audit also verifies the equal target form `K(t,i(x)) = β(i(x))`.
No fixed-point condition on the displayed contraction is required.

All spaces use the original common universe of the HLP and compact HELP
APIs. There is no Hausdorff, embedding, or finite-CW hypothesis on the test
pair. Empty boundaries are permitted and explicitly checked. A chosen
contraction point is part of the contract, so the contracted target itself
is nonempty.

## Actual constructions

`HELP/StrictPullback.lean` constructs the literal strict-pullback map
`(d,e) ↦ (d,f(e))`, retaining the parameter. It proves that the actual
`strictPullbackFiberHomeomorph` squares commute exactly. Compact HELP on the
original strict fiber transfers through the genuine homeomorphisms by the
proved composition and second-map cancellation. This transport lemma itself
does not need either fibration hypothesis.

For a strict test square, set `r = q ∘ β` and pull both fibrations back along
`r`. Genuine HLP is preserved by the existing actual base-change theorem.
The displayed contraction of `D`, the identified fiber map at `d₀`, and
`ContractibleBaseHELP` give compact HELP for the literal pulled-back map.
The boundary lift is exactly `(i(a),α(a))`; the target is exactly `(d,β(d))`.
Their square commutes strictly. Apply strict compact HELP and project the
resulting lift and relative homotopy back to `E` and `F`.

The projected lift is not claimed to lie over the original base map at
every interior point. No such condition is needed for the asserted strict
HELP square. The boundary remains exact for the entire homotopy. This is
a contracted-test lifting theorem, not full compact HELP of `f` on arbitrary
tests and not a global or finite-cover gluing theorem.

## Verification

Both sources compile warning-free and are frozen in
`logs/contracted-test-20261009/sources.sha256`, fingerprint
`0cab80b429df3bf87cfa543a81ad178974886fadb8e86b516a25d0034be16430`.
The all-origin recursive audit passed the final fixed-11 guard, permitting
only `propext`, `Classical.choice` and `Quot.sound`, with ten exact consumers
in `audits/ContractedTestAudit.lean`. The terminal run completed warning-free
at 09:46:32 UTC; source hashes were rechecked unchanged.
The consumers include the combined public
`Quillen.Library` import, literal pullback/source maps, exact fiber square,
one-fiber and all-fiber strict lifting, both full constant-boundary formulas,
and a genuine empty-boundary test.

Evidence: `logs/contracted-test-20261009/`.
Scripts: `logs/check-contracted-test.sh`, `logs/audit-contracted-test.sh`.
The parent's two contraction prerequisites are reviewed separately in an
isolated overlay. Independent review of this authored boundary is complete:
`docs/REVIEW_20261009_CONTRACTED_TEST_HELP.md` records a fresh two-source
rebuild, fixed-11 recursive audit and all ten consumers passing warning-free.
Shared slot1 and single-threaded Lean are used for the authored checks.
