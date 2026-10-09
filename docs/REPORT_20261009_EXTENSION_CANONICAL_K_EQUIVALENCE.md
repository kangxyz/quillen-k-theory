# Canonical extension-category K-equivalence

Import `Quillen.Waldhausen.ExtensionCategory.KEquivalence`.
For `C : Type u`, `[Category.{u} C]`, and an arbitrary genuine Waldhausen
structure `W`, the checked endpoint is

```lean
ExtensionCategory.KEquiv W n :
  (ExtensionCategory.waldhausenStructure W).K n ≃*
    (ExtensionCategory.productStructure W W).K n
```

Its forward homomorphism is definitionally the original public
`Waldhausen.KMap (ExtensionCategory.sourceCofiber_exact W) n`.
`KEquiv_symm_toMonoidHom` proves that its inverse is exactly `splitKMap W n`,
the original canonical K-map of the actual literal split-extension functor.
The coproduct instances required by that functor are derived from the
Waldhausen axioms.

The generic supporting module `Functoriality.KEquivalence` proves that an
exact functor whose original realization map is the forward map of a genuine
homotopy equivalence induces a bijective original canonical K-map. It uses
the actual natural-isomorphism homotopy from the canonical zero rebasing to
the original functor, and replaces the equivalence's forward map by that
homotopic based map. The proved homotopy-fiber/group theorem then yields
bijectivity, including degree zero. No based inverse is assumed.

The concrete extension theorem instantiates this with the previously proved
actual extension realization equivalence. The inverse K-map formula follows
from original K-map composition, the actual split-source/cofiber natural
isomorphism, and injectivity of the forward equivalence.

## Validation

Both new implementation modules compiled warning-free and are frozen in
`logs/waldhausen-extension-kequivalence-sources.sha256`.
`audits/WaldhausenExtensionKEquivalenceAudit.lean` checks every defining-module
origin recursively, with fixed count **15**. Only `propext`, `Classical.choice`,
and `Quot.sound` occur as axioms. Exact forward/inverse and explicit degree-zero
consumers passed warning-free. Evidence:

- `logs/waldhausen-extension-kequivalence-audit.log`
- `logs/waldhausen-extension-kequivalence-hashes.log`

The common-universe restriction is explicit. The target is the actual
Waldhausen product-category K-theory. This theorem does not assume or assert
an unrestricted geometric-realization product homeomorphism, nor does it yet
identify this target with the product of the two K-groups. That actual
projection-compatible product-K comparison is the next separate obligation.
