# Ordinary functor implementation candidates

These candidates preserve the existing declaration namespaces. PointwiseCoproduct supplies the
actual coproduct functor, injections, split endpoint and endpoint transformation. CoproductPostcompose
retains its canonical comparison under a coproduct-preserving functor. UnderlyingIso retains
the literal underlying functor of an object-property lift. FullSubcategoryExt retains the original
full-subcategory functor-inclusion extensionality and injectivity helpers.

Rebase replaces the specified object and conjugates actual functor maps through the supplied
isomorphism, with its original comparison and reflexive laws. IdentityAutomorphismRebase preserves
the same supplied automorphisms through this actual rebasing. The remaining identity-automorphism
leaves retain their original faithful/full evaluation and naturality hypotheses.
