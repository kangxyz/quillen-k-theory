# Regular-local algebra: checked proof and remaining globalization

## Completed arbitrary-dimensional local theorem

The repository now proves
`Quillen.RegularLocal.hasProjectiveDimensionLE_of_regularLocal_dimension`:
a finite module over a ring satisfying mathlib's actual `IsRegularLocalRing`
class and having dimension `d` has projective dimension at most `d`.
`projectiveDimension_ne_top_of_regularLocal` removes the explicit numerical
bound. The ring's regularity implies it; finite projective dimension is not
an extra hypothesis.

The proof uses neither an assumed Auslander–Buchsbaum–Serre theorem nor an
unproved Koszul/Tor interface.

## Checked algebraic chain

1. `Algebra/RegularLocal/ParameterQuotient.lean` extends a nonzero cotangent
   vector to a basis and lifts it by Nakayama. This gives a generating family
   of the maximal ideal containing a specified `x` outside its square.
   Killing `x` reduces the generator bound by one. The Krull lower bound then
   proves that the quotient is regular local and its dimension drops by one.
   No domain hypothesis is used.
2. `ParameterAvoidance.lean` chooses such an `x` outside all minimal primes.
   The quotient is a domain by dimension induction, so `(x)` is prime. A
   minimal prime contained in `(x)` avoids `x`, hence equals `x` times itself;
   Nakayama forces that minimal prime to be zero. `Domain.lean` therefore
   proves that the original regular local ring is a domain.
3. `Parameters.lean` combines the first two steps into an actual regular
   parameter: `x` belongs to the maximal ideal, acts injectively on the ring,
   and has regular quotient of dimension one less.
4. `QuotientLifting.lean` supplies the homological induction. First take a
   finite free cover of an arbitrary finite module. Its kernel is regular
   with respect to `x`, because it embeds in a free module. Reduction modulo
   `x` preserves the relevant short exact sequences. Induction over `R/(x)`
   resolves that kernel modulo `x`; repeated finite free covers and the
   existing `Module.free_quotSMulTop_iff_free` lift the tower back to `R`.
   Appending the initial cover proves the claimed bound.
5. `ProjectiveDimension.lean` runs the actual dimension induction and produces
   finite admissible projective resolutions as well as the Ext-defined bound.

## Completed affine comparison with finite Krull dimension

`Scheme/Regular/AffineFiniteDimension.lean` applies the local bound at every
prime and uses mathlib's proved localization criterion for projective
dimension. It proves the all-degree canonical `Scheme.KToG` equivalence for
regular rings with a specified finite dimension bound, and also under the
usual `FiniteRingKrullDim` typeclass. Its forward map is definitionally the
existing comparison map.

## Completed objectwise globalization and remaining non-affine target

* `Algebra/RegularLocal/GlobalProjectiveDimension.lean` now proves the
  objectwise version for every regular Noetherian ring, even with unbounded
  Krull dimension. Actual finite-free syzygies give increasing open free loci.
  Each stalk has finite projective dimension by the local theorem, and
  quasi-compactness supplies a bound for each individual finite module.
  `Scheme/Regular/Affine.lean` then proves the canonical all-degree
  `Scheme.KToG_regular_affine_bijective` under only `IsRegularRing R`.
  No common bound over all modules is assumed.
* A general non-affine comparison for vector-bundle K-theory also needs the
  genuine resolution-property argument. Local perfection alone does not
  supply globally defined finite locally free resolution terms.

Primary references: [Stacks 00NN](https://stacks.math.columbia.edu/tag/00NN)
for regular-local algebra, [065U](https://stacks.math.columbia.edu/tag/065U)
for the classical homological theorem, and
[066Z](https://stacks.math.columbia.edu/tag/066Z) for objectwise globalization.
The repository's elementary domain induction avoids needing the
associated-graded/Hilbert–Samuel proof used in the first reference.
