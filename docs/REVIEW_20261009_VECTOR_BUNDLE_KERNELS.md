# Independent review: vector-bundle kernels on arbitrary schemes

Accepted 2026-10-09 05:16 UTC. This is an algebraic prerequisite for the
Gillet–Waldhausen comparison, not that comparison itself.

## Mathematical result

The two reviewed sources are `Scheme/VectorBundle/AffineProjective.lean` and
`Scheme/VectorBundle/KernelClosure.lean` below `Quillen/`.

On an arbitrary affine scheme, finite local bases give a principal-open cover
on which actual sections are free. Global finite generation makes these local
modules finite free. Finite presentation descends along this cover, and the
proved local-free criterion then gives actual projectivity over the arbitrary
base ring. There is no noetherian assumption.

An ambient short exact sequence with vector-bundle middle and right terms has
a quasicoherent kernel. The actual affine quasicoherent equivalence takes the
sequence to a short exact sequence of modules. Projectivity of the right term
gives a genuine splitting, so the kernel is finite projective. The original
kernel sheaf is recovered through the actual tilde/sections isomorphism.
Restriction to the canonical affine cover and finite-local-freeness descent
give the theorem on every scheme.

Consequently `finiteLocallyFree_kernelClosed` is a proved instance, and
`vectorBundle_deflation_of_ambient_epi` requires only that the underlying map
of module sheaves be epi. The actual categorical kernel lies in the bundle
subcategory and supplies its inherited conflation. Global sheaf projectivity,
regularity, resolution property and quasi-compactness are not assumed.

## Independent verification

Both sources were read in full and rebuilt warning/error-free into an isolated
artifact overlay, excluding their live artifacts. Source hashes matched before
and after. A recursive all-origin audit covered their 7 declarations together
with the 27 declarations of the separately reviewed acyclic truncation functor.
Only the three standard Lean logical foundations occurred. Arbitrary-universe
consumers checked finite presentation/projectivity, kernel closure, the original
ambient-epi deflation, and its use in the actual vector-bundle-valued acyclic
truncation functor. The fixed-count rerun at 34 also passed, with its completion recorded in the
audit log.

Evidence: `audits/VectorBundleKernelIndependentAudit.lean`,
`logs/vb-kernel-independent-{check,audit,hashes}.log`, and
`logs/vb-kernel-independent-sources.sha256` (manifest SHA-256
`533eb5fd18b5b88acac8251e8d51bd1cf2caf3c0b72398f8fd825e56b984db2b`).

## Acyclic truncation functor review

`Waldhausen/GilletWaldhausen/TruncationFunctor.lean` was also read fully and
independently rebuilt. It uses mathlib's unchanged truncation map, the original
chain map, and the induced categorical cokernel map. Identity and composition
are proved; the resulting functor lands in the full category of inherited
conflations. Forgetting only the conflation proof gives exactly the short-complex
functor. Exactness of the functor and the K-theory comparison are separate.

These sources postdate, and are excluded from, the frozen 05:00 checkpoint.
