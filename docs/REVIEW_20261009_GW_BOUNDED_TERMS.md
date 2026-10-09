# Independent review: bounded termwise complexes and acyclic inclusion

Date: 2026-10-09. Result: **accepted for the frozen two-source boundary**.
No implementation source was modified.

## Exact accepted contract

The ambient category is any abelian category `A : Type u` with
`Category.{v} A`; object and hom universes are independent. The predicate
`boundedTerms P K` is exactly actual strict term boundedness together with
membership of every actual complex term in `P`. It is not merely bounded
homology or a packaged resolution/equivalence assertion.

The closure assumptions are minimal and explicit:

- Integer shifts preserve this predicate for arbitrary `P`, with no closure
  assumptions. Bounds translate by the actual shift integer.
- Actual short-exact extensions preserve it under extension closure of `P`
  alone. Term bounds use the minimum lower and maximum upper endpoint bounds;
  the degreewise actual short exact sequences supply term membership.
- Actual mapping cones remain bounded and termwise in `P` under repleteness
  and extension closure. This theorem does not require `P.ContainsZero`.
  The proof uses the actual cone-term biproduct isomorphism and explicit
  translated bounds.
- With zero membership, repleteness, and extension closure, the actual full
  subcategory inherits its exact structure. Finite-product closure is derived;
  neither kernel closure nor projectivity is an input.

`boundedAcyclicTermsInclusion P` is literally the full-subcategory inclusion
from the previously defined bounded acyclic complexes into bounded termwise
complexes. It leaves every underlying complex and chain map unchanged.
`boundedAcyclicTermsExactInclusion` preserves the actual inherited conflations,
and the quasi-exact inclusion additionally preserves the actual quasi-isomorphism
class and all pushouts along inherited cofibrations.

The inflation-reflection theorem is honest about admissibility. Given an
inherited ambient inflation between acyclic objects, it starts with its actual
bounded termwise admissible quotient. A map between acyclic complexes is a
quasi-isomorphism; the actual short exact homology sequence therefore proves
that quotient is acyclic. The same quotient and maps then witness the original
acyclic-category inflation. No arbitrary quotient closure, kernel closure, or
blanket assertion about all ambient monomorphisms is assumed.

For any map from any actual zero object, the weak-equivalence condition is
proved equivalent to actual acyclicity of the target complex. Specializing to
the chosen Waldhausen zero identifies the weakly acyclic objects exactly with
the original bounded acyclic predicate. Weak equivalences remain the ambient
`HomologicalComplex.QuasiIso` condition on the unchanged chain map.

I read both new modules and the relevant complete `BoundedAcyclic` and
`ComplexSubcategory` dependencies. The latter's cofibrations are inherited
ambient conflations whose quotient remains inside, and its weak equivalences
are genuine quasi-isomorphisms. No desired K-equivalence, fibration, or homotopy
conclusion occurs in any input of these new endpoints.

## Independent verification

The two source files were rebuilt into a fresh isolated namespace, with
unchanged dependency artifacts linked and the two selected artifacts newly
compiled. `lean --deps` confirms the final module selects the isolated
`BoundedTerms` artifact. No production olean was replaced, and no live Lake
build was used. Lean 4.34.0 ran with `-j1` and the shared slot1 lock; acquisition
is logged. Both fresh sources and the independent audit are warning-free.

`audits/GWBoundedTermsIndependentAudit.lean` checks exactly **27 defining
origins** from the two modules, including private/generated declarations
(15 in `BoundedTerms`, 12 in `BoundedTermsAcyclic`). Recursive `collectAxioms`
permits only `propext`, `Classical.choice`, and `Quot.sound`. All 27 pass.
The author's larger 455-origin scan covers these same new declarations among
all 21 existing GW modules; this independent scan deliberately fixes the new
boundary and recursively checks its dependencies' axioms.

Consumers explicitly check:

- independent object/hom universes;
- shift closure without any predicate closure assumptions;
- short-exact extension closure without zero or repleteness assumptions;
- cone closure without zero membership;
- the actual inherited exact structure and unchanged inclusion objects/maps;
- inherited cofibration reflection and literal weak-class agreement;
- quasi-isomorphism-from-zero and chosen-zero acyclicity equivalences;
- the actual inherited joint-cylinder cofibration obtained from the proved
  cone and shift closure;
- on an arbitrary scheme, `boundedTerms (finiteLocallyFree X)` equals the
  accepted `strictPerfect X` predicate by **rfl**.

Both new hashes match before/after. I also reconstructed the 19 earlier frozen
source hashes from their checked manifests, found no conflicts, and rechecked
all 19 successfully. No source repair was needed.

## Limits

This is the ambient bounded-complex category and its actual acyclic inclusion,
with the stated structural properties. It does not prove a fibration or
Gillet–Waldhausen equivalence, a brutal-truncation filtration, or a new K-map
comparison. Kernel closure remains a separate prerequisite for the earlier
cycle-membership and cycle-functor results. The checked cylinder consumer is
the actual inherited joint-cofibration input, not a full fibration theorem.

## Frozen sources and evidence

Manifest: `logs/gw-bounded-terms-independent-20261009/sources.sha256`

Manifest SHA-256:
`2de6e62bd0106c5d62436859ba552395734506fecc626ffe79930d74ef1c55af`

- `BoundedTerms.lean`: `71fd26e8e8e7473a8e7b0af612ded7a83342078ea47f6ba5aca265b81415bb1f`
- `BoundedTermsAcyclic.lean`: `c9c7606f82baed6de1a515568611b077b3a24945a58525d75c5c54e0fcc8203d`

Evidence directory: `logs/gw-bounded-terms-independent-20261009/`

- `check.log`: fresh ordered source checks
- `audit.log`: fixed27 recursive origin audit and exact consumers
- `deps.log`: selected fresh dependency paths
- `hashes-before.log`, `hashes-after.log`: new source rechecks
- `prior19-sources.sha256`, `prior19-hashes-after.log`: earlier frozen boundary recheck
- `artifacts.sha256`: exact independent audit, report, logs and fresh oleans

Independent audit SHA-256:
`55771d56274155acd67160c7111d2e251c383af5db240c6787e1a8e2e9c11895`

Audit log SHA-256:
`1d71785adc10e20ed16603ca84ae5e11dd89a6be2936a02089b7731796aff909`
