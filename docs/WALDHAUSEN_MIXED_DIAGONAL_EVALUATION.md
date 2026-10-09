# Original diagonal evaluation of the mixed nerve

`MixedNerves/DiagonalEvaluation.lean` regards each original fine chain as a
coarse chain using the given nesting, and retains all original pointwise
coarse horizontal transformations. The genuine diagonal functor then gives
the original diagonal chain: vertex i is F(i)(i), and arrow i→j is the
original horizontal component at i followed by the original fine arrow in
F(j). Both factors are proved coarse weak, hence so is their composite.

The resulting simplicial map commutes with all original ordinal restrictions.
Its composite after the original constant-chain inclusion is strictly the
identity simplicial map. The accepted constant-inclusion homotopy equivalence
therefore yields a genuine homotopy equivalence whose forward map is exactly
this original evaluation and whose inverse is exactly the original constant
inclusion. The proof obtains the necessary inverse homotopy by composing the
already proved homotopies with the strict section identity.

The categorical diagrams retain independent object/hom universes; the
simplicial and realization endpoints use the same explicit object Type(max u
v), hom v scope as the accepted constant comparison. No cylinder, saturation,
extension, kernel closure or fibration conclusion is required.

The source compiles warning-free. The final fixed33-origin recursive audit
and19 consumers (18 examples plus the actual scheme HE definition) pass
warning-free, with only the standard three axioms. An initial explicit
scheme-universe annotation was corrected in the audit alone; no production
source changed. The frozen source manifest is
`logs/mixed-diagonal-evaluation-sources.sha256`; independent review accepted the evaluation boundary.
The audit is
`audits/MixedDiagonalEvaluationAudit.lean`, with original object/arrow maps,
coarse witnesses, strict simplicial section, all ordinal restrictions,
realization section and both prescribed HE maps, degree0, original zero and
an arbitrary-scheme bounded-term specialization.

Independent acceptance on2026-10-09 used four fresh evaluation sources,
fixed111 defining origins and79 original-map/structural-input consumers,
warning-free with unchanged production and dependency hashes. The actual
coarse target and explicit universe scopes were retained.
