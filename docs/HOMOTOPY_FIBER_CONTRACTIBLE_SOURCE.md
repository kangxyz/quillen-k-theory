# The original loop inclusion for a contractible source

`Quillen/Topology/HomotopyFiber/ContractibleSource.lean` constructs a genuine
homotopy equivalence with the existing original map
`HomotopyFiber.loopInclusion f y x h` as its exact forward map, assuming only
that the source X is contractible and that the displayed equality h is
`f x = y`. The source and target universes are independent.

The domain is the existing compact-open path space `Path y y`. The actual
fiber of `f ∘ const(x) : Unit → Y` is explicitly homeomorphic to that path
space, retaining the entire original path. The accepted source-equivalence
construction then supplies the result from the actual point inclusion into
X. The forward equivalence retains source coordinate x and the full path
coordinate literally. The constant loop maps to the original constant-path
fiber point. The original based homotopy-set map is bijective in every
finite dimension, including zero.

The chosen point-inclusion inverse uses contractibility only. No based
inverse or fixed-track contraction of X is assumed. The lemma has no
fibration hypothesis. In particular it applies to the original tail map
out of the now-proved contractible all-weak relative total. It does not
supply the global relative-realization fiber theorem or identify the
canonical acyclic zero-transformation path; those remain separate assembly
obligations.

Author source check, recursive origin audit, exact-path/basepoint/zero-degree
and actual-relative-tail consumers are recorded in
`audits/HomotopyFiberContractibleSourceAudit.lean` and the corresponding
`logs/homotopy-fiber-contractible-source-*` files. The terminal fixed25-origin audit and all13 consumers pass warning-free
in `logs/homotopy-fiber-contractible-source-audit-final.log`; all recursive
axioms are standard-only. Frozen hashes are in
`logs/homotopy-fiber-contractible-source-sources.sha256`. Independent review passed: fresh two-source rebuild of this and the
ordinary-row companion, fixed42 combined origins and29 consumers,
warning-free with all hashes unchanged.
