# Transport through actual common-base fiber models

`CommonBaseSquareTransport.lean` takes actual continuous maps over one common
base, actual source-to-fiber-model maps k₀ and k₁, and their strict original
projection and transition squares. It constructs the source-change map on
homotopy pullbacks with unchanged parameter and complete outer path. After
the displayed projection equality is literal, that map is exactly the
accepted `HomotopyPullback.sourceMap`.

The original model-square comparison, followed by this source-change map,
is proved equal to the original `commonBaseComparison` followed by k₀. Both
the entire fiber coordinate and the constant outer comparison path are kept.
Consequently, if k₀ and k₁ are genuine weak homotopy equivalences, accepted
weak source invariance and weak cancellation prove that the original
model-square comparison is a weak homotopy equivalence.

The two weak fiber-model hypotheses are explicit inputs about actual given
maps. The theorem does not construct or assume hidden proofs of either
global relative-tail fiber comparison. In particular, it does not yet prove
the Waldhausen fibration theorem or the canonical acyclic fiber equivalence.
No lifting hypothesis on the original maps is added. All spaces use the
single universe of the existing homotopy-pullback and lifting APIs, and the
weak conclusion retains empty spaces and degree zero.

The source compiled warning-free. The initial single-pass audit measured
all10 origins and all8 consumers passed, using only the standard three
axioms recursively. The source is frozen in
`logs/homotopy-fiber-common-base-transport-sources.sha256`; the fixed10 guard
replay also passed warning-free in
`logs/homotopy-fiber-common-base-transport-audit-final.log`. Independent fresh3/fixed[10,15,16]=41
review of this source and the original total-tail pair passed all33 consumers
with unchanged full dependency hashes on 2026-10-09 at14:07:08 UTC.
