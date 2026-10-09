# Independent review: original finite and global K-class Euler reduction

The two exact sources in `logs/gillet-waldhausen-euler-reduction-checked-sources.sha256`
were read completely and freshly rebuilt in an isolated overlay. The fixed
59-origin recursive audit and all 16 consumers passed warning-free, including
explicit finite and global arbitrary-scheme specializations. Final source hashes
match. The final fixed audit is `logs/euler-independent-audit-final.log`.

## Exact mathematical endpoint

The finite theorem identifies the original acyclic inclusion, in the genuine
finite term/cycle K equivalences, with the already proved adjacent-coordinate
incidence homomorphism. The original single-complex insertion is literally the
single-coordinate homomorphism. Every fine class for [a,a+m] consequently has
one unique original acyclic class and one original chosen-term class whose
original KMap images multiply to it. The coordinate can be any actual term;
the zero-width interval and K₀ are included.

The global theorem uses actual symmetric finite-stage representation, the
true degree-zero coordinate N in [-N,N], and original inclusion/transition
KMap squares. Actual eventual-zero detection reduces the joint kernel to a
finite stage. Finite uniqueness gives the original acyclic and single-term
classes, and the existing group operations give global uniqueness. No globally
uniform bound, Euler map, exactness of a conjectural sequence, or fibration
conclusion is assumed.

The abstract decomposition needs zero containment, repleteness, extension
closure, and kernel closure. Kernel closure is needed for the actual cycles;
the original single functor and its exactness/transition equations do not need
it. The mixed-universe contract is A : Type(max u v), Category.{v} A. The finite
scheme specialization uses actual finite-locally-free sheaves with the proved
kernel closure and no regularity or noetherianity assumption.

This is a group-level decomposition in the original isomorphism-weak bounded
complex model. It is separate from the still-open fibration and the comparison
with the quasi-isomorphism model.

## Evidence

- Fresh targets: `/tmp/quillen-euler-independent-0850`.
- Before/after hashes: `logs/euler-independent-{prehash,posthash}.log`.
- Fresh dependency paths and builds: `logs/euler-independent-build.log`.
- Fixed audit: `audits/GilletWaldhausenEulerIndependentAudit.lean`.
- Replay: `logs/verify-euler-independent.sh`.
- Allowed recursive axioms: propext, Classical.choice, Quot.sound only.
