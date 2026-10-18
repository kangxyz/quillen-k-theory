# Adjacent permutation presentations

`Presentation.lean` proves the type-A adjacent-transposition presentation of
`Equiv.Perm (Fin (n + 1))`, including the bubble-word construction. Its universal
property takes generators satisfying square, distant-commutation and braid
relations. The final injectivity theorem additionally takes generation by those
marked generators and the specified native permutation projection.

The declaration namespace is `Equiv.Perm.AdjacentPresentation`. The intended
upstream owner is `Aglib.Algebra.Group.Perm.AdjacentPresentation.Presentation`.
The current consumer is the root-coordinate normalizer's Weyl quotient in
`Quillen.Algebra.Group.StableSteinberg.Matsumoto.Normalizer`.
