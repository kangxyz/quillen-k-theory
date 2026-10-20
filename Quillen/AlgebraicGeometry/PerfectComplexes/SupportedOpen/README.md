# Auxiliary support, excision, and Mayer–Vietoris

## Auxiliary support and its naturality

For an auxiliary open `T`, `PerfectSupportedOpenK j T n` uses objects acyclic
on `T`, with weak equivalences detected on `U`. The absolute open endpoint is
supported away from `j ⁻¹ᵁ T`; the fiber is supported away from `U ∪ T`.
If `X` is qcqs and `U,T` are quasi-compact, its positive endpoint is
`qcqsPerfectSupportedOpenKEquiv`, and degree zero identifies the exact restriction
image. `qcqsPerfectSupportedConnectingHom`,
`qcqsPerfectSupported_positiveLongExactSequence`, and
`qcqsPerfectSupported_zeroTail` retain these original maps.
See [SupportedOpen/GlobalLocalization.lean](GlobalLocalization.lean).

The actual supported boundary and positive inverse endpoint are natural for
arbitrary commuting support and localization squares between qcqs ambient
schemes with quasi-compact localization and auxiliary opens. Neither flatness
nor cartesianness is required. Relative boundary naturality needs only
quasi-compact ambient schemes; relative restriction additionally needs
quasi-compact localization opens.
See [SupportedOpen/PairNaturality.lean](PairNaturality.lean).
Fixed-base inclusions `S ≤ T` and forgetting support also commute with the
boundaries. See [SupportedOpen/AuxiliaryNaturality.lean](AuxiliaryNaturality.lean).

## Support excision and Mayer–Vietoris

For any open immersion `j : U ⟶ X` and auxiliary open `T` with
`j(U) ∪ T = X`, `perfectSupportedExcisionKEquiv` identifies the original
supported groups on `X` and `U` in every nonnegative degree. Its forward map is
restriction, and its inverse is the actual exact extension-by-zero map. The
unit and counit give weak equivalences and realization homotopy inverses.
No quasi-compactness or quasi-separatedness is assumed.
See [SupportedOpen/Excision.lean](Excision.lean).

For a qcqs scheme `X = U ∪ V` with quasi-compact opens, the original restrictions
and boundary give the connective sequence

```text
Kₙ₊₁(U) × Kₙ₊₁(V) → Kₙ₊₁(U ∩ V) → Kₙ(X)
                    → Kₙ(U) × Kₙ(V) → Kₙ(U ∩ V).
```

`PerfectMayerVietoris.overlapDifference` is the first restricted class multiplied
by the inverse of the second. `qcqs_positiveExactSequence` supplies the recurring
positions; `qcqs_completeZeroTail` includes exactness at the local K₀ pair.
`qcqs_matching_zero_classes_glue` gives a global K₀ class for any matching local
pair. It does not require either single-open restriction to be surjective.
See [MayerVietoris.lean](../MayerVietoris.lean).

`SupportedMayerVietoris` gives the supported sequence and matching-class gluing
with a quasi-compact auxiliary acyclicity open `Z`; its boundary is compatible
with forgetting support. The geometric cover reflection and cylinder inputs are
discharged in the qcqs wrappers. No surjectivity onto overlap K₀ or negative
boundary is asserted.
See [SupportedOpen/MayerVietoris.lean](MayerVietoris.lean)
and [SupportedOpen/MayerVietorisForget.lean](MayerVietorisForget.lean).

## Auxiliary-supported constructed completion

Let `f : P → Q` be the actual open arrow over `Spec R`, `T ⊂ Q` the open
complement of the auxiliary closed support, and `a : Under R`. Retain the
original coefficient fibers and projection pullbacks. Write `T_a` for the
pullback of `T` and `V_a = T_a ∪ range(f_a)`.

| Construction | Original data retained | Conditions |
| --- | --- | --- |
| Auxiliary finite/telescope transfer | Literal `B^i(C_Z/F_Z/G_Z)`, original transitions, `r_i/q_i`, iterated canonical `N_i`, every whole null-transition equation, signed `G_Z∞` vanishing, original `Cone(r_Z∞) → G_Z∞` and stable `r_Z∞` | Graded coefficient data require compact `P,Q`. Final cone/restriction stability additionally requires quasi-separated `Q` and compact `T`. |
| Native auxiliary fiber | Sections vanishing on `V_a`, literal forget into sections vanishing on `T_a`, identity change of weakness to `C_Z`, and the reversed zero-to-image null | `CoefficientSupportedFiberLocalizationModels` supplies actual JointData, second-endpoint, extension and two-out-of-three inputs and identifies the fiber with the acyclic category of the same native weak structure. The same-null initial cone comparison needs no compactness or separation. |
| Seeds and coarse completion | The same ambient forward Laurent unit on the `V_a`-supported fiber, forget/changeWeak seed squares, every canonical-null time-slice square, actual finite towers/telescope null, and stable `Cone(forget∞) → C_Z∞` | Only the original open immersion. Original inclusions, whole identity-action interchange, finite Model excision/T1 and telescope cone descent retain independent null time and telescope height. No supplied compatibility or localization input. |
| Final fine auxiliary sequence | Postcomposition with original `r_Z∞`, same-null stable fiber lift for `Fiber_Z∞ → A_Z∞ → F_Z∞`, projection and signed connecting identity | Compact `P,Q,T` and quasi-separated `Q` for final fine stability. Projection and boundary identities retain only the open immersion. |

The same joint zero is retained throughout the fiber, native acyclic
equivalence, fibration inputs, and every level/time value of the canonical
null. This does not identify independently chosen geometric zeros.

The [tensor-generated Bass realization](../BoundedFlat/TensorBassConstruction.md)
directly proves the auxiliary statement of original TT 7.4. For qcqs `X`,
quasi-compact `U ⊂ X`, and closed `Z` with quasi-compact complement `T`, its
three support objects are `(X, (X ∖ U) ∩ Z)`, `(X, Z)`, and `(U, U ∩ Z)`.
They are defined by acyclicity on `U ∪ T`, `T`, and the inverse image of `T`;
the arrows are actual support enlargement and open restriction.
[`ParameterAuxiliaryCurrentFiber.currentLift_integer_isStableEquivalence`](../BoundedFlat/ParameterAuxiliaryCurrentLocalization.lean)
proves stability of their canonical-null fiber lift, and
`currentLift_integer_signed_isIso` covers every integer degree. This gives
the supported long exact sequence as well. Comparison with the
[separately prescribed raw implementation](../Development.md#comparison-with-the-prescribed-raw-point-set-implementation)
and its chosen class/boundary conventions remains an additional task.
