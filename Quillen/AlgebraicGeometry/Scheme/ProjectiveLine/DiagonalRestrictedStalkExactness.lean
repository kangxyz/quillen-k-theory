/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.SectionStalk
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCokernel
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalClosedImmersion
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.StalkFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Tensor exactness of the original diagonal sequence after scalar restriction

At a point on the original relative diagonal, restrict the actual module-stalk
sequence along the original first projection, with its canonical point transport.
Its quotient is the original quotient-line stalk with its original scalar action,
hence is flat. Tensoring this restricted sequence with any stalk module is short
exact. This does not yet identify the result with the stalks of the sheafified
tensor sequence: the native tensor/stalk comparison remains a separate obligation.
-/
@[expose] public section
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules

/-- Restriction of the original incidence stalk sequence along the original first projection. -/
def diagonalRestrictedStalkSequence (R : CommRingCat.{u}) (x : twoChartLine R) :
    ShortComplex (ModuleCat.{u} ((twoChartLine R).presheaf.stalk x)) :=
  ((diagonalIncidenceSequence R).map (moduleStalk (relativeSquare R) (relativeDiagonal R x))).map
    (ModuleCat.restrictScalars
      (sectionStalkRingMap (relativeDiagonal R) (relativeFirst R) (relativeDiagonal_first R) x).hom)

/-- The original incidence and quotient remain short exact under these exact stalk functors. -/
theorem diagonalRestrictedStalkSequence_shortExact (R : CommRingCat.{u}) (x : twoChartLine R) :
    (diagonalRestrictedStalkSequence R x).ShortExact :=
  ((diagonalIncidenceSequence_shortExact R).map_of_exact
    (moduleStalk (relativeSquare R) (relativeDiagonal R x))).map_of_exact _

/-- The actual quotient stalk, with scalar restriction, is the original quotient-line stalk. -/
def diagonalRestrictedQuotientStalkIso (R : CommRingCat.{u}) (x : twoChartLine R) :
    (diagonalRestrictedStalkSequence R x).X₃ ≅
      (moduleStalk (twoChartLine R) x).obj (tautologicalQuotientLine R) :=
  (sectionPushforwardModuleStalkIso (relativeDiagonal R) (relativeFirst R)
    (relativeDiagonal_first R)
    (isClosedImmersion_relativeDiagonal R).isClosedEmbedding.isInducing x).app
      (tautologicalQuotientLine R)

/-- The quotient identification uses the unchanged canonical germ map. -/
theorem diagonalRestrictedQuotientStalkIso_germ (R : CommRingCat.{u}) (x : twoChartLine R)
    (U : (relativeSquare R).Opens) (hx : relativeDiagonal R x ∈ U)
    (s : Γ(tautologicalQuotientLine R, relativeDiagonal R ⁻¹ᵁ U)) :
    (diagonalRestrictedQuotientStalkIso R x).hom
      ((diagonalIncidenceSequence R).X₃.presheaf.germ U (relativeDiagonal R x) hx s) =
      (tautologicalQuotientLine R).presheaf.germ (relativeDiagonal R ⁻¹ᵁ U) x hx s :=
  pushforwardModuleStalkMap_germ (relativeDiagonal R) x (tautologicalQuotientLine R) U hx s

/-- The quotient of the restricted original stalk sequence is flat over the source local ring. -/
instance diagonalRestrictedStalkSequence_flat_quotient (R : CommRingCat.{u})
    (x : twoChartLine R) :
    Module.Flat ((twoChartLine R).presheaf.stalk x) (diagonalRestrictedStalkSequence R x).X₃ := by
  let : Module.Flat ((twoChartLine R).presheaf.stalk x)
      ((moduleStalk (twoChartLine R) x).obj (tautologicalQuotientLine R)) :=
    stalkwiseFlat_of_finiteLocallyFree (tautologicalQuotientLine R) x
  exact Module.Flat.of_linearEquiv (diagonalRestrictedQuotientStalkIso R x).toLinearEquiv

/-- Tensor with any module preserves the original incidence stalk's injectivity
when the sequence is restricted along the original first projection. -/
theorem diagonalRestrictedStalkSequence_lTensor_injective (R : CommRingCat.{u})
    (x : twoChartLine R) (E : ModuleCat.{u} ((twoChartLine R).presheaf.stalk x)) :
    Function.Injective ((diagonalRestrictedStalkSequence R x).f.hom.lTensor E) := by
  let S := diagonalRestrictedStalkSequence R x
  have hS := diagonalRestrictedStalkSequence_shortExact R x
  exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hS.moduleCat_surjective_g
    S.f.hom hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) E

/-- Full tensor short exactness for arbitrary coefficients at an actual diagonal point.
The tensor functor here is over the source local ring after scalar restriction. -/
theorem diagonalRestrictedStalkSequence_tensor_shortExact (R : CommRingCat.{u})
    (x : twoChartLine R) (E : ModuleCat.{u} ((twoChartLine R).presheaf.stalk x)) :
    ((diagonalRestrictedStalkSequence R x).map
      (MonoidalCategory.tensorLeft E)).ShortExact := by
  let S := diagonalRestrictedStalkSequence R x
  let T := MonoidalCategory.tensorLeft E
  have hS := diagonalRestrictedStalkSequence_shortExact R x
  have hmono : Mono (T.map S.f) :=
    (ModuleCat.mono_iff_injective _).mpr
      (diagonalRestrictedStalkSequence_lTensor_injective R x E)
  let : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hr := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi T).mp inferInstance S hS
  exact { exact := hr.1, mono_f := hmono, epi_g := hr.2 }

/-- The original diagonal quotient stalk vanishes off the original diagonal image. -/
theorem diagonalQuotientModuleStalk_isZero_off_image (R : CommRingCat.{u})
    (y : relativeSquare R) (hy : y ∉ Set.range (relativeDiagonal R)) :
    IsZero ((moduleStalk (relativeSquare R) y).obj (diagonalIncidenceSequence R).X₃) := by
  let : IsClosedImmersion (relativeDiagonal R) := isClosedImmersion_relativeDiagonal R
  exact isZero_closedImmersion_moduleStalk_of_not_mem (relativeDiagonal R) y hy
    (tautologicalQuotientLine R)

/-- Off the original diagonal, the actual incidence stalk arrow is invertible. -/
theorem diagonalIncidence_moduleStalk_isIso_off_image (R : CommRingCat.{u})
    (y : relativeSquare R) (hy : y ∉ Set.range (relativeDiagonal R)) :
    IsIso ((moduleStalk (relativeSquare R) y).map (diagonalIncidence R)) :=
  ((diagonalIncidenceSequence_shortExact R).map_of_exact
    (moduleStalk (relativeSquare R) y)).isIso_f_iff.mpr
      (diagonalQuotientModuleStalk_isZero_off_image R y hy)

/-- The original diagonal pushforward is exact for arbitrary module sheaves. -/
theorem diagonalPushforward_shortExact_all (R : CommRingCat.{u})
    {S : ShortComplex (twoChartLine R).Modules} (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pushforward (relativeDiagonal R))).ShortExact := by
  let : IsClosedImmersion (relativeDiagonal R) := isClosedImmersion_relativeDiagonal R
  exact shortExact_pushforward_of_closedImmersion (relativeDiagonal R) hS

end AlgebraicGeometry.Scheme.ProjectiveLine
