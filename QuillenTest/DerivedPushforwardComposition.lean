/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalIncidence

/-!
# Original bounded-below flasque and derived-composition consumers

The tests retain arbitrary integer degrees, the original cochain maps and
installed units, and both original pushforward composition factors. They
include the actual projective-line diagonal followed by its second projection.
No upper term bound, flatness or injective-preservation premise is imposed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace QuillenTest.DerivedPushforwardComposition

open Quillen

/-- Standard original module-sheaf derived categories. -/
local instance compositionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The exact integer kernel sequence retains its literal differential kernel lift. -/
theorem original_integer_kernel {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (n : ℤ) (hK : K.ExactAt (n + 1)) :
    (CochainComplex.kernelSequence K n).ShortExact ∧
      (CochainComplex.kernelSequence K n).g =
        kernel.lift (K.d (n + 1) (n + 2)) (K.d n (n + 1))
          (K.d_comp_d n (n + 1) (n + 2)) :=
  ⟨CochainComplex.kernelSequence_shortExact K n hK, rfl⟩

/-- Original direct image preserves every degree of a bounded-below acyclic flasque complex. -/
theorem original_acyclic_direct_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex X.Modules ℤ) (a : ℤ)
    (hl : ∀ n, n < a → IsZero (K.X n)) (hA : K.Acyclic)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).presheaf) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  intro n
  have h := pushforward_exactAt_succ_of_acyclic_flasque f K a hl hA hK (n - 1)
  simpa only [sub_add_cancel] using h

/-- An arbitrary original quasi-isomorphism between bounded-below flasque complexes survives. -/
theorem original_quasi_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex.Plus X.Modules} (q : K ⟶ L) [QuasiIso q.hom]
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf)
    (hL : ∀ n, TopCat.Presheaf.IsFlasque (L.obj.X n).presheaf) :
    QuasiIso (((Scheme.Modules.pushforward f).mapCochainComplexPlus.map q).hom) := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  let := ha
  let := hb
  exact quasiIso_pushforward_of_flasque f q.hom a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE L.obj b n hn) hK hL

/-- The actual installed unit has an inverse without an upper-bound hypothesis. -/
theorem original_flasque_unit_inverse {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex.Plus X.Modules)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf) :
    letI := isIso_derivedPushforwardPlusUnit_of_flasque f K hK
    (derivedPushforwardPlusUnit f).app K ≫
      inv ((derivedPushforwardPlusUnit f).app K) = 𝟙 _ := by
  let := isIso_derivedPushforwardPlusUnit_of_flasque f K hK
  exact IsIso.hom_inv_id _

/-- The geometric composition map preserves both original derived units in their actual order. -/
theorem original_composite_units {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex.Plus X.Modules) :
    (derivedPushforwardPlusUnit (f ≫ g)).app K ≫
        (derivedPushforwardPlusCompIso f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp f g)).inv.app K) ≫
      (derivedPushforwardPlusUnit g).app
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K) ≫
      (derivedPushforwardPlus g).map ((derivedPushforwardPlusUnit f).app K) := by
  rw [derivedPushforwardPlusCompIso_unit, Functor.rightDerivedFunctorPlusCompUnit_app]
  rfl

/-- Naturality uses an arbitrary original bounded-below derived morphism. -/
theorem original_derived_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {K L : DerivedCategory.Plus X.Modules} (q : K ⟶ L) :
    (derivedPushforwardPlus (f ≫ g)).map q ≫ (derivedPushforwardPlusCompIso f g).hom.app L =
      (derivedPushforwardPlusCompIso f g).hom.app K ≫
        (derivedPushforwardPlus g).map ((derivedPushforwardPlus f).map q) :=
  (derivedPushforwardPlusCompIso f g).hom.naturality q

/-- The actual diagonal followed by the second projection computes
the derived geometric identity. -/
def originalDiagonalSecond (R : CommRingCat.{u}) :
    derivedPushforwardPlus (𝟙 (twoChartLine R)) ≅
      derivedPushforwardPlus (relativeDiagonal R) ⋙ derivedPushforwardPlus (relativeSecond R) :=
  (Scheme.Modules.pushforward (𝟙 (twoChartLine R))).rightDerivedFunctorPlusIso
      (Scheme.Modules.pushforwardCongr (relativeDiagonal_second R)).symm ≪≫
    derivedPushforwardPlusCompIso (relativeDiagonal R) (relativeSecond R)

end QuillenTest.DerivedPushforwardComposition
