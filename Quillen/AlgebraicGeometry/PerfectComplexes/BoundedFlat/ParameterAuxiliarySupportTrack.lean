/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportMaps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack

/-! # Original Laurent tracks on auxiliary support enlargement and restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open ParameterLaurentTrack ParameterLaurentUnit NaturalTrack GeometricSeedCospan
attribute [local irreducible] globalModel

private theorem restrictedUnit {C D : Type*} [Category C] [Category D]
    (p : ObjectProperty C) (q : ObjectProperty D) (H : C ⥤ D)
    (hH : ∀ x : p.FullSubcategory, q (H.obj x.obj))
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves H α β) :
    Preserves (q.lift (p.ι ⋙ H) hH) (lift p.ι α) (lift q.ι β) := by
  intro S
  apply q.ι.map_injective
  exact (congrArg H.map (map_lift_hom p.ι α S)).trans
    ((h (p.ι.obj S)).trans (map_lift_hom q.ι β ((q.lift (p.ι ⋙ H) hH).obj S)).symm)

/-- The actual product pair pullback preserves the original restricted external unit. -/
theorem supportedMap_unit {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (X : Scheme.{u}ᵒᵖ) :
    Preserves ((supportedMap g).app (laurent.op.obj X)).functor
      (supportedUnit B.obj.hom X) (supportedUnit A.obj.hom X) :=
  restrictedUnit (parameterSupported B.obj.hom (laurent.op.obj X))
    (parameterSupported A.obj.hom (laurent.op.obj X)) _
    (fun S => pairReindex_supported ((pairTransformation g).app (laurent.op.obj X).unop)
      S.obj S.property) _ _ (ambientUnit_factor g.hom.right X)

/-- Every original track time is preserved by the actual supported pair pullback. -/
theorem supportedMap_equivariant {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    Equivariant (supportedTrack B.obj.hom) (supportedTrack A.obj.hom)
      (Functor.whiskerRight (supportedMap g) prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (supportedMap_unit g)

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- Support enlargement retains the original forward Laurent action in every time. -/
theorem enlargement_equivariant :
    Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack T.ι)
      (Functor.whiskerRight (enlargement f T) prespectrumFunctor) :=
  supportedMap_equivariant (enlargementPair f T)

omit [IsOpenImmersion f] in
/-- Supported restriction retains the original forward Laurent action in every time. -/
theorem restriction_equivariant :
    Equivariant (supportedTrack T.ι) (supportedTrack (inverseOpen f T).ι)
      (Functor.whiskerRight (restriction f T) prespectrumFunctor) :=
  supportedMap_equivariant (supportRestrictionPair f T)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
