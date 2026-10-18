/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Localization.Serre.Naturality
public import Quillen.GTheory.FiniteModules.LocalizationSequence
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-!
# Naturality of the original finite-module localization boundary

An ordinary natural isomorphism between two composites of exact finite-module
functors induces a square on the actual chosen small-model localization
sequences. The support functor is the restriction of the original small-model
ambient functor. Preservation of the kernel is a consequence of the ordinary
localization square.

`connectingHom_naturality` retains the original `connectingHom` on both sides
and the original `smallKMap` on localized modules. The proof transports the
canonical Serre boundary theorem through both actual `smallAbelianKEquiv`
comparisons. All endpoints use the common native universe `u`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat

namespace Quillen.FiniteModuleLocalization

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The original small-model exact functor, expressed with the standard abelian
exact structures on the same chosen small categories. -/
def smallAbelianExactFunctorOfExact {R T : Type u} [CommRing R] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T]
    (V : ExactFunctor (finiteModuleExactStructure.{u, u} R) (finiteModuleExactStructure.{u, u} T)) :
    ExactFunctor (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} R)))
      (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} T))) where
  toFunctor := V.smallModel.toFunctor
  map_conflation S h := by
    have h₀ : (finiteModuleExactStructure.{u, u} R).smallModel.conflation S := by
      change ((abelianExactStructure (FGModuleCat.{u} R)).smallModel).conflation S
      rw [abelianExactStructure_smallModel]
      exact h
    have h₁ := V.smallModel.map_conflation S h₀
    change ((abelianExactStructure (FGModuleCat.{u} T)).smallModel).conflation
      (S.map V.smallModel.toFunctor) at h₁
    rw [abelianExactStructure_smallModel] at h₁
    exact h₁

/-- The original small K-map commutes with the identity comparison between
transported and standard abelian exact structures. -/
theorem smallKMap_comparison_of_exactFunctor {R T : Type u} [CommRing R] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T]
    (V : ExactFunctor (finiteModuleExactStructure.{u, u} R) (finiteModuleExactStructure.{u, u} T))
    (n : ℕ) :
    (smallAbelianKEquiv T n).toMonoidHom.comp (V.smallKMap n) =
      ((smallAbelianExactFunctorOfExact V).KMap n).comp (smallAbelianKEquiv R n).toMonoidHom := by
  change ((smallModelToAbelian T).KMap n).comp (V.smallModel.KMap n) =
    ((smallAbelianExactFunctorOfExact V).KMap n).comp ((smallModelToAbelian R).KMap n)
  rw [← ExactFunctor.KMap_comp, ← ExactFunctor.KMap_comp]
  rfl

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
  (S : Submonoid R) (T : Submonoid R')
  (V : ExactFunctor (finiteModuleExactStructure.{u, u} R) (finiteModuleExactStructure.{u, u} R'))
  (W : ExactFunctor (finiteModuleExactStructure.{u, u} (Localization S))
    (finiteModuleExactStructure.{u, u} (Localization T)))
  (hV : ∀ X : SmallModel.{u} (FGModuleCat.{u} R), smallTorsion S X →
    smallTorsion T (V.smallModel.toFunctor.obj X))
  (e : ((exactFunctor S).comp W).toFunctor ≅ (V.comp (exactFunctor T)).toFunctor)

/-- Restrict the original small-model ambient functor to the actual support kernels. -/
def inducedSupportedExactFunctor : ExactFunctor (ObjectProperty.subcategoryExactStructure
    (smallTorsion S)) (ObjectProperty.subcategoryExactStructure (smallTorsion T)) :=
  SerreLocalization.inducedSupportExactFunctor (smallTorsion S) (smallTorsion T)
    (smallAbelianExactFunctorOfExact V) hV

/-- The given ordinary square transported through the canonical small-model
composition isomorphisms, with all original localization functors retained. -/
def smallLocalizationSquareIso :
    smallFunctor S ⋙ (smallAbelianExactFunctorOfExact W).toFunctor ≅
      (smallAbelianExactFunctorOfExact V).toFunctor ⋙ smallFunctor T :=
  (ExactFunctor.smallModelCompIso (exactFunctor S) W).symm ≪≫
    ExactFunctor.smallModelNatIso e ≪≫ ExactFunctor.smallModelCompIso V (exactFunctor T)

include e in
/-- An exact localization square carries its actual Serre kernel into the target kernel. -/
theorem smallTorsion_map_of_exactSquare (X : SmallModel.{u} (FGModuleCat.{u} R))
    (hX : smallTorsion S X) : smallTorsion T (V.smallModel.toFunctor.obj X) := by
  have hz : IsZero ((smallAbelianExactFunctorOfExact W).toFunctor.obj ((smallFunctor S).obj X)) :=
    (smallAbelianExactFunctorOfExact W).toFunctor.map_isZero hX
  exact hz.of_iso ((smallLocalizationSquareIso S T V W e).app X).symm

/-- The canonical restricted exact functor whose kernel preservation follows
from the given ordinary localization square. -/
def inducedSupportedExactFunctorOfSquare : ExactFunctor
    (ObjectProperty.subcategoryExactStructure (smallTorsion S))
    (ObjectProperty.subcategoryExactStructure (smallTorsion T)) :=
  inducedSupportedExactFunctor S T V (smallTorsion_map_of_exactSquare S T V W e)

include e in
/-- Naturality of the original finite-module boundary, retaining any supplied
proof that the original ambient functor preserves the actual support kernel. -/
theorem connectingHom_naturality_of_exactSquare (n : ℕ) :
    ((inducedSupportedExactFunctor S T V hV).KMap n).comp (connectingHom S n) =
      (connectingHom T n).comp (W.smallKMap (n + 1)) := by
  let U := smallAbelianExactFunctorOfExact W
  have hn := SerreLocalization.actualConnectingHom_naturality (smallTorsion S) (smallTorsion T)
    (smallAbelianExactFunctorOfExact V) hV (smallFunctor S) (smallFunctor T)
    U (smallLocalizationSquareIso S T V W e) n
  apply MonoidHom.ext
  intro a
  change (inducedSupportedExactFunctor S T V hV).KMap n
      (SerreLocalization.actualConnectingHom (smallTorsion S) (smallFunctor S) n
        (smallAbelianKEquiv (Localization S) (n + 1) a)) =
    SerreLocalization.actualConnectingHom (smallTorsion T) (smallFunctor T) n
      (smallAbelianKEquiv (Localization T) (n + 1) (W.smallKMap (n + 1) a))
  have hu := DFunLike.congr_fun (smallKMap_comparison_of_exactFunctor W (n + 1)) a
  change smallAbelianKEquiv (Localization T) (n + 1) (W.smallKMap (n + 1) a) =
    U.KMap (n + 1) (smallAbelianKEquiv (Localization S) (n + 1) a) at hu
  exact (DFunLike.congr_fun hn (smallAbelianKEquiv (Localization S) (n + 1) a)).trans
    (congrArg (SerreLocalization.actualConnectingHom (smallTorsion T) (smallFunctor T) n) hu.symm)

/-- Naturality of the original finite-module boundary from the actual ordinary
localization square, with no separate support-compatibility hypothesis. -/
theorem connectingHom_naturality (n : ℕ) :
    ((inducedSupportedExactFunctorOfSquare S T V W e).KMap n).comp (connectingHom S n) =
      (connectingHom T n).comp (W.smallKMap (n + 1)) :=
  connectingHom_naturality_of_exactSquare S T V W
    (smallTorsion_map_of_exactSquare S T V W e) e n

end Quillen.FiniteModuleLocalization
