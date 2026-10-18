/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.IdentityAutomorphism
public import Quillen.KTheory.LowDegreeScalarAction.ExactNaturality
public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.Aglib.CategoryTheory.Linear.ScalarAutomorphism
public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjective
public import Aglib.Algebra.Category.FGModuleCat.Basic

/-!
# Actual scalar units in the original low-degree K-operations

The canonical map to the center of a linear category, followed by the existing
units-to-automorphisms equivalence, supplies the actual scalar natural
automorphism of the identity. Its normalized Q self-homotopy defines the
existing K0-to-K1 and K1-to-K2 operations. Both source and unit laws are bundled
as homomorphisms, and the representative equations retain the original cubes
and degree-zero normalization inverse.

The ordinary linear-functor square preserves the same scalar coefficient.
For a chosen SmallModel, full faithfulness of its original realization functor
lifts this same natural automorphism; no additional linear structure on that
model is assumed. The concrete consumers are finite projectives over a
commutative ring and finite modules over a noetherian commutative ring,
including fields, together with the original upper finite-module model.

The identity-automorphism naturality theorem gives the original
exact-functor K-map squares, including the actual mapped-model small K-maps,
from ordinary linearity. Ordered-symbol or product normalization and boundary
compatibility remain separate obligations.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe w u v u₁ v₁ u₂ v₂ s
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open scoped ZeroObject Topology

namespace Quillen.LowDegreeScalarAction.ScalarUnit

section MappedModelAutomorphism
variable (R : Type w) [Ring R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D] [Linear R D]
  [EssentiallySmall.{s} C] [EssentiallySmall.{s} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The original mapped-model functor preserves the lifted scalar components. -/
theorem smallModelScalarNatAut_map (F : ExactFunctor EC ED) [F.toFunctor.Linear R]
    (r : Rˣ) (X : SmallModel.{s} C) :
    F.smallModel.{s}.toFunctor.map ((smallModelScalarNatAut R C r).hom.app X) =
      (smallModelScalarNatAut R D r).hom.app (F.smallModel.{s}.toFunctor.obj X) := by
  change (equivSmallModel.{s} D).functor.map
    (F.toFunctor.map ((equivSmallModel.{s} C).inverse.map
      ((smallModelScalarNatAut R C r).hom.app X))) =
    (smallModelScalarNatAut R D r).hom.app
      ((equivSmallModel.{s} D).functor.obj
        (F.toFunctor.obj ((equivSmallModel.{s} C).inverse.obj X)))
  rw [smallModelScalarNatAut_map_hom]
  have h := scalarNatAut_map R F.toFunctor r ((equivSmallModel.{s} C).inverse.obj X)
  simp only [scalarNatAut_hom_app] at h
  rw [h]
  simpa only [scalarNatAut_hom_app] using
    smallModelScalarNatAut_functor_map_hom R D r
      (F.toFunctor.obj ((equivSmallModel.{s} C).inverse.obj X))

end MappedModelAutomorphism

section Operations
variable {C : Type (max u v)} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (R : Type w) [Ring R] (E : ExactStructure C)

/-- The original K-zero operation for an actual multiplicative family of unit automorphisms. -/
def kZeroActionOf (a : Rˣ →* Aut (𝟭 C)) : Rˣ →* (E.K 0 →* E.K 1) where
  toFun r := IdentityAutomorphism.kZeroActionHom E (a r)
  map_one' := by
    ext x
    change IdentityAutomorphism.kZeroNatAut E x (a 1) = 1
    simp only [map_one]
  map_mul' r t := by
    ext x
    change IdentityAutomorphism.kZeroNatAut E x (a (r * t)) =
      IdentityAutomorphism.kZeroNatAut E x (a r) * IdentityAutomorphism.kZeroNatAut E x (a t)
    simp only [map_mul]

/-- The original K-one operation for an actual multiplicative family of unit automorphisms. -/
def kOneActionOf (a : Rˣ →* Aut (𝟭 C)) : Rˣ →* (E.K 1 →* E.K 2) where
  toFun r := IdentityAutomorphism.kOneAction E (a r)
  map_one' := by
    ext x
    change IdentityAutomorphism.kOneNatAut E x (a 1) = 1
    simp only [map_one]
  map_mul' r t := by
    ext x
    change IdentityAutomorphism.kOneNatAut E x (a (r * t)) =
      IdentityAutomorphism.kOneNatAut E x (a r) * IdentityAutomorphism.kOneNatAut E x (a t)
    simp only [map_mul]

variable [Linear R C]

/-- The original degree-(0,1) operation, a homomorphism in the unit and the K-zero class. -/
def kZeroAction : Rˣ →* (E.K 0 →* E.K 1) := kZeroActionOf R E (scalarNatAut R C)

/-- The original degree-(1,1) operation, a homomorphism in the unit and the K-one class. -/
def kOneAction : Rˣ →* (E.K 1 →* E.K 2) := kOneActionOf R E (scalarNatAut R C)

/-- The scalar operation is the existing identity-automorphism operation on the same class. -/
@[simp] theorem kZeroAction_apply (r : Rˣ) (a : E.K 0) :
    kZeroAction R E r a = IdentityAutomorphism.kZeroAction E (scalarNatAut R C r) a := rfl

/-- The scalar operation retains the existing identity-automorphism K-one operation. -/
@[simp] theorem kOneAction_apply (r : Rˣ) (a : E.K 1) :
    kOneAction R E r a = IdentityAutomorphism.kOneAction E (scalarNatAut R C r) a := rfl

/-- The degree-(0,1) operation preserves the original source product. -/
theorem kZeroAction_source_mul (r : Rˣ) (a b : E.K 0) :
    kZeroAction R E r (a * b) = kZeroAction R E r a * kZeroAction R E r b :=
  (kZeroAction R E r).map_mul a b

/-- The degree-(1,1) operation preserves the original source product. -/
theorem kOneAction_source_mul (r : Rˣ) (a b : E.K 1) :
    kOneAction R E r (a * b) = kOneAction R E r a * kOneAction R E r b :=
  (kOneAction R E r).map_mul a b

/-- Multiplication of the actual scalar units adds their degree-(0,1) operations. -/
theorem kZeroAction_unit_mul (r t : Rˣ) (a : E.K 0) :
    kZeroAction R E (r * t) a = kZeroAction R E r a * kZeroAction R E t a :=
  DFunLike.congr_fun ((kZeroAction R E).map_mul r t) a

/-- Multiplication of the actual scalar units adds their degree-(1,1) operations. -/
theorem kOneAction_unit_mul (r t : Rˣ) (a : E.K 1) :
    kOneAction R E (r * t) a = kOneAction R E r a * kOneAction R E t a :=
  DFunLike.congr_fun ((kOneAction R E).map_mul r t) a

/-- The identity K-zero input has identity output. -/
theorem kZeroAction_source_one (r : Rˣ) : kZeroAction R E r 1 = 1 :=
  (kZeroAction R E r).map_one

/-- The identity K-one input has identity output. -/
theorem kOneAction_source_one (r : Rˣ) : kOneAction R E r 1 = 1 :=
  (kOneAction R E r).map_one

/-- The identity scalar unit has zero degree-(0,1) operation. -/
theorem kZeroAction_unit_one (a : E.K 0) : kZeroAction R E 1 a = 1 :=
  DFunLike.congr_fun (kZeroAction R E).map_one a

/-- The identity scalar unit has zero degree-(1,1) operation. -/
theorem kOneAction_unit_one (a : E.K 1) : kOneAction R E 1 a = 1 :=
  DFunLike.congr_fun (kOneAction R E).map_one a

/-- The degree-(0,1) representative is the original normalized track-first cube. -/
theorem kZeroAction_cube (r : Rˣ) (p : GenLoop (Fin 1) E.KSpace E.kBasepoint) :
    kZeroAction R E r ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 0 p
        (IdentityTrack.track (IdentityAutomorphism.homotopy E (scalarNatAut R C r)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E (scalarNatAut R C r)) 0 p)⟧ : E.K 1) :=
  IdentityAutomorphism.kZeroAction_cube E (scalarNatAut R C r) p

/-- The degree-(1,1) representative is the original normalized track-first cube. -/
theorem kOneAction_cube (r : Rˣ) (p : GenLoop (Fin 2) E.KSpace E.kBasepoint) :
    kOneAction R E r ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 1 p
        (IdentityTrack.track (IdentityAutomorphism.homotopy E (scalarNatAut R C r)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E (scalarNatAut R C r)) 1 p)⟧ : E.K 2) :=
  IdentityAutomorphism.kOneAction_cube E (scalarNatAut R C r) p

/-- Every track time is the actual normalized-Q homotopy of the scalar automorphism. -/
theorem track_apply (r : Rˣ) (m : ℕ)
    (p : GenLoop (Fin (m + 1)) E.KSpace E.kBasepoint)
    (t : unitInterval) (z : Fin (m + 1) → unitInterval) :
    IdentityTrack.track (IdentityAutomorphism.homotopy E (scalarNatAut R C r)).toHomotopy
      (IdentityAutomorphism.homotopy_fixed E (scalarNatAut R C r)) m p t z =
      classifyingSpaceNaturalTransformationHomotopy
        (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E)
          (scalarNatAut R C r)).hom (t, p z) :=
  IdentityAutomorphism.track_apply E (scalarNatAut R C r) m p t z

/-- The degree-zero comparison retains the original inverse in loop normalization. -/
theorem kZeroAction_normalization (r : Rˣ) (p : GenLoop (Fin 1) E.KSpace E.kBasepoint) :
    kZeroAction R E r ⟦p⟧ =
      (loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
        ⟦(IdentityTrack.track (IdentityAutomorphism.homotopy E (scalarNatAut R C r)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E (scalarNatAut R C r)) 0 p).map
            (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧)⁻¹ :=
  IdentityAutomorphism.kZeroAction_normalization E (scalarNatAut R C r) p

variable {E} {D : Type (max u v)} [Category.{v} D] [Preadditive D]
  [HasFiniteBiproducts D] [Linear R D] {ED : ExactStructure D}

/-- Ordinary linearity gives scalar naturality with the original exact-functor K-maps. -/
theorem kZeroAction_natural (F : ExactFunctor E ED) [F.toFunctor.Linear R]
    (r : Rˣ) (a : E.K 0) :
    F.KMap 1 (kZeroAction R E r a) = kZeroAction R ED r (F.KMap 0 a) :=
  ExactNaturality.kZeroAction_natural F (scalarNatAut R C r) (scalarNatAut R D r)
    (scalarNatAut_map R F.toFunctor r) a

/-- The K-one scalar operation retains the original degree-one and degree-two K-maps. -/
theorem kOneAction_natural (F : ExactFunctor E ED) [F.toFunctor.Linear R]
    (r : Rˣ) (a : E.K 1) :
    F.KMap 2 (kOneAction R E r a) = kOneAction R ED r (F.KMap 1 a) :=
  ExactNaturality.kOneAction_natural F (scalarNatAut R C r) (scalarNatAut R D r)
    (scalarNatAut_map R F.toFunctor r) a

end Operations

section SmallModelOperations
variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [Linear R C] [EssentiallySmall.{s} C] (E : ExactStructure C)

/-- The actual chosen-model K-zero operation, without assuming a new linear model structure. -/
def smallModelKZeroAction : Rˣ →* (E.SmallK.{s} 0 →* E.SmallK.{s} 1) :=
  kZeroActionOf R E.smallModel.{s} (smallModelScalarNatAut R C)

/-- The actual chosen-model K-one operation with its original scalar automorphism lifted. -/
def smallModelKOneAction : Rˣ →* (E.SmallK.{s} 1 →* E.SmallK.{s} 2) :=
  kOneActionOf R E.smallModel.{s} (smallModelScalarNatAut R C)

/-- The chosen-model operation is the original operation of the lifted scalar automorphism. -/
@[simp] theorem smallModelKZeroAction_apply (r : Rˣ) (a : E.SmallK.{s} 0) :
    smallModelKZeroAction R E r a =
      IdentityAutomorphism.kZeroAction E.smallModel (smallModelScalarNatAut R C r) a := rfl

/-- The chosen-model operation retains the original K-one operation of the lifted automorphism. -/
@[simp] theorem smallModelKOneAction_apply (r : Rˣ) (a : E.SmallK.{s} 1) :
    smallModelKOneAction R E r a =
      IdentityAutomorphism.kOneAction E.smallModel (smallModelScalarNatAut R C r) a := rfl

/-- The chosen-model K-zero representative retains the original normalized track-first cube. -/
theorem smallModelKZeroAction_cube (r : Rˣ)
    (p : GenLoop (Fin 1) E.smallModel.{s}.KSpace E.smallModel.{s}.kBasepoint) :
    smallModelKZeroAction R E r ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 0 p
        (IdentityTrack.track (IdentityAutomorphism.homotopy E.smallModel
          (smallModelScalarNatAut R C r)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E.smallModel (smallModelScalarNatAut R C r))
          0 p)⟧ : E.SmallK.{s} 1) :=
  IdentityAutomorphism.kZeroAction_cube E.smallModel (smallModelScalarNatAut R C r) p

/-- The chosen-model K-one representative retains the original normalized track-first cube. -/
theorem smallModelKOneAction_cube (r : Rˣ)
    (p : GenLoop (Fin 2) E.smallModel.{s}.KSpace E.smallModel.{s}.kBasepoint) :
    smallModelKOneAction R E r ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 1 p
        (IdentityTrack.track (IdentityAutomorphism.homotopy E.smallModel
          (smallModelScalarNatAut R C r)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E.smallModel (smallModelScalarNatAut R C r))
          1 p)⟧ : E.SmallK.{s} 2) :=
  IdentityAutomorphism.kOneAction_cube E.smallModel (smallModelScalarNatAut R C r) p

/-- The chosen-model normalization retains the original degree-zero inverse. -/
theorem smallModelKZeroAction_normalization (r : Rˣ)
    (p : GenLoop (Fin 1) E.smallModel.{s}.KSpace E.smallModel.{s}.kBasepoint) :
    smallModelKZeroAction R E r ⟦p⟧ =
      (loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
        ⟦(IdentityTrack.track (IdentityAutomorphism.homotopy E.smallModel
          (smallModelScalarNatAut R C r)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E.smallModel (smallModelScalarNatAut R C r))
          0 p).map (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧)⁻¹ :=
  IdentityAutomorphism.kZeroAction_normalization E.smallModel (smallModelScalarNatAut R C r) p

variable {E} {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D]
  [Linear R D] [EssentiallySmall.{s} D] {ED : ExactStructure D}

/-- Chosen-model scalar naturality uses the original small K-map in both degrees. -/
theorem smallModelKZeroAction_natural (F : ExactFunctor E ED) [F.toFunctor.Linear R]
    (r : Rˣ) (a : E.SmallK.{s} 0) :
    F.smallKMap.{s} 1 (smallModelKZeroAction R E r a) =
      smallModelKZeroAction R ED r (F.smallKMap.{s} 0 a) :=
  ExactNaturality.kZeroAction_natural.{s, s} F.smallModel.{s}
    (smallModelScalarNatAut R C r) (smallModelScalarNatAut R D r)
    (smallModelScalarNatAut_map R F r) a

/-- Chosen-model K-one scalar naturality needs no linear structure on either model. -/
theorem smallModelKOneAction_natural (F : ExactFunctor E ED) [F.toFunctor.Linear R]
    (r : Rˣ) (a : E.SmallK.{s} 1) :
    F.smallKMap.{s} 2 (smallModelKOneAction R E r a) =
      smallModelKOneAction R ED r (F.smallKMap.{s} 1 a) :=
  ExactNaturality.kOneAction_natural.{s, s} F.smallModel.{s}
    (smallModelScalarNatAut R C r) (smallModelScalarNatAut R D r)
    (smallModelScalarNatAut_map R F r) a

end SmallModelOperations

section Consumers
universe r
variable (R : Type r) [CommRing R]

/-- On actual finite modules the component is the same ordinary scalar multiplication. -/
theorem finiteModule_scalarNatAut_apply (a : Rˣ) (M : FGModuleCat.{r} R) (x : M) :
    ((scalarNatAut R (FGModuleCat.{r} R) a).hom.app M).hom x = (a : R) • x := rfl

/-- On actual finite projectives the component is the same ordinary scalar multiplication. -/
theorem finiteProjective_scalarNatAut_apply (a : Rˣ)
    (M : FiniteProjectiveModule.Category.{r, r} R) (x : M.obj) :
    ((scalarNatAut R (FiniteProjectiveModule.Category.{r, r} R) a).hom.app M).hom x =
      (a : R) • x := rfl

/-- The original K-zero scalar operation on actual finite projective modules. -/
def finiteProjectiveKZeroAction : Rˣ →*
    ((FiniteProjectiveModule.exactStructure.{r, r} R).K 0 →*
      (FiniteProjectiveModule.exactStructure.{r, r} R).K 1) :=
  kZeroAction.{r, r + 1, r} R (FiniteProjectiveModule.exactStructure.{r, r} R)

/-- The original K-one scalar operation on actual finite projective modules. -/
def finiteProjectiveKOneAction : Rˣ →*
    ((FiniteProjectiveModule.exactStructure.{r, r} R).K 1 →*
      (FiniteProjectiveModule.exactStructure.{r, r} R).K 2) :=
  kOneAction.{r, r + 1, r} R (FiniteProjectiveModule.exactStructure.{r, r} R)

variable [IsNoetherianRing R]

/-- The original K-zero scalar operation on finite modules over a noetherian commutative ring. -/
def finiteModuleKZeroAction : Rˣ →*
    ((ModuleCat.finiteModuleExactStructure.{r, r} R).K 0 →*
      (ModuleCat.finiteModuleExactStructure.{r, r} R).K 1) :=
  kZeroAction.{r, r + 1, r} R (ModuleCat.finiteModuleExactStructure.{r, r} R)

/-- The original K-one scalar operation on finite modules over a noetherian commutative ring. -/
def finiteModuleKOneAction : Rˣ →*
    ((ModuleCat.finiteModuleExactStructure.{r, r} R).K 1 →*
      (ModuleCat.finiteModuleExactStructure.{r, r} R).K 2) :=
  kOneAction.{r, r + 1, r} R (ModuleCat.finiteModuleExactStructure.{r, r} R)

/-- The scalar operation on the same finite-module category in its chosen upper model. -/
def upperFiniteModuleKZeroAction : Rˣ →*
    ((ModuleCat.finiteModuleExactStructure.{r, r} R).SmallK.{r + 1} 0 →*
      (ModuleCat.finiteModuleExactStructure.{r, r} R).SmallK.{r + 1} 1) :=
  smallModelKZeroAction.{r, r + 1, r, r + 1} R (ModuleCat.finiteModuleExactStructure.{r, r} R)

/-- The K-one scalar operation on that actual upper finite-module model. -/
def upperFiniteModuleKOneAction : Rˣ →*
    ((ModuleCat.finiteModuleExactStructure.{r, r} R).SmallK.{r + 1} 1 →*
      (ModuleCat.finiteModuleExactStructure.{r, r} R).SmallK.{r + 1} 2) :=
  smallModelKOneAction.{r, r + 1, r, r + 1} R (ModuleCat.finiteModuleExactStructure.{r, r} R)

end Consumers

end Quillen.LowDegreeScalarAction.ScalarUnit
