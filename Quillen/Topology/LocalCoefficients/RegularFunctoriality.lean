/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.RegularChains

/-!
# Functoriality of regular chains along the original continuous map

The coefficient morphism maps actual path classes. Its composite with the
existing pushforward is the genuine regular chain map. An explicit equality
of basepoints is retained, so a commuting covering square does not have to
identify its corner points definitionally.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Apply the original continuous map to every basis path in the regular system. -/
def regularMap (f : C(X, Y)) (b : X) : regular b ⟶ pullback f (regular (f b)) where
  app x := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (fun q ↦
    (FundamentalGroupoid.map f).map q))
  naturality x y q := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro r z
    simp only [regular, pullback, Functor.comp_obj, FundamentalGroupoid.map_map,
      ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Functor.comp_map]
    exact congrArg (fun q ↦ Finsupp.single q z) ((FundamentalGroupoid.map f).map_comp r q)

/-- The coefficient map retains the actual image of the path class. -/
theorem regularMap_single (f : C(X, Y)) (b : X)
    {x : X} (q : Path.Homotopic.Quotient b x) (z : ℤ) :
    (regularMap f b).app (FundamentalGroupoid.mk x) (regularSingle b q z) =
      regularSingle (f b) (q.map f) z := by
  exact Finsupp.mapDomain_single

/-- The regular coefficient map with a specified equality at the target basepoint. -/
def regularMapTo (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    regular b ⟶ pullback f (regular b') :=
  regularMap f b ≫ eqToHom (congrArg (fun y ↦ pullback f (regular y)) hb.symm)

/-- A regular basis simplex under the original map, with its explicit basepoint cast. -/
def mapRegularSimplex (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    {n : SimplexCategory} (s : RegularSimplex b n) : RegularSimplex b' n :=
  ⟨f.comp s.1, (s.2.map f).cast hb rfl⟩

/-- The degreewise composite of the coefficient conversion and original pushforward. -/
def regularPushforwardModuleMap (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (n : SimplexCategory) : chainModule (regular b) n ⟶ chainModule (regular b') n :=
  coefficientModuleMap (regularMapTo f b b' hb) n ≫ pushforwardModuleMap f (regular b') n

/-- The actual coefficient-plus-spatial chain map on every regular generator. -/
@[simp]
theorem regularPushforwardModuleMap_generator (f : C(X, Y)) (b : X) (b' : Y)
    (hb : b' = f b) {n : SimplexCategory} (s : RegularSimplex b n) (z : ℤ) :
    regularPushforwardModuleMap f b b' hb n (regularChainGenerator b s z) =
      regularChainGenerator b' (mapRegularSimplex f b b' hb s) z := by
  subst b'
  change (chainInclusion (regular b) s.1 ≫
    regularPushforwardModuleMap f b (f b) rfl n) (regularSingle b s.2 z) = _
  simp only [regularPushforwardModuleMap, regularMapTo, eqToHom_refl, Category.comp_id,
    chainInclusion_coefficientModuleMap_assoc, pullback_fiber,
    chainInclusion_pushforwardModuleMap, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, regularChainGenerator, mapRegularSimplex, ContinuousMap.comp_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl]
  change chainInclusion (regular (f b)) (f.comp s.1)
    ((regularMap f b).app _ (regularSingle b s.2 z)) = _
  rw [regularMap_single]

/-- The actual simplicial map induced by a continuous map and explicit basepoint equality. -/
def regularPushforwardSimplicialMap (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    simplicialModule (regular b) ⟶ simplicialModule (regular b') :=
  coefficientSimplicialMap (regularMapTo f b b' hb) ≫
    pushforwardSimplicialMap f (regular b')

/-- The regular chain map is built from the already-defined original pushforward. -/
def regularPushforwardChainMap (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    singularChainComplex (regular b) ⟶ singularChainComplex (regular b') :=
  coefficientChainMap (regularMapTo f b b' hb) ≫ pushforwardChainMap f (regular b')

/-- Applying alternating faces gives precisely the displayed original-map composite. -/
theorem regularPushforwardChainMap_eq (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    regularPushforwardChainMap f b b' hb =
      (AlgebraicTopology.alternatingFaceMapComplex _).map
        (regularPushforwardSimplicialMap f b b' hb) := by
  simp [regularPushforwardChainMap, regularPushforwardSimplicialMap,
    coefficientChainMap, pushforwardChainMap]

/-- Ordinary pushforward retains both the original map and the integral coefficient. -/
@[simp]
theorem pushforwardModuleMap_integralGenerator (f : C(X, Y)) {n : SimplexCategory}
    (σ : SingularSimplex X n) (z : ℤ) :
    pushforwardModuleMap f (constant Y integralCoefficients) n
        (integralChainGenerator σ z) = integralChainGenerator (f.comp σ) z := by
  change (chainInclusion (pullback f (constant Y integralCoefficients)) σ ≫
    pushforwardModuleMap f (constant Y integralCoefficients) n) (ULift.up z) = _
  rw [chainInclusion_pushforwardModuleMap]
  rfl

/-- Ordinary-chain reindexing respects the original continuous map at the simplicial level. -/
@[reassoc]
theorem constantSimplicialIso_naturality (f : C(X, Y)) (V : ModuleCat.{u} ℤ) :
    pushforwardSimplicialMap f (constant Y V) ≫ (constantSimplicialIso V).hom =
      (constantSimplicialIso V).hom ≫
        Functor.whiskerRight (TopCat.toSSet.map (TopCat.ofHom f)) (sigmaConst.obj V) := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  simp [pushforwardSimplicialMap, constantSimplicialIso, constantModuleIso,
    pushforwardModuleMap, chainInclusion, sigmaConst, Sigma.map', constant]
  rfl

/-- The standard comparison retains mathlib's actual singular-chain map of the original map. -/
@[reassoc]
theorem constantChainComplexIso_naturality (f : C(X, Y)) (V : ModuleCat.{u} ℤ) :
    pushforwardChainMap f (constant Y V) ≫ (constantChainComplexIso V).hom =
      (constantChainComplexIso V).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map
          (TopCat.ofHom f) := by
  have h := congrArg (fun η ↦ (AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{u} ℤ)).map η) (constantSimplicialIso_naturality f V)
  simpa [pushforwardChainMap, constantChainComplexIso,
    AlgebraicTopology.singularChainComplexFunctor, SSet.chainComplexFunctor] using h

end Quillen.LocalCoefficients
