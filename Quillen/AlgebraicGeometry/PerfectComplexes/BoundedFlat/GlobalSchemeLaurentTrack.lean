/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentScalar
public import Quillen.KTheory.Bass.GeometricSeedCospan
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Units
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismSquare

/-!
# The original Laurent unit track on all scheme sections

The forward coordinate is pulled back by the actual second product projection.
Every scheme morphism preserves it, so the original global section identity
unit supplies a whole natural realization track. This instantiates the finite
geometric seed cospan without a track or unit-square hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalSchemeLaurentTrack
open GlobalSectionChangeIndex GeometricSeedCospan
open GeometricSquareInterchange SquareConeStrength

/-- The original global section Model, realized as a strict diagram of spectra. -/
def diagram : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u+1} :=
  globalModel ⋙ prespectrumFunctor

/-- The original forward Laurent coordinate on the actual product with any scheme. -/
def laurentScalar (X : Scheme.{u}ᵒᵖ) : (Γ((laurent.op.obj X).unop, ⊤))ˣ :=
  Units.map (pullback.snd (toIntegerBase X.unop)
    (laurentProjection (.of (ULift.{u} ℤ)))).appTop.hom.toMonoidHom
      (laurentGlobalUnit (.of (ULift.{u} ℤ)))

/-- Every original scheme map keeps the same forward coordinate under actual pullback. -/
theorem laurentScalar_map {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Units.map (laurent.op.map f).unop.appTop.hom.toMonoidHom (laurentScalar X) =
      laurentScalar Y := by
  apply Units.ext
  have h : laurent.map f.unop ≫
      pullback.snd (toIntegerBase X.unop) (laurentProjection (.of (ULift.{u} ℤ))) =
      pullback.snd (toIntegerBase Y.unop) (laurentProjection (.of (ULift.{u} ℤ))) := by
    simp [laurent, baseProductFunctor]
  have hs := congrArg (fun g => g.appTop) h
  rw [Scheme.Hom.comp_appTop] at hs
  exact ConcreteCategory.congr_hom hs (↑(laurentGlobalUnit (.of (ULift.{u} ℤ))))

/-- The original evaluation-lifted scalar identity unit on the Laurent global section Model. -/
def unit (X : Scheme.{u}ᵒᵖ) :
    𝟭 (globalModel.obj (laurent.op.obj X)) ≅ 𝟭 (globalModel.obj (laurent.op.obj X)) :=
  globalUnit (laurent.op.obj X) (laurentScalar X)

/-- Actual global section reindexing preserves the same identity unit on all schemes. -/
theorem unit_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Preserves (globalModel.map (laurent.op.map f)).functor (unit X) (unit Y) :=
  globalUnit_reindex_of_eq (laurent.op.map f) (laurentScalar X) (laurentScalar Y)
    (laurentScalar_map f)

/-- Realize the original scalar unit along the unchanged Laurent projection Model map. -/
def homotopy (X : Scheme.{u}ᵒᵖ) :
    Homotopy (diagram.map (coefficient.app X)) (diagram.map (coefficient.app X)) :=
  prespectrumIsoHomotopy (globalModel.map (coefficient.app X))
    (onFunctor (globalModel.map (coefficient.app X)).functor (unit X))

/-- Every original unit-track time commutes with every actual scheme morphism. -/
theorem homotopy_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (r : unitInterval) (x : (diagram.obj X).space n) :
    (diagram.map (laurent.op.map f)).map n ((homotopy X).level n (r,x)) =
      (homotopy Y).level n (r, (diagram.map f).map n x) := by
  have h : globalModel.map (coefficient.app X) ≫ globalModel.map (laurent.op.map f) =
      globalModel.map f ≫ globalModel.map (coefficient.app Y) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg globalModel.map (coefficient.naturality f).symm
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg Model.Hom.functor h))
      (unit X) (unit Y) (unit_naturality f).whisker) n r x

/-- The actual global-unit induced Bass track satisfies the original whole-unit square. -/
theorem wholeUnitSquare (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (bassTrack diagram homotopy homotopy_naturality X).at r ≫
        (eta (laurentProjection (.of (ULift.{u} ℤ))) diagram).hom.app X =
      (strictDiagramMapHomotopy (sourceTrack diagram homotopy)
        (sourceTrack_naturality diagram homotopy homotopy_naturality) squareFunctor X).at r :=
  GeometricSeedCospan.wholeUnitSquare diagram homotopy homotopy_naturality X r

/-- The finite original global-unit seed cospan, with no supplied track or unit compatibility. -/
theorem seed_cospan (X : Scheme.{u}ᵒᵖ) :
    (WholeSeedCospan.seed
      (geometricSquare ((strictDiagramFunctor squareFunctor).obj diagram))
      (bassTrack diagram homotopy homotopy_naturality)
      (bassTrack_naturality diagram homotopy homotopy_naturality)).app X ≫
        parameterLoopingMap ((chiGeom diagram).app X) =
      (((strictDiagramFunctor squareFunctor).map
        (WholeSeedCospan.seed (geometricSquare diagram) (sourceTrack diagram homotopy)
          (sourceTrack_naturality diagram homotopy homotopy_naturality))).app X) ≫
        LoopStrength.strength squareFunctor
          (mappingConeDiagram (comparison (geometricSquare diagram))) X :=
  GeometricSeedCospan.seed_cospan diagram homotopy homotopy_naturality X

end Quillen.PerfectComplexes.GlobalSchemeLaurentTrack
