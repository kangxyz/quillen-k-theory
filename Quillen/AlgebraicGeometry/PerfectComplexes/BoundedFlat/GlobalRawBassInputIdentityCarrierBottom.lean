/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCarrierProjection
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitSimplex

/-!
# The original Laurent-unit product face in the global identity carrier

The actual five-node global projection path is composed with the original three-node Laurent
identity track. The complete fifteen-node product is reanchored to the unchanged common source.
All native levels retain both independent coordinates and the original Laurent map-id transport.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierBottom
open OriginalUnitSquareSimplex CoefficientPolynomialSpanUnitSimplex

private theorem anchored_family {V W : Model.{u}} {F G : V ⟶ W} {k : ℕ}
    (ρ : F.functor ≅ G.functor) (N : Fin (k + 1) → CommonReferenceNerve.Node G) :
    ModelSimplex.ofIsos F (fun i ↦ (BassH0Merge.anchorNode ρ (N i)).1)
        (fun i ↦ (BassH0Merge.anchorNode ρ (N i)).2) =
      ModelSimplex.ofIsos G (fun i ↦ (N i).1) (fun i ↦ (N i).2) :=
  ModelSimplex.ofIsos_change_reference ρ _ _

variable (X : Scheme.{u})

/-- The original bottom reference is projection followed by the genuine Laurent identity map. -/
abbrev productSource := InputIdentityProjection.source X ≫ unitSourceMap (laurent.obj X)

/-- Both original split units determine the exact common reference transport. -/
def sourceIso : (InputIdentityNodes.source X).functor ≅ (productSource X).functor :=
  InputIdentityNodes.sourceToProjection X ≪≫
    (isoWhiskerLeft (InputIdentityProjection.source X).functor
      (unitFirst (laurent.obj X) ≪≫ unitSecond (laurent.obj X))).symm

/-- Each original product vertex retains its entire actual product reference isomorphism. -/
def productNodes (i : Fin 15) : CommonReferenceNerve.Node (productSource X) :=
  ⟨CommonReferenceProduct.vertices (fun j ↦ (InputIdentityProjection.nodes X j).1)
      (identityVertices (laurent.obj X)) i,
    CommonReferenceProduct.references (InputIdentityProjection.source X)
      (fun j ↦ (InputIdentityProjection.nodes X j).1)
      (fun j ↦ (InputIdentityProjection.nodes X j).2)
      (unitSourceMap (laurent.obj X)) (identityVertices (laurent.obj X))
      (identityReferences (laurent.obj X)) i⟩

/-- All product nodes live in the same complete reference carrier as the other identity faces. -/
def nodes (i : Fin 15) : InputIdentityNodes.Node X :=
  BassH0Merge.anchorNode (sourceIso X) (productNodes X i)

/-- The entire reanchored simplex is the original independent-parameter product diagram. -/
theorem product_family :
    ModelSimplex.ofIsos (InputIdentityNodes.source X) (fun i ↦ (nodes X i).1)
      (fun i ↦ (nodes X i).2) =
        CommonReferenceProduct.simplex (InputIdentityProjection.source X)
          (fun j ↦ (InputIdentityProjection.nodes X j).1)
          (fun j ↦ (InputIdentityProjection.nodes X j).2)
          (unitSourceMap (laurent.obj X)) (identityVertices (laurent.obj X))
          (identityReferences (laurent.obj X)) :=
  anchored_family (sourceIso X) (productNodes X)

/-- Projection height and original Laurent identity time retain their independent product clocks. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The complete original Laurent-unit face, with all fifteen actual dependent nodes. -/
def face : C(unitInterval × unitInterval, InputIdentityCarrierCharts.Carrier X) :=
  (CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)).comp parameter.{u}

/-- The entire native bottom is the actual Laurent identity after the unchanged Bass comparison. -/
theorem face_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X) (face X)
        n ((r, t), x) =
      (Homotopy.precomp (comparison X) (InputIdentity.laurentHomotopy X)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (InputIdentityNodes.source X)
    (face X) (nodes X) (r, t) (parameter.{u} (r, t)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, product_family]
  refine (CommonReferenceProduct.prespectrum_comp (InputIdentityProjection.source X)
    (fun j ↦ (InputIdentityProjection.nodes X j).1)
    (fun j ↦ (InputIdentityProjection.nodes X j).2)
    (unitSourceMap (laurent.obj X)) (identityVertices (laurent.obj X))
    (identityReferences (laurent.obj X)) n x (InputIdentityProjection.parameter t)
    (binaryPath (k := 2) 0 1 2 r)).trans ?_
  refine (identity_native (laurent.obj X) n r _).trans ?_
  exact congrArg (fun y ↦ (InputIdentity.laurentHomotopy X).level n (r, y))
    (InputIdentityProjection.native X n t x)

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierBottom
