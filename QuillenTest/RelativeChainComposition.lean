/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.LocalCoefficients.RelativeComposition

/-!
# Consumers of actual relative coefficient and composition maps

The identity relative map and relative coefficient comparisons are invertible.
Composition preserves quasi-isomorphisms of the original pair maps, including
the necessary coefficient correction. Naturality identifies the relative spatial
map for isomorphic target coefficient systems by an exact conjugation formula.
-/

noncomputable section

open CategoryTheory Quillen.LocalCoefficients

universe u

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example (U : Set X) (A : System.{u, u} X) :
    IsIso (relativePushforwardChainMap (ContinuousMap.id X) U U (fun _ hx ↦ hx) A) := by
  rw [relativePushforwardChainMap_id]
  infer_instance

example (f : C(X, Y)) (g : C(Y, Z)) (U : Set X) (V : Set Y) (W : Set Z)
    (hf : Set.MapsTo f U V) (hg : Set.MapsTo g V W) (A : System.{u, u} Z)
    [QuasiIso (relativePushforwardChainMap f U V hf (pullback g A))]
    [QuasiIso (relativePushforwardChainMap g V W hg A)] :
    QuasiIso (relativePushforwardChainMap (g.comp f) U W (fun _ hx ↦ hg (hf hx)) A) := by
  rw [relativePushforwardChainMap_comp f g U V W hf hg A]
  infer_instance

example (f : C(X, Y)) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
    {A B : System.{u, u} Y} (e : A ≅ B) :
    relativePushforwardChainMap f U V h A =
      relativeCoefficientChainMap U (pullbackMap f e.hom) ≫
        relativePushforwardChainMap f U V h B ≫
          (relativeCoefficientChainIso V e).inv := by
  rw [← Category.assoc, relativePushforwardChainMap_coefficient_naturality,
    Category.assoc]
  change _ = relativePushforwardChainMap f U V h A ≫
    (relativeCoefficientChainIso V e).hom ≫ (relativeCoefficientChainIso V e).inv
  rw [Iso.hom_inv_id, Category.comp_id]
