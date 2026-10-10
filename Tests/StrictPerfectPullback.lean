/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.PullbackFunctor
import Quillen.PerfectComplexes.OpenFunctor

/-!
# Consumers of actual strict-perfect arbitrary pullback

The consumers keep the original geometric K-map visible, exercise degree zero,
and use arbitrary affine morphisms without flatness hypotheses. In particular,
the comparison inverse is natural because of the proved original comparison
square, rather than being used to define the pullback map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Tests.StrictPullback

/-- Arbitrary affine morphisms act on genuine bounded finite-locally-free
complexes, including non-flat morphisms. -/
def affineComplexPullback {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    StrictPerfect (Spec R) ⥤ StrictPerfect (Spec S) := strictPullback (Spec.map φ)

/-- The arbitrary affine K-map is the map of the original geometric functor. -/
theorem affineKMap_origin {R S : CommRingCat.{u}} (φ : R ⟶ S) (n : ℕ) :
    strictKPullback (Spec.map φ) n =
      Waldhausen.KMap (strictPullback_waldhausenExact (Spec.map φ)) n := rfl

/-- Pullback exactness concerns the actual ambient short exact sequence. -/
theorem preserves_actual_conflation {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex (StrictPerfect Y))
    (hS : (strictExactStructure Y).conflation S) :
    (strictExactStructure X).conflation (S.map (strictPullback f)) :=
  (strictExactPullback f).map_conflation S hS

/-- The actual pulled chain map is a quasi-isomorphism. -/
theorem preserves_actual_quasiIso {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    {K L : StrictPerfect Y} (s : K ⟶ L) [QuasiIso s.hom] :
    QuasiIso ((strictPullback f).map s).hom :=
  quasiIso_pullback_of_strictPerfect f K.property L.property s.hom

/-- Degree-zero naturality uses the original public comparison homomorphism. -/
theorem original_K0_naturality {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (x : Scheme.K Y 0) :
    strictKPullback f 0 (vectorBundleToStrictKMap Y 0 x) =
      vectorBundleToStrictKMap X 0 (Scheme.pullbackK f 0 x) :=
  DFunLike.congr_fun (vectorBundleToStrictKMap_pullback f 0) x

/-- The original equivalence inverse computes pullback on every strict K0 class. -/
theorem inverse_K0_naturality {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (x : StrictK Y 0) :
    (vectorBundleToStrictKEquiv X 0).symm (strictKPullback f 0 x) =
      Scheme.pullbackK f 0 ((vectorBundleToStrictKEquiv Y 0).symm x) :=
  (DFunLike.congr_fun (vectorBundleToStrictKEquiv_symm_pullback f 0) x).symm

/-- Identity and composition hold on the literal S-construction K-maps. -/
theorem composite_pullback_evaluation {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (x : StrictK Z n) :
    strictKPullback (f ≫ g) n x = strictKPullback f n (strictKPullback g n x) := by
  rw [strictKPullback_comp]
  rfl

/-- Scheme isomorphisms induce mutually inverse actual strict-perfect K-maps. -/
theorem isomorphism_inverse_pullbacks {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) (n : ℕ) :
    (strictKPullback e.hom n).comp (strictKPullback e.inv n) =
      MonoidHom.id (StrictK X n) := by
  rw [← strictKPullback_comp, e.hom_inv_id, strictKPullback_id]

/-- Restricting the full-scheme functor to open immersions recovers the
existing functor map, without changing either definition. -/
theorem existing_open_functor_map {X Y : Scheme.OpenImmersionSchemes.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ) :
    ((StrictKOpenFunctor n).map f).hom = strictKPullback f.unop.hom n :=
  (strictKPullback_eq_restrict f.unop.hom n).symm

/-- On opens, arbitrary strict pullback followed by the original inclusion
agrees with the original locally-perfect restriction square. -/
theorem strict_to_local_open_square {X Y : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (n : ℕ) :
    (perfectKRestrict j n).comp (strictToPerfectKMap Y n) =
      (strictToPerfectKMap X n).comp (strictKPullback j n) := by
  rw [strictKPullback_eq_restrict]
  exact strictToPerfectKMap_restrict j n

/-- Actual inverse-image restriction compatibility holds in degree zero
for every scheme morphism and every target open. -/
theorem inverse_image_open_K0_square {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : StrictK Y 0) :
    strictKRestrict (f ⁻¹ᵁ U).ι 0 (strictKPullback f 0 x) =
      strictKPullback (f ∣_ U) 0 (strictKRestrict U.ι 0 x) :=
  DFunLike.congr_fun (strictKPullback_restrict f U 0) x

/-- The bundled comparison has exactly the original forward component. -/
theorem original_comparison_component (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    ((vectorBundleToStrictNatIso n).hom.app (Opposite.op X)).hom =
      vectorBundleToStrictKMap X n := rfl

end Quillen.Tests.StrictPullback
