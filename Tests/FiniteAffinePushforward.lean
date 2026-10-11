/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.FiniteAffinePushforward

/-! # Original-map finite affine pushforward consumers, including a genuinely nonsurjective finite
  ring homomorphism. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen Quillen.CoherentScheme Quillen.CoherentScheme.FiniteAffine
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Tests.FiniteAffinePushforward
variable {R S T : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
  (φ : R ⟶ S) (hφ : φ.hom.Finite)

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- The source sheaf and actual geometric direct image are unchanged. -/
theorem original_sheaf (M : FiniteTypeSheaves (Spec S)) :
    ((coherentPushforward φ hφ).obj M).obj =
      (Scheme.Modules.pushforward (Spec.map φ)).obj M.obj := rfl

/-- A genuine coherent short exact sequence remains exact under this actual direct image. -/
theorem actual_shortExact (A : ShortComplex (FiniteTypeSheaves (Spec S))) (hA : A.ShortExact) :
    (A.map (coherentPushforward φ hφ)).ShortExact := hA.map_of_exact _

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- The scalar action is exactly restriction along the original ring map. -/
theorem original_scalar (M : FGModuleCat.{u} S) (r : R) (m : M) :
    @SMul.smul R (((moduleRestriction φ hφ).obj M).obj) inferInstance r m =
      φ.hom r • m := rfl

/-- Composition acts on the original public G-class through the original direct images. -/
theorem original_composition (ψ : S ⟶ T) (hψ : ψ.hom.Finite) (n : ℕ) (a : G (Spec T) n) :
    pushforwardG (φ ≫ ψ) (hψ.comp hφ) n a = pushforwardG φ hφ n (pushforwardG ψ hψ n a) :=
  DFunLike.congr_fun (pushforwardG_comp φ hφ ψ hψ n) a

/-- Existing closed pushforward is preserved in every connective degree. -/
theorem original_closed_map [IsClosedImmersion (Spec.map φ)] (n : ℕ) (a : G (Spec S) n) :
    pushforwardG φ hφ n a = ClosedImmersion.General.coherentPushforwardGMap (Spec.map φ) n a :=
  DFunLike.congr_fun (pushforwardG_eq_closed φ hφ n) a

/-- The actual global-section comparison retains the upper-universe public G-group. -/
theorem original_global_sections (n : ℕ) (a : G (Spec S) n) :
    ExactFunctor.smallKMap.{u+1} (ClosedImmersion.Ideal.globalSectionsExact R) n (pushforwardG φ hφ
      n a) =
      ExactFunctor.smallKMap.{u+1} (moduleRestrictionExact φ hφ) n
        (ExactFunctor.smallKMap.{u+1} (ClosedImmersion.Ideal.globalSectionsExact S) n a) :=
  DFunLike.congr_fun (pushforwardG_globalSections φ hφ n) a

/-- Bundling does not change the original finite affine map. -/
theorem original_bundled_map {A B : Quillen.Scheme.NoetherianFiniteRings.{u}}
    (f : A ⟶ B) (n : ℕ) :
    ((Quillen.Scheme.GFiniteAffinePushforwardFunctor n).map f.op).hom =
      pushforwardG f.hom.hom f.hom.property n := rfl

/-- The diagonal R to R×R is finite, so the construction includes nonclosed finite maps. -/
theorem diagonal_finite (R : CommRingCat.{u}) :
    ((RingHom.id R).prod (RingHom.id R)).Finite := by
  change Module.Finite R (R × R)
  infer_instance

/-- For a nontrivial ring the same finite diagonal is genuinely nonsurjective. -/
theorem diagonal_not_surjective (R : CommRingCat.{u}) [Nontrivial R] :
    ¬ Function.Surjective ((RingHom.id R).prod (RingHom.id R)) := by
  intro h
  obtain ⟨r, hr⟩ := h (0, 1)
  have h0 : r = (0 : R) := congrArg Prod.fst hr
  have h1 : r = (1 : R) := congrArg Prod.snd hr
  exact zero_ne_one (h0.symm.trans h1)

end Tests.FiniteAffinePushforward
