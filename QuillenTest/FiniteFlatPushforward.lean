/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToGFinitePushforward

/-! Consumers of finite flat vector-bundle direct image: a two-copy cover,
original sheaf maps, exact sequences, open base change and canonical K-to-G. -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace QuillenTest.FiniteFlatPushforward

open Quillen

/-- The two-copy cover requires no closed-immersion hypothesis. -/
theorem double_cover_preserves_vector_bundles (X : Scheme.{u}) [IsLocallyNoetherian X]
    (M : (X ⨿ X).Modules) [IsFiniteLocallyFree (X ⨿ X) M] :
    IsFiniteLocallyFree X
      ((Scheme.Modules.pushforward (coprod.desc (𝟙 X) (𝟙 X))).obj M) := by
  have : Flat (coprod.desc (𝟙 X) (𝟙 X)) := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (coprodOpenCover.{u, 0} X X)).mpr
    intro i
    cases i with
    | inl i => simpa [coprodOpenCover] using (inferInstance : Flat (𝟙 X))
    | inr i => simpa [coprodOpenCover] using (inferInstance : Flat (𝟙 X))
  exact finiteLocallyFree_pushforward _ M

variable {Z X U : Scheme.{u}}
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

omit [IsLocallyNoetherian Z] in
/-- Every underlying vector-bundle arrow is the original module-sheaf pushforward. -/
theorem original_sheaf_map {M N : FiniteLocallyFree Z} (a : M ⟶ N) :
    ((vectorBundlePushforward f).map a).hom = (Scheme.Modules.pushforward f).map a.hom := rfl

/-- The exact functor transports original vector-bundle conflations. -/
theorem original_conflation (S : ShortComplex (FiniteLocallyFree Z))
    (h : (vectorBundleExactStructure Z).conflation S) :
    (vectorBundleExactStructure X).conflation (S.map (vectorBundlePushforward f)) :=
  (vectorBundlePushforwardExact f).map_conflation S h

/-- Actual inverse-image opens preserve the original pushed-forward K-class. -/
theorem original_open_base_change (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (x : SchemeK Z n) :
    schemeKRestrict j n (schemeKPushforward f n x) =
      schemeKPushforward (pullback.snd f j) n (schemeKRestrict (pullback.fst f j) n x) :=
  congrArg (fun h ↦ h x) (schemeKPushforward_openBaseChange f j n)

/-- The original K-to-G square agrees on every input K-class. -/
theorem original_KToG (n : ℕ) (x : SchemeK Z n) :
    AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap f n
      (schemeKToG Z n x) =
      schemeKToG X n (schemeKPushforward f n x) :=
  congrArg (fun h ↦ h x) (schemeKToG_pushforward f n)

/-- The bundled natural comparison is the original public K-to-G homomorphism. -/
theorem public_comparison_app (Y : AlgebraicGeometry.Scheme.LocallyNoetherianFiniteFlatSchemes.{u})
    (n : ℕ) :
    ((AlgebraicGeometry.Scheme.KToGFiniteFlatPushforward n).app Y).hom =
      AlgebraicGeometry.Scheme.KToG Y.obj.obj n := rfl

end QuillenTest.FiniteFlatPushforward
