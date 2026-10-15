/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ClosedPushforward
public import Quillen.AlgebraicGeometry.Scheme.ClosedGTheory

/-!
# Closed pushforward functoriality regression statements

Records identity, composition, open base change, and inverse laws for the public
closed pushforward maps on G-theory. The bundled functor statement identifies its
composite map with the original pushforwards in their covariant order.
-/

@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
universe u
namespace QuillenTest.ClosedPushforwardFunctoriality

open Quillen
open AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion

/-- Identity on the original public closed G-map, with its inferred source noetherianity. -/
theorem original_id (X : AlgebraicGeometry.Scheme.{u}) [IsNoetherian X] (n : ℕ) :
    Scheme.Closed.pushforwardG (𝟙 X) n = MonoidHom.id (Scheme.G X n) :=
  coherentPushforwardGMap_id X n

/-- The established public maps compose, including their independently derived source instances. -/
theorem original_comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion f] [IsClosedImmersion g] (n : ℕ) :
    Scheme.Closed.pushforwardG (f ≫ g) n =
      (Scheme.Closed.pushforwardG g n).comp (Scheme.Closed.pushforwardG f n) :=
  coherentPushforwardGMap_comp f g n

/-- Original open base change is compatible with a composite of actual closed pushforwards. -/
theorem composite_open_base_change {X Y Z V : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsLocallyNoetherian V] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] (a : V ⟶ Z) [IsOpenImmersion a] (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.Coherent.restrictionGMap a n).comp
      ((coherentPushforwardGMap g n).comp (coherentPushforwardGMap f n)) =
      (coherentPushforwardGMap (Limits.pullback.snd (f ≫ g) a) n).comp
        (AlgebraicGeometry.Scheme.Modules.Coherent.restrictionGMap (Limits.pullback.fst (f ≫ g) a)
          n) := by
  rw [← coherentPushforwardGMap_comp]
  exact coherentPushforwardGMap_openBaseChange (f ≫ g) a n

/-- The displayed inverse comparison is the genuine inverse scheme pushforward. -/
theorem original_inverse {X Y : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : X ≅ Y) (n : ℕ)
    (x : AlgebraicGeometry.Scheme.Modules.Coherent.G X n) :
    (coherentPushforwardGEquiv e n).symm
      (coherentPushforwardGMap e.hom n x) = x :=
  (coherentPushforwardGEquiv e n).symm_apply_apply x

/-- The bundled covariant functor acts by the original maps in their correct composition order. -/
theorem bundled_comp {X Y Z : Scheme.LocallyNoetherianClosedSchemes.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    ((Scheme.GClosedPushforwardFunctor n).map (f ≫ g)).hom =
      (coherentPushforwardGMap g.hom.hom n).comp
        (coherentPushforwardGMap f.hom.hom n) :=
  coherentPushforwardGMap_comp f.hom.hom g.hom.hom n

end QuillenTest.ClosedPushforwardFunctoriality
