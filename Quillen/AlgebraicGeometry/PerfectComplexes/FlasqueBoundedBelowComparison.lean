/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueBoundedBelow
public import Quillen.Waldhausen.Functoriality.KMap

/-!
# Original K-map comparison for the flasque perfect model

The actual two forward augmentation transformations give equality of the native
canonical chosen-zero K-maps. Thus the literal inclusion and original Godement
total functor induce mutually inverse maps for every natural degree, including
zero. For compact schemes the literal composite inclusion into all original
perfect complexes also induces a bijection, using the admitted lower-bounded
comparison in its original direction.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.PerfectComplexes.FlasqueBoundedBelow

/-- Inclusion after original totalization induces the identity native K-map. -/
theorem inclusion_comp_total_KMap (X : Scheme.{u}) (n : ℕ) :
    (Waldhausen.KMap (inclusion_exact X) n).comp (Waldhausen.KMap (total_exact X) n) =
      MonoidHom.id ((BoundedBelow.waldhausen X).K n) := by
  calc
    _ = Waldhausen.KMap ((total_exact X).comp (inclusion_exact X)) n :=
      Waldhausen.KMap_comp_KMap (total_exact X) (inclusion_exact X) n
    _ = Waldhausen.KMap (Waldhausen.IsExact.id (BoundedBelow.waldhausen X).cof
        (BoundedBelow.waldhausen X).weq) n :=
      (Waldhausen.KMap_eq_of_weakNatTrans
        (Waldhausen.IsExact.id (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq)
        ((total_exact X).comp (inclusion_exact X)) (unit X) (unit_weak X) n).symm
    _ = _ := Waldhausen.KMap_id (BoundedBelow.waldhausen X) n

/-- Original totalization after inclusion induces the identity native K-map. -/
theorem total_comp_inclusion_KMap (X : Scheme.{u}) (n : ℕ) :
    (Waldhausen.KMap (total_exact X) n).comp (Waldhausen.KMap (inclusion_exact X) n) =
      MonoidHom.id ((waldhausen X).K n) := by
  calc
    _ = Waldhausen.KMap ((inclusion_exact X).comp (total_exact X)) n :=
      Waldhausen.KMap_comp_KMap (inclusion_exact X) (total_exact X) n
    _ = Waldhausen.KMap (Waldhausen.IsExact.id (waldhausen X).cof (waldhausen X).weq) n :=
      (Waldhausen.KMap_eq_of_weakNatTrans
        (Waldhausen.IsExact.id (waldhausen X).cof (waldhausen X).weq)
        ((inclusion_exact X).comp (total_exact X)) (flasqueUnit X) (flasqueUnit_weak X) n).symm
    _ = _ := Waldhausen.KMap_id (waldhausen X) n

/-- The inverse on original K-groups is supplied by the actual Godement total map. -/
theorem total_KMap_leftInverse (X : Scheme.{u}) (n : ℕ) :
    Function.LeftInverse (Waldhausen.KMap (total_exact X) n)
      (Waldhausen.KMap (inclusion_exact X) n) :=
  fun x => DFunLike.congr_fun (total_comp_inclusion_KMap X n) x

/-- The other inverse law follows from the actual source-model augmentation. -/
theorem total_KMap_rightInverse (X : Scheme.{u}) (n : ℕ) :
    Function.RightInverse (Waldhausen.KMap (total_exact X) n)
      (Waldhausen.KMap (inclusion_exact X) n) :=
  fun x => DFunLike.congr_fun (inclusion_comp_total_KMap X n) x

/-- The actual original full inclusion induces a bijection in every natural degree. -/
theorem inclusion_KMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (inclusion_exact X) n) :=
  ⟨(total_KMap_leftInverse X n).injective, (total_KMap_rightInverse X n).surjective⟩

/-- The literal original full inclusion into all locally perfect complexes. -/
def perfectInclusion (X : Scheme.{u}) : Obj X ⥤ Perfect X :=
  inclusion X ⋙ BoundedBelow.inclusion X

/-- This same literal composite inclusion is Waldhausen-exact. -/
lemma perfectInclusion_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (waldhausen X).cof (waldhausen X).weq
    (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectInclusion X) :=
  (inclusion_exact X).comp (BoundedBelow.inclusion_exact X)

/-- The K-map is the composite of the two actual original inclusion K-maps. -/
theorem perfectInclusion_KMap_eq (X : Scheme.{u}) (n : ℕ) :
    Waldhausen.KMap (perfectInclusion_exact X) n =
      (Waldhausen.KMap (BoundedBelow.inclusion_exact X) n).comp
        (Waldhausen.KMap (inclusion_exact X) n) :=
  (Waldhausen.KMap_comp_KMap (inclusion_exact X) (BoundedBelow.inclusion_exact X) n).symm

/-- On a compact scheme the unchanged original flasque-perfect inclusion induces
an isomorphism on native K-groups, including degree zero. -/
theorem perfectInclusion_KMap_bijective (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (perfectInclusion_exact X) n) := by
  rw [perfectInclusion_KMap_eq]
  exact (BoundedBelow.inclusion_KMap_bijective X n).comp (inclusion_KMap_bijective X n)

end Quillen.PerfectComplexes.FlasqueBoundedBelow
