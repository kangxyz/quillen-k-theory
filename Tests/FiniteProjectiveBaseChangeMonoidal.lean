/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeMonoidal
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of original strong monoidal change of rings

Arbitrary unital ring homomorphisms act on the original projective isomorphism
groupoids by strong monoidal functors. The canonical coproduct inclusions and
original identity and composition comparisons are retained, including for the
zero ring.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory Quillen.FiniteProjectiveModule
universe u
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric rightBaseChangeMonoidal
variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

example (f : R →+* S) : (rightBaseChange f).Monoidal := inferInstance
example (f : R →+* S) : (rightBaseChange f).core.Monoidal := inferInstance

example (f : R →+* S) (P Q : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :
    coprod.inl ≫ (rightBaseChangeTensorIso f P Q).hom =
      (rightBaseChange f).map coprod.inl :=
  rightBaseChangeTensorIso_inl f P Q

example (f : R →+* S) (P Q : IsoCategory Rᵐᵒᵖ) :
    (Functor.LaxMonoidal.μ (rightBaseChange f).core P Q).iso.hom =
      coprodComparison (rightBaseChange f) P.of Q.of :=
  rightBaseChangeCore_μ_hom f P Q

example (f : R →+* S) : (rightBaseChange f).core ⋙ Core.inclusion _ =
    Core.inclusion _ ⋙ rightBaseChange f := rightBaseChangeCore_inclusion f

example : (rightBaseChangeId (R := R)).hom.IsMonoidal := inferInstance
example (f : R →+* S) (g : S →+* T) :
    (rightBaseChangeComp f g).hom.IsMonoidal := inferInstance

example : (rightBaseChange (RingHom.id (ZMod 1))).core.Monoidal := inferInstance

example : rightBaseChangeCore (RingHom.id (ZMod 1)) ≅ 𝟭 (IsoCategory (ZMod 1)ᵐᵒᵖ) :=
  rightBaseChangeCoreId

example : (rightBaseChangeCoreId (R := R)).hom.IsMonoidal := inferInstance
example (f : R →+* S) (g : S →+* T) :
    (rightBaseChangeCoreComp f g).hom.IsMonoidal := inferInstance

example (f : R →+* S) : (rightBaseChange f).Braided := rightBaseChangeBraided f

example (f : R →+* S) : (rightBaseChange f).core.Braided := by
  letI := rightBaseChangeBraided f
  infer_instance

example : (rightBaseChange (Int.castRingHom (ZMod 1))).core.Monoidal := inferInstance
