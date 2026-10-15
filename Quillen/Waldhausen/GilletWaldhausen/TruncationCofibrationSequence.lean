/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.QuotientExact
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-!
# The genuine acyclic truncation cofibration sequence

The actual truncation inclusion, identity functor, and actual cokernel
projection satisfy all structural hypotheses of the additivity theorem.
The relative-pushout cofibration condition is derived from exactness of
the quotient, rather than supplied as a hypothesis.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u

namespace Quillen.Waldhausen.GilletWaldhausen

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The canonical inclusion, as an actual natural transformation. -/
def boundedAcyclicTruncationInclusion (n : ℤ) :
    boundedAcyclicTruncLEFunctor P n ⟶ 𝟭 (boundedAcyclic P).FullSubcategory where
  app K := ((acyclicTruncationSequenceFunctor P n).obj K).f
  naturality _ _ f := ((acyclicTruncationSequenceFunctor P n).map f).comm₁₂

/-- The canonical quotient projection, as an actual natural transformation. -/
def boundedAcyclicTruncationProjection (n : ℤ) :
    𝟭 (boundedAcyclic P).FullSubcategory ⟶ boundedAcyclicQuotientFunctor P n where
  app K := ((acyclicTruncationSequenceFunctor P n).obj K).g
  naturality _ _ f := ((acyclicTruncationSequenceFunctor P n).map f).comm₂₃

@[reassoc]
theorem boundedAcyclicTruncation_comp_zero (n : ℤ) :
    boundedAcyclicTruncationInclusion P n ≫ boundedAcyclicTruncationProjection P n = 0 := by
  apply NatTrans.ext
  funext K
  exact ((acyclicTruncationSequenceFunctor P n).obj K).zero

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual truncation sequence satisfies the ordinary relative-cofibration
condition for the inherited exact structure. -/
theorem boundedAcyclicTruncation_cofibration (n : ℤ) :
    Additivity.IsCofibrationTransformation (ofExactCategory (boundedAcyclicExactStructure P))
      (boundedAcyclicTruncationInclusion P n)
      (ofExactCategory (boundedAcyclicExactStructure P)) :=
  exactFunctorSequence_cofibration _ _ _ _ (boundedAcyclicTruncation_comp_zero P n)
    (acyclicTruncationSequenceFunctor_conflation P n)
    (boundedAcyclicQuotientExactFunctor P n).map_inflation

/-- A genuine cofibration sequence of exact functors, with isomorphism weak
 equivalences and the original actual truncation/cokernel maps. -/
theorem boundedAcyclicTruncation_isCofibrationSequence (n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (boundedAcyclicExactStructure P))
      (ofExactCategory (boundedAcyclicExactStructure P))
      (boundedAcyclicTruncationInclusion P n) (boundedAcyclicTruncationProjection P n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (boundedAcyclicTruncation_comp_zero P n)
    (acyclicTruncationSequenceFunctor_conflation P n)
    (boundedAcyclicTruncLEExactFunctor P n) (CategoryTheory.ExactCategory.ExactFunctor.id
      (boundedAcyclicExactStructure P))
    (boundedAcyclicQuotientExactFunctor P n) rfl rfl rfl

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- Every actual map of acyclic complexes is a genuine quasi-isomorphism. -/
theorem boundedAcyclic_map_quasiIso {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    QuasiIso f.hom := by
  rw [quasiIso_iff]
  intro i
  exact (quasiIsoAt_iff_exactAt' f.hom i (L.property.2.2 i)).2 (K.property.2.2 i)

omit [(abelianExactStructure A).IsKernelClosed P] in
/-- Exactness also holds with genuine quasi-isomorphisms, since these are
all actual maps in the bounded acyclic category. -/
theorem boundedAcyclicExactFunctor_waldhausenExact
    (F : ExactFunctor (boundedAcyclicExactStructure P) (boundedAcyclicExactStructure P)) :
    IsExact (complexSubcategory (boundedAcyclic P)).cof
      (complexSubcategory (boundedAcyclic P)).weq
      (complexSubcategory (boundedAcyclic P)).cof
      (complexSubcategory (boundedAcyclic P)).weq F.toFunctor where
  zero hZ := F.toFunctor.map_isZero hZ
  cofibration f hf := F.map_inflation f hf
  weak f _ := boundedAcyclic_map_quasiIso P (F.toFunctor.map f)
  pushout hi h := F.map_isPushout hi h

/-- The same actual truncation cofibration sequence for genuine quasi-isomorphisms. -/
theorem boundedAcyclicTruncation_isCofibrationSequence_quasiIso (n : ℤ) :
    Additivity.IsCofibrationSequence (complexSubcategory (boundedAcyclic P))
      (complexSubcategory (boundedAcyclic P))
      (boundedAcyclicTruncationInclusion P n) (boundedAcyclicTruncationProjection P n) where
  exactF := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicTruncLEExactFunctor P n)
  exactG := IsExact.id _ _
  exactH := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicQuotientExactFunctor P n)
  cofibration := {
    app_cof := (boundedAcyclicTruncation_cofibration P n).app_cof
    relative_cof f hf := (boundedAcyclicTruncation_cofibration P n).relative_cof f hf }
  cofiber := (boundedAcyclicTruncation_isCofibrationSequence P n).cofiber

end Quillen.Waldhausen.GilletWaldhausen
