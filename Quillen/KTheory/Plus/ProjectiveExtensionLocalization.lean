/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveExtensionEquivariance
public import Quillen.CategoryTheory.GroupCompletion.ProjectionComma
public import Quillen.Topology.ClassifyingSpace.ExtensionTotal
public import Quillen.Topology.ClassifyingSpace.GroupCompletionContractibleUniversal

/-!
# The actual localized total extension category of finite projectives

The source for Grayson's comparison with the original Q-construction is the
simultaneous localization of the extension category by direct sums. Its
projection to the action category of the isomorphism groupoid retains the
original denominator. No plus or Q-comparison theorem is built into this type.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory
namespace Quillen.FiniteProjectiveModule
variable (R : Type u) [Ring R]
attribute [local instance] directSumMonoidal directSumSymmetric extensionDirectSumAction

/-- The actual simultaneous direct-sum localization of the total extension category. -/
def LocalizedExtensionCategory :=
  GroupCompletion.Localization (IsoCategory R) (exactStructure R).ExtensionTotal

instance localizedExtensionCategory : CategoryTheory.Category (LocalizedExtensionCategory R) :=
  inferInstanceAs (CategoryTheory.Category
    (GroupCompletion.Localization (IsoCategory R) (exactStructure R).ExtensionTotal))

/-- A denominator projective module together with an original extension object. -/
abbrev localizedExtensionPair (A : IsoCategory R) (x : (exactStructure R).ExtensionTotal) :
    LocalizedExtensionCategory R := ⟨(A, x)⟩

/-- The first-coordinate projection used to contract the localized total space. -/
def localizedExtensionBaseProjection :
    LocalizedExtensionCategory R ⥤
      GroupCompletion.ActionLocalization (IsoCategory R) (IsoCategory R) :=
  GroupCompletion.Localization.projection

/-- The original unlocalized extension category has contractible realization. -/
theorem extensionTotal_classifyingSpace_contractible :
    ContractibleSpace (ClassifyingSpace (exactStructure R).ExtensionTotal) :=
  (exactStructure R).extensionTotal_contractibleSpace

/-- Each comma category of the base projection has an actual adjunction with
its original extension fiber. Faithfulness is the proved direct-sum theorem. -/
def localizedExtensionCommaAdjunction (B : IsoCategory R) :
    letI : ∀ A : IsoCategory R, (tensorRight A).Faithful := directSumRight_faithful R
    GroupCompletion.Localization.commaTransport
      (D := (exactStructure R).ExtensionTotal) B ⊣
        GroupCompletion.Localization.commaEntry B := by
  letI : ∀ A : IsoCategory R, (tensorRight A).Faithful := directSumRight_faithful R
  exact GroupCompletion.Localization.commaTransportAdjunction B

/-- The actual localized total extension realization is contractible. The
proof uses its base projection, the comma adjunction, and Quillen's Theorem A. -/
theorem localizedExtension_classifyingSpace_contractible :
    ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) := by
  let : ∀ A : IsoCategory R, (tensorRight A).Faithful := directSumRight_faithful R
  let : ContractibleSpace (ClassifyingSpace (exactStructure R).ExtensionTotal) :=
    extensionTotal_classifyingSpace_contractible R
  exact GroupCompletion.Localization.classifyingSpace_contractible_universal
    (C := IsoCategory R) (D := (exactStructure R).ExtensionTotal)

end Quillen.FiniteProjectiveModule
