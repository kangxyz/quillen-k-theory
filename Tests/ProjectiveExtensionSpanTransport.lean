/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveExtensionSpanTransport

/-! # Original extension transport and genuine lineator regression tests -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.FiniteProjectiveModule
attribute [local instance] directSumMonoidal directSumSymmetric extensionFiberDirectSumAction

variable (R : Type u) [Ring R]
  {X Y : Quillen.FiniteProjectiveModule.Category.{u, u} R}

example (f : X ⟶ Y) :
    ((exactStructure R).extensionFiberPullback f).LaxLeftLinear (IsoCategory R) :=
  extensionFiberPullbackLinear R f

example (f : X ⟶ Y) (hf : (exactStructure R).deflation f) :
    ((exactStructure R).extensionFiberPostcompose f hf).LaxLeftLinear (IsoCategory R) :=
  extensionFiberPostcomposeLinear R f hf

example (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    ((exactStructure R).extensionSpanTransport s).LaxLeftLinear (IsoCategory R) :=
  extensionSpanTransportLinear R s

example (f : X ⟶ Y) (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    S ⊙ₗ ((exactStructure R).extensionFiberPullback f).obj p ≅
      ((exactStructure R).extensionFiberPullback f).obj (S ⊙ₗ p) :=
  extensionPullbackAddIso R f S p

example (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    (A : Quillen.GroupCompletion.Localization (IsoCategory R)
      ((exactStructure R).ExtensionFiber Y)) :
    (localizedExtensionSpanTransport R s).obj A =
      ⟨(A.obj.1, ((exactStructure R).extensionSpanTransport s).obj A.obj.2)⟩ := rfl

example (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    IsWeakHomotopyEquivalence
      (Quillen.classifyingSpaceMapUniversal (localizedExtensionSpanTransport R s)) :=
  localizedExtensionSpanTransport_isWeakHomotopyEquivalence R s

example (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    letI := extensionSpanTransportLinear R s
    (Functor.LaxLeftLinear.μₗ ((exactStructure R).extensionSpanTransport s) S p).iso.hom.hom.left =
      extensionPullbackAddHom R s.r S p :=
  extensionSpanTransportLinear_μ_middle R s S p
