/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenConeFiberLoop

/-! Consumers retain the original weak diagonal and the actual supported-cone fiber coordinates. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.PerfectComplexes
universe u v
namespace Quillen.Tests.CanonicalFiberObjectLoop

/-- The weak-endomorphism loop retains both actual independent parameters. -/
theorem original_weak_endomorphism {C : Type u} [Category.{v} C] (W : Structure C)
    {A : C} (f : A ⟶ A) (hf : W.weq f) (s t : unitInterval) :
    W.weakEndomorphismLoop f hf s t = W.weakObjectLoopTrack f hf (s, t) := rfl

/-- The prescribed diagonal is retained halfway through the original pasted weak-arrow track. -/
theorem original_weak_midpoint {C : Type u} [Category.{v} C] (W : Structure C)
    {A B : C} (f : A ⟶ B) (hf : W.weq f) (t : unitInterval) :
    W.weakObjectLoopTrack f hf (⟨1 / 2, by norm_num, by norm_num⟩, t) =
      Quillen.realizationEdgePath (W.weakObjectEdge f hf) t :=
  W.weakObjectLoopTrack_midpoint f hf t

/-- The original canonical fiber uses the reversed exact transformation cylinder, with its sign.
-/
theorem original_reversed_track {C : Type u} [Category.{v} C] {V : Structure C}
    (N : NestedWeakEquivalences V) (A : AcyclicCategory N) (t s : unitInterval) :
    (canonicalFiberObjectLoop N A t).val.2 s =
      acyclicObjectTransformationTrack N A (unitInterval.symm s, t) :=
  canonicalFiberObjectLoop_path_transformation N A t s

/-- The genuine supported cone keeps its original underlying cochain complex. -/
theorem original_cone_complex {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : Perfect X} (f : K ⟶ L) (hf : (perfectOpenWeakWaldhausen j).weq f) :
    (perfectOpenMappingConeAcyclic j f hf).obj.obj = CochainComplex.mappingCone f.hom := rfl

/-- The original fine source coordinate is the actual perfect mapping-cone object loop. -/
theorem original_cone_projection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : Perfect X} (f : K ⟶ L) (hf : (perfectOpenWeakWaldhausen j).weq f)
    (t : unitInterval) :
    (perfectOpenMappingConeFiberLoop j f hf t).val.1 =
      (perfectWaldhausen X).kZeroObjectLoop
        ⟨CochainComplex.mappingCone f.hom,
          locallyPerfect_mappingCone K.property L.property f.hom⟩ t :=
  perfectOpenMappingConeFiberLoop_projection j f hf t

/-- Independent fiber time and object-loop time survive on the original supported cone. -/
theorem original_cone_reversed_track {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : Perfect X} (f : K ⟶ L) (hf : (perfectOpenWeakWaldhausen j).weq f)
    (t s : unitInterval) :
    (perfectOpenMappingConeFiberLoop j f hf t).val.2 s =
      acyclicObjectTransformationTrack (perfectOpenNested j)
        (perfectOpenMappingConeAcyclic j f hf) (unitInterval.symm s, t) := rfl

end Quillen.Tests.CanonicalFiberObjectLoop
