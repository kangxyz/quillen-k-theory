/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.MappingCone.Map

/-!
# Naturality of actual mapping cones under open restriction

The original restriction/cone comparison retains the given square and literal cone map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
theorem restrict_cone_map_naturality {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {K₁ L₁ K₂ L₂ : CochainComplex X.Modules ℤ}
    (p : K₁ ⟶ L₁) (q : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : p ≫ b = a ≫ q) :
    (restrict j).map (CochainComplex.mappingCone.map p q a b h) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso q
          (Scheme.Modules.restrictFunctor j)).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso p
        (Scheme.Modules.restrictFunctor j)).hom ≫
          CochainComplex.mappingCone.map ((restrict j).map p) ((restrict j).map q)
            ((restrict j).map a) ((restrict j).map b)
            (by simpa only [Functor.map_comp] using congrArg ((restrict j).map) h) := by
  ext n : 1
  have hf : (CochainComplex.mappingCone.map p q a b h).f n ≫
      (CochainComplex.mappingCone.fst q).1.v n (n + 1) rfl =
    (CochainComplex.mappingCone.fst p).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
    simp [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
      CochainComplex.mappingCone.map, Category.assoc]
  have hs : (CochainComplex.mappingCone.map p q a b h).f n ≫
      (CochainComplex.mappingCone.snd q).v n n (add_zero n) =
    (CochainComplex.mappingCone.snd p).v n n (add_zero n) ≫ b.f n := by
    simp [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
      CochainComplex.mappingCone.map, Category.assoc]
  simp only [CochainComplex.mappingCone.map] at hf hs
  simp [AlgebraicGeometry.Scheme.Modules.Complex.restrict,
    CochainComplex.mappingCone.mapHomologicalComplexIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso',
    CochainComplex.mappingCone.map, Category.assoc, -Functor.map_comp,
    ← Functor.map_comp_assoc, hf, hs]


end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
end
end

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine
theorem mappingCone_eqToIso_inr {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    {f g : K ⟶ L} (h : f = g) :
    CochainComplex.mappingCone.inr f ≫
        (eqToIso (congrArg (fun f => CochainComplex.mappingCone f) h)).hom =
      CochainComplex.mappingCone.inr g := by
  subst g
  simp


end Quillen.PerfectComplexes.ProjectiveLine
end
end
