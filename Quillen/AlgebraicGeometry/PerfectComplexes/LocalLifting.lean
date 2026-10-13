/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction

/-!
# Local lifting from vector bundles

A morphism out of a finite locally free sheaf lifts locally through any
surjection. This uses a pullback and the already-proved local splitting
of vector-bundle quotients. The output uses actual open restriction of
scheme modules, rather than a surrogate site-over category.

This is a single-degree input for the finite shrinking induction needed to
lift maps from bounded vector-bundle complexes. No global projectivity of
vector bundles is claimed.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Quillen.PerfectComplexes

variable {X : Scheme.{u}}

/-- An epimorphism onto a vector bundle admits sections on actual open
subschemes near every point. -/
theorem exists_local_section {E P : X.Modules} (q : E ⟶ P) [Epi q]
    [SchemeSheaf.IsFiniteLocallyFree X P] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ s : (Scheme.Modules.restrictFunctor U.ι).obj P ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj E,
        s ≫ (Scheme.Modules.restrictFunctor U.ι).map q = 𝟙 _ := by
  have hs : (ShortComplex.kernelSequence q).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact q
      epi_g := inferInstanceAs (Epi q) }
  obtain ⟨U, hxU, ⟨s⟩⟩ := @SchemeSheaf.exists_local_splitting X
    (ShortComplex.kernelSequence q) hs
    (inferInstanceAs (SchemeSheaf.IsFiniteLocallyFree X P)) x
  let F := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U
  let σ := e.inv.app P ≫ F.map s.s ≫ e.hom.app E
  refine ⟨U, hxU, σ, ?_⟩
  have he := e.hom.naturality q
  have hs' : s.s ≫ q.over U = 𝟙 _ := s.s_g
  change e.inv.app P ≫ F.map s.s ≫ e.hom.app E ≫
    (Scheme.Modules.restrictFunctor U.ι).map q = 𝟙 _
  rw [← he]
  change e.inv.app P ≫ F.map s.s ≫ F.map (q.over U) ≫ e.hom.app P = 𝟙 _
  rw [← Functor.map_comp_assoc, hs']
  change e.inv.app P ≫ F.map (𝟙 (P.over U)) ≫ e.hom.app P = 𝟙 _
  rw [F.map_id]
  erw [Category.id_comp]
  exact e.inv_hom_id_app P

/-- A map from a vector bundle lifts locally through a surjection. -/
theorem exists_local_lift {E N P : X.Modules} (p : E ⟶ N) [Epi p]
    (f : P ⟶ N) [SchemeSheaf.IsFiniteLocallyFree X P] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ l : (Scheme.Modules.restrictFunctor U.ι).obj P ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj E,
        l ≫ (Scheme.Modules.restrictFunctor U.ι).map p =
          (Scheme.Modules.restrictFunctor U.ι).map f := by
  obtain ⟨U, hxU, s, hs⟩ := exists_local_section (pullback.snd p f) x
  let R := Scheme.Modules.restrictFunctor U.ι
  refine ⟨U, hxU, s ≫ R.map (pullback.fst p f), ?_⟩
  change (s ≫ R.map (pullback.fst p f)) ≫ R.map p = R.map f
  rw [Category.assoc, ← R.map_comp, pullback.condition, R.map_comp, ← Category.assoc, hs]
  simp

/-- A map from a vector bundle into the kernel of the second arrow of an
exact sequence locally factors through the first arrow. This is the local
analogue of the lifting lemma used for globally projective objects. -/
theorem exists_local_factor_of_exact {S : ShortComplex X.Modules} (hS : S.Exact)
    {P : X.Modules} [SchemeSheaf.IsFiniteLocallyFree X P]
    (f : P ⟶ S.X₂) (hf : f ≫ S.g = 0) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ l : (Scheme.Modules.restrictFunctor U.ι).obj P ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj S.X₁,
        l ≫ (Scheme.Modules.restrictFunctor U.ι).map S.f =
          (Scheme.Modules.restrictFunctor U.ι).map f := by
  let := hS.epi_toCycles
  obtain ⟨U, hxU, l, hl⟩ := exists_local_lift S.toCycles (S.liftCycles f hf) x
  let R := Scheme.Modules.restrictFunctor U.ι
  refine ⟨U, hxU, l, ?_⟩
  change l ≫ R.map S.f = R.map f
  rw [← S.toCycles_i, R.map_comp, ← Category.assoc, hl, ← R.map_comp, S.liftCycles_i]


end Quillen.PerfectComplexes
