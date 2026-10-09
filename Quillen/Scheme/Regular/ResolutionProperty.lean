import Quillen.Scheme.Regular.AffineResolution

/-!
# The geometric resolution property

The hypothesis here says only that every coherent sheaf is the quotient of
an actual finite locally free sheaf. It assumes neither a finite resolution
nor projectivity of vector bundles as global sheaf objects. Its first
syzygy is the genuine coherent kernel of this quotient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme

variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- The usual resolution property: each coherent sheaf is a quotient of a
finite locally free sheaf. Both the object and epimorphism live in the actual
coherent category with its ambient sheaf exact structure. -/
class HasResolutionProperty : Prop where
  exists_vectorBundle_epi (M : CoherentScheme.Coherent X) :
    ∃ P : CoherentScheme.Coherent X, SchemeSheaf.coherentVectorBundle X P ∧
      ∃ p : P ⟶ M, Epi p

/-- The categorical formulation is exactly the ordinary sheaf quotient
formulation: the source is an actual vector bundle and the underlying sheaf
morphism is an epimorphism. -/
theorem hasResolutionProperty_iff_sheaf_epi : HasResolutionProperty X ↔
    ∀ M : CoherentScheme.Coherent X, ∃ V : SchemeSheaf.FiniteLocallyFree X,
      ∃ p : V.obj ⟶ M.obj, Epi p := by
  constructor
  · intro h M
    obtain ⟨P, hP, p, hp⟩ := h.exists_vectorBundle_epi M
    have := hp
    exact ⟨⟨P.obj, hP⟩, p.hom,
      inferInstanceAs (Epi ((CoherentScheme.coherentToSheaves X).map p))⟩
  · intro h
    constructor
    intro M
    obtain ⟨V, p, hp⟩ := h M
    let P := (SchemeSheaf.vectorBundleToCoherent X).obj V
    let q : P ⟶ M := ObjectProperty.homMk p
    have : Epi ((CoherentScheme.coherentToSheaves X).map q) := hp
    exact ⟨P, V.property, q,
      Functor.epi_of_epi_map (CoherentScheme.coherentToSheaves X) inferInstance⟩

/-- A vector-bundle cover has a genuine coherent syzygy and gives an actual
short exact sequence. No splitting or global projectivity is used. -/
theorem exists_vectorBundle_shortExact [HasResolutionProperty X]
    (M : CoherentScheme.Coherent X) :
    ∃ (K P : CoherentScheme.Coherent X) (i : K ⟶ P) (p : P ⟶ M)
      (w : i ≫ p = 0), SchemeSheaf.coherentVectorBundle X P ∧
        (ShortComplex.mk i p w).ShortExact := by
  obtain ⟨P, hP, p, hp⟩ := HasResolutionProperty.exists_vectorBundle_epi M
  have := hp
  exact ⟨kernel p, P, kernel.ι p, p, kernel.condition p, hP,
    { exact := ShortComplex.exact_kernel p }⟩

/-- Every noetherian affine scheme has the geometric resolution property,
by a finite free module cover and the actual tilde equivalence. -/
instance hasResolutionProperty_spec (R : CommRingCat.{u}) [IsNoetherianRing R] :
    HasResolutionProperty (Spec R) where
  exists_vectorBundle_epi M := by
    let E := CoherentScheme.coherentSpecModuleEquivalence R
    obtain ⟨K, P, i, p, w, hP, hS⟩ :=
      CoherentScheme.exists_finiteFree_shortExact R (E.functor.obj M)
    have := hS.epi_g
    refine ⟨E.inverse.obj P, SchemeSheaf.finiteModuleTilde_finiteFree R P hP,
      E.inverse.map p ≫ (E.unitIso.app M).inv, ?_⟩
    infer_instance

end Quillen.Scheme
