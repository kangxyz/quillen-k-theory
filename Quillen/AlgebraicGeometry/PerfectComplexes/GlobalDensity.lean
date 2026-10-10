/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRetractComplement

/-!
# Genuine global perfect-complex density on qcqs schemes

For any quasi-compact quasi-separated scheme X and compact open U, every
ORIGINAL locally-perfect complex E on U is a literal derived retract of the
restriction of an actual global perfect complex. An actual perfect complement
C then identifies the original restriction with the literal complex E plus C.
The same theorem is proved for arbitrary compact open immersions, retaining
the original restriction functor rather than a chosen open presentation.

The proof adds a finite affine cover one chart at a time, using actual weak
stabilization maps, original restriction-composition isomorphisms, and genuine
perfect gluing. Shift multiplicities may grow; only the original derived
summand and actual perfect complement are claimed. Quasi-separatedness is
used for compact overlaps, without a global affine-diagonal hypothesis.
Global morphism roofs and a K-theory localization endpoint are separate results.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Transport an existing original retract across one actual weak stabilization
map and the literal open-restriction composition isomorphism. -/
def derivedRetractOfWeakStabilization {U Y X : Scheme.{u}}
    (i : U ⟶ Y) (j : Y ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    {E : Complex U} {P : Complex Y} {Q : Complex X}
    (r : Retract ((toDerived U).obj E) ((toDerived U).obj ((restrict i).obj P)))
    (f : P ⊞ P⟦(1 : ℤ)⟧ ⟶ (restrict j).obj Q) [QuasiIso f] :
    Retract ((toDerived U).obj E) ((toDerived U).obj ((restrict (i ≫ j)).obj Q)) := by
  let rP : Retract P (P ⊞ P⟦(1 : ℤ)⟧) :=
    { i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst }
  exact r.trans ((rP.map (restrict i ⋙ toDerived U)).trans (Retract.ofIso
    (asIso ((toDerived U).map ((restrict i).map f)) ≪≫
      (toDerived U).mapIso ((restrictCompIso i j).app Q))))

lemma isCompact_finite_affine_sup {X : Scheme.{u}} (s : Finset X.affineOpens) :
    IsCompact ((s.sup (fun V => V.val) : X.Opens) : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert V s hV ih =>
    rw [Finset.sup_insert]
    exact V.property.isCompact.union ih

lemma exists_perfect_retract_on_finite_affine_union {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (E : Complex U.toScheme)
    (hE : locallyPerfect U.toScheme E) (s : Finset X.affineOpens) :
    ∃ (hUS : U ≤ U ⊔ s.sup (fun V => V.val))
      (P : Complex (U ⊔ s.sup (fun V => V.val)).toScheme),
      locallyPerfect (U ⊔ s.sup (fun V => V.val)).toScheme P ∧
      Nonempty (Retract ((toDerived U.toScheme).obj E)
        ((toDerived U.toScheme).obj ((restrict (X.homOfLE hUS)).obj P))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, sup_bot_eq]
    refine ⟨le_rfl, E, hE, ⟨Retract.ofIso ((toDerived U.toScheme).mapIso ?_)⟩⟩
    exact ((eqToIso (restrict_congr (X.homOfLE_rfl U)) ≪≫ restrictIdIso U.toScheme).app E).symm
  | @insert V s hV ih =>
    rw [Finset.sup_insert, show U ⊔ (V.val ⊔ s.sup (fun V => V.val)) =
      (U ⊔ s.sup (fun V => V.val)) ⊔ V.val by ac_rfl]
    let S := U ⊔ s.sup (fun V => V.val)
    have hS : IsCompact (S : Set X) := hU.union (isCompact_finite_affine_sup s)
    let : CompactSpace S.toScheme := isCompact_iff_compactSpace.mp hS
    let : IsAffine V.val.toScheme := V.property
    let : QuasiSeparatedSpace (S ⊔ V.val).toScheme :=
      QuasiSeparatedSpace.of_isOpenEmbedding (S ⊔ V.val).ι.isOpenEmbedding
    obtain ⟨hUS, P, hP, ⟨r⟩⟩ := ih
    let i := X.homOfLE hUS
    let j := X.homOfLE (le_sup_left : S ≤ S ⊔ V.val)
    let k := X.homOfLE (le_sup_right : V.val ≤ S ⊔ V.val)
    have hcover (x : (S ⊔ V.val).toScheme) : x ∈ Set.range j ∨ x ∈ Set.range k := by
      rcases x.property with hx | hx
      · exact Or.inl ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
      · exact Or.inr ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
    obtain ⟨Q, hQ, f, hf⟩ := exists_perfect_extension_across_affine_openImmersion j k hcover P hP
    refine ⟨hUS.trans le_sup_left, Q, hQ, ⟨(derivedRetractOfWeakStabilization i j r f).trans
      (Retract.ofIso ?_)⟩⟩
    exact (toDerived U.toScheme).mapIso
      ((eqToIso (restrict_congr (X.homOfLE_homOfLE hUS
        (le_sup_left : S ≤ S ⊔ V.val)))).app Q)

/-- On an arbitrary qcqs scheme, every original perfect complex on a compact
open is a literal derived retract of the original restriction of a global
perfect complex. Only a finite affine cover is used; shift multiplicities are
allowed to grow during the actual chart-by-chart construction. -/
lemma locallyPerfect_exists_global_derived_retract {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (E : Complex U.toScheme)
    (hE : locallyPerfect U.toScheme E) :
    ∃ P : Complex X, locallyPerfect X P ∧
      Nonempty (Retract ((toDerived U.toScheme).obj E)
        ((toDerived U.toScheme).obj ((restrict U.ι).obj P))) := by
  classical
  obtain ⟨s, hs, hcover⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (X := X) (U := ⊤)).mp (by simpa using (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set
      X)))
  have ht : hs.toFinset.sup (fun V => V.val) = (⊤ : X.Opens) := by
    simpa only [Finset.sup_eq_iSup, Set.Finite.mem_toFinset] using hcover.symm
  have h := exists_perfect_retract_on_finite_affine_union U hU E hE hs.toFinset
  rw [ht, sup_top_eq] at h
  obtain ⟨hUTop, P, hP, ⟨r⟩⟩ := h
  let Q := (restrict X.topIso.inv).obj P
  have hj : U.ι ≫ X.topIso.inv = X.homOfLE (le_top : U ≤ ⊤) := by
    apply (cancel_mono (⊤ : X.Opens).ι).mp
    simp
  let e : (restrict U.ι).obj Q ≅ (restrict (X.homOfLE (le_top : U ≤ ⊤))).obj P :=
    (restrictCompIso U.ι X.topIso.inv ≪≫ eqToIso (restrict_congr hj)).app P
  exact ⟨Q, locallyPerfect_restrict X.topIso.inv hP,
    ⟨r.trans (Retract.ofIso ((toDerived U.toScheme).mapIso e.symm))⟩⟩

/-- Genuine global density on a qcqs scheme: the ORIGINAL local perfect E has
an actual local perfect complement, and their literal complex biproduct is
derived-isomorphic to the original restriction of an actual global perfect P. -/
lemma locallyPerfect_exists_global_perfect_complement {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (E : Complex U.toScheme)
    (hE : locallyPerfect U.toScheme E) :
    ∃ (P : Complex X) (C : Complex U.toScheme),
      locallyPerfect X P ∧ locallyPerfect U.toScheme C ∧
      Nonempty ((toDerived U.toScheme).obj ((restrict U.ι).obj P) ≅
        (toDerived U.toScheme).obj (E ⊞ C)) := by
  obtain ⟨P, hP, ⟨r⟩⟩ := locallyPerfect_exists_global_derived_retract U hU E hE
  obtain ⟨C, hC, e, he⟩ := exists_actual_perfect_complement_of_derived_retract hE
    (locallyPerfect_restrict U.ι hP) r
  exact ⟨P, C, hP, hC, ⟨e⟩⟩

/-- The same original global complement for an arbitrary compact open immersion,
with no chosen presentation of its source as a literal open subscheme. -/
lemma locallyPerfect_exists_global_perfect_complement_of_openImmersion
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (E : Complex U) (hE : locallyPerfect U E) :
    ∃ (P : Complex X) (C : Complex U), locallyPerfect X P ∧ locallyPerfect U C ∧
      Nonempty ((toDerived U).obj ((restrict j).obj P) ≅ (toDerived U).obj (E ⊞ C)) := by
  let W := j.opensRange
  have hW : IsCompact (W : Set X) := isCompact_range j.continuous
  let E' := (restrict j.isoOpensRange.inv).obj E
  obtain ⟨P, C', hP, hC', ⟨e⟩⟩ := locallyPerfect_exists_global_perfect_complement W hW E'
    (locallyPerfect_restrict j.isoOpensRange.inv hE)
  let C := (restrict j.isoOpensRange.hom).obj C'
  let eleft : (restrict j).obj P ≅ (restrict j.isoOpensRange.hom).obj ((restrict W.ι).obj P) :=
    ((restrictCompIso j.isoOpensRange.hom W.ι ≪≫
      eqToIso (restrict_congr j.isoOpensRange_hom_ι)).symm).app P
  let eE : (restrict j.isoOpensRange.hom).obj E' ≅ E :=
    (restrictCompIso j.isoOpensRange.hom j.isoOpensRange.inv ≪≫
      eqToIso (restrict_congr j.isoOpensRange.hom_inv_id) ≪≫ restrictIdIso U).app E
  let : PreservesBinaryBiproducts (restrict j.isoOpensRange.hom) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let eright := (restrict j.isoOpensRange.hom).mapBiprod E' C' ≪≫ biprod.mapIso eE (Iso.refl C)
  exact ⟨P, C, hP, locallyPerfect_restrict j.isoOpensRange.hom hC',
    ⟨(toDerived U).mapIso eleft ≪≫ restrictDerivedIso j.isoOpensRange.hom e ≪≫
      (toDerived U).mapIso eright⟩⟩

end Quillen.PerfectComplexes
