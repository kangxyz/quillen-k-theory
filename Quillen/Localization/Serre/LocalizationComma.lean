/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.Localization.Serre.FiberComparison
public import Quillen.Localization.Serre.AuxiliaryLift
public import Quillen.Devissage.CommaLayers
public import Quillen.Devissage.FullyFaithful
public import Quillen.Topology.ClassifyingSpace.Equivalence
public import Quillen.CategoryTheory.TheoremB.Naturality
public import Quillen.CategoryTheory.TheoremA.ContractibleComma

/-!
# The zero comma category of a Serre quotient

For the covariant comma convention `(Q(q) ↓ V)`, the zero comma category is
actually equivalent to `Q(P)`. A Q-arrow to an original zero object forces its
source to be zero, because its right leg is monic and its left leg is epic.
Consequently the objects of the zero comma category are exactly those of the
Serre subcategory. The comparison uses the canonical quotient nullhomotopy,
and lies strictly over the Q-inclusion.

The source-zero structured comma comparison is also proved. More generally,
the inclusion of isomorphism objects into every quotient structured comma
category is a homotopy equivalence. Its actual comma fibers are identified
with lifted interval posets, whose join operation gives a concrete contraction.
The checked Theorem A supplies the prescribed inclusion as the forward map.
Q-isomorphism classification and complete layer-endpoint invariants discharge
all span representative choices in this comparison.

These supply zero-comma identifications in localization. They do not assert
Theorem B's transition hypothesis or the localization theorem.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Topology

namespace Quillen

/-- A nonempty join-semilattice has a concrete classifying-space contraction:
join with one chosen object receives natural transformations from both the
identity and the constant functor. No general filtered-nerve theorem is used. -/
theorem classifyingSpace_contractible_of_semilatticeSup
    (A : Type u) [SemilatticeSup A] [Nonempty A] : ContractibleSpace (ClassifyingSpace A) := by
  let a : A := Classical.choice inferInstance
  let F : A ⥤ A := (show Monotone (fun x : A => x ⊔ a) from
    fun _ _ h => sup_le_sup_right h a).functor
  let η : 𝟭 A ⟶ F := { app := fun x => homOfLE le_sup_left }
  let ε : (Functor.const A).obj a ⟶ F := { app := fun x => homOfLE le_sup_right }
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨classifyingSpacePoint a, ?_⟩
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_const, TopCat.hom_id] using
    (ContinuousMap.Homotopic.trans
      ⟨classifyingSpaceNaturalTransformationHomotopy η⟩
      ⟨(classifyingSpaceNaturalTransformationHomotopy ε).symm⟩)

end Quillen

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A Q-arrow into an original zero object forces its source object to be zero.
No zero-object assertion about the entire Q-category is involved. -/
theorem isZero_source_of_qHom {X Y : E.QCategory} (f : X ⟶ Y)
    (hY : IsZero Y.obj.of) : IsZero X.obj.of := by
  induction f using Quotient.inductionOn with
  | _ s =>
    have : Mono s.r := E.mono_of_inflation s.wr
    have : Epi s.l := E.epi_of_deflation s.wl
    have hS : IsZero s.apex := (IsZero.iff_id_eq_zero _).2 (by
      apply (cancel_mono s.r).1
      exact hY.eq_of_tgt _ _)
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi s.l).1
    exact hS.eq_of_src _ _

end CategoryTheory.ExactCategory.ExactStructure

namespace Quillen.Q

attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- An invertible abelian Q-arrow has invertible legs in every span
representative. The proof uses both inverse identities and actual pullbacks. -/
theorem isIso_legs_of_isIso {X Y : C} (s : Q.AbelianSpan X Y)
    [IsIso (Q.mkHom _ _ s)] : IsIso s.l ∧ IsIso s.r := by
  obtain ⟨t, ht⟩ := Quotient.exists_rep (inv (Q.mkHom _ _ s))
  change Q.AbelianSpan Y X at t
  change Q.mkHom _ _ t = inv (Q.mkHom _ _ s) at ht
  have h₁ : Q.mkHom _ _ (Span.comp s t) = Q.mkHom _ _ (Span.id X) := by
    change Q.mkHom _ _ s ≫ Q.mkHom _ _ t = 𝟙 _
    rw [ht]
    exact IsIso.hom_inv_id _
  have h₂ : Q.mkHom _ _ (Span.comp t s) = Q.mkHom _ _ (Span.id Y) := by
    change Q.mkHom _ _ t ≫ Q.mkHom _ _ s = 𝟙 _
    rw [ht]
    exact IsIso.inv_hom_id _
  obtain ⟨e₁, hl₁, _⟩ := (Q.mkHom_eq_iff_apexIso _ _ _ _).1 h₁
  obtain ⟨e₂, _, hr₂⟩ := (Q.mkHom_eq_iff_apexIso _ _ _ _).1 h₂
  have hl : pullback.fst s.r t.l ≫ s.l = e₁.hom := by simpa [Span.comp] using hl₁.symm
  have hr : pullback.snd t.r s.l ≫ s.r = e₂.hom := by simpa [Span.comp] using hr₂.symm
  have : Mono (pullback.fst s.r t.l) := mono_of_mono_fac hl
  have : IsIso (pullback.fst s.r t.l) := isIso_of_mono_of_epi _
  have : IsIso (pullback.fst s.r t.l ≫ s.l) := by rw [hl]; infer_instance
  have hleft : IsIso s.l := IsIso.of_isIso_comp_left (pullback.fst s.r t.l) s.l
  have : Epi s.r := epi_of_epi_fac hr
  exact ⟨hleft, isIso_of_mono_of_epi _⟩

set_option backward.isDefEq.respectTransparency false in
/-- If a span's two legs are invertible, its Q-class is exactly the ordinary
isomorphism obtained by inverting the left leg and following the right leg. -/
theorem mkHom_eq_qIsoOfIso {X Y : C} (s : Q.AbelianSpan X Y) [IsIso s.l] [IsIso s.r] :
    Q.mkHom _ _ s =
      ((abelianExactStructure C).qIsoOfIso ((asIso s.l).symm ≪≫ asIso s.r)).hom := by
  apply Q.mkHom_eq_of_apexIso _ _ s _ (asIso s.l)
  · simp [Q.isoSpan]
  · simp [Q.isoSpan]

set_option backward.isDefEq.respectTransparency false in
/-- Every invertible abelian Q-arrow comes from an actual ambient isomorphism. -/
theorem exists_iso_of_isIso {X Y : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    [hf : IsIso f] : ∃ e : X ≅ Y, ((abelianExactStructure C).qIsoOfIso e).hom = f := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep f
  change Q.AbelianSpan X Y at s
  change Q.mkHom _ _ s = f at hs
  have : IsIso (Q.mkHom _ _ s) := by rw [hs]; infer_instance
  obtain ⟨hl, hr⟩ := isIso_legs_of_isIso s
  let := hl
  let := hr
  exact ⟨(asIso s.l).symm ≪≫ asIso s.r, (mkHom_eq_qIsoOfIso s).symm.trans hs⟩

/-- Changing the source and apex of a span by compatible isomorphisms
preserves its lower endpoint as an actual subobject of the target. -/
theorem spanLower_eq_of_iso {X Y M : C} (s : Q.AbelianSpan X M) (t : Q.AbelianSpan Y M)
    (e : X ≅ Y) (a : s.apex ≅ t.apex)
    (hl : s.l ≫ e.hom = a.hom ≫ t.l) (hr : s.r = a.hom ≫ t.r) :
    Devissage.spanLower s = Devissage.spanLower t := by
  apply Subobject.mk_eq_mk_of_comm _ _ (kernel.mapIso s.l t.l a e hl)
  simp [Category.assoc, hr]

/-- The upper endpoint has the same invariance under compatible isomorphisms. -/
theorem spanUpper_eq_of_iso {X Y M : C} (s : Q.AbelianSpan X M) (t : Q.AbelianSpan Y M)
    (a : s.apex ≅ t.apex) (hr : s.r = a.hom ≫ t.r) :
    Devissage.spanUpper s = Devissage.spanUpper t :=
  Subobject.mk_eq_mk_of_comm _ _ a hr.symm

set_option backward.isDefEq.respectTransparency false in
/-- The lower subobject of a Q-arrow, independent of its representative. -/
def arrowLower {X M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Subobject M := by
  refine Quotient.liftOn f (fun s : Q.AbelianSpan X M => Devissage.spanLower s) ?_
  intro s t h
  change Q.AbelianSpan X M at s t
  obtain ⟨a, hl, hr⟩ := (Q.mkHom_eq_iff_apexIso _ _ s t).1 (Quotient.sound h)
  exact spanLower_eq_of_iso s t (Iso.refl X) a (by simpa using hl.symm) hr.symm

set_option backward.isDefEq.respectTransparency false in
/-- The upper subobject of a Q-arrow, independent of its representative. -/
def arrowUpper {X M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Subobject M := by
  refine Quotient.liftOn f (fun s : Q.AbelianSpan X M => Devissage.spanUpper s) ?_
  intro s t h
  change Q.AbelianSpan X M at s t
  obtain ⟨a, _, hr⟩ := (Q.mkHom_eq_iff_apexIso _ _ s t).1 (Quotient.sound h)
  exact spanUpper_eq_of_iso s t a hr.symm

/-- The two endpoints of a Q-arrow form a genuine interval. -/
theorem arrowLower_le_upper {X M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowLower f ≤ arrowUpper f := by
  induction f using Quotient.inductionOn with | _ s =>
  exact Devissage.spanLower_le_upper s

set_option backward.isDefEq.respectTransparency false in
/-- Source isomorphisms do not change the lower endpoint of a Q-arrow. -/
theorem arrowLower_comp_iso {X Y M : C} (e : X ≅ Y)
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowLower (((abelianExactStructure C).qIsoOfIso e).hom ≫ f) = arrowLower f := by
  induction f using Quotient.inductionOn with | _ s =>
  change Q.AbelianSpan Y M at s
  let c := Q.isoSpan (abelianExactStructure C).deflation (abelianExactStructure C).inflation
    e ((abelianExactStructure C).inflation_of_iso e)
  have : IsIso (pullback.snd e.hom s.l) :=
    (IsPullback.of_hasPullback e.hom s.l).isIso_snd_of_isIso
  apply spanLower_eq_of_iso (Span.comp c s) s e (asIso (pullback.snd e.hom s.l))
  · simpa [Span.comp, c, Q.isoSpan] using pullback.condition (f := e.hom) (g := s.l)
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- The upper endpoint is likewise unchanged by source isomorphisms. -/
theorem arrowUpper_comp_iso {X Y M : C} (e : X ≅ Y)
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowUpper (((abelianExactStructure C).qIsoOfIso e).hom ≫ f) = arrowUpper f := by
  induction f using Quotient.inductionOn with | _ s =>
  change Q.AbelianSpan Y M at s
  let c := Q.isoSpan (abelianExactStructure C).deflation (abelianExactStructure C).inflation
    e ((abelianExactStructure C).inflation_of_iso e)
  have : IsIso (pullback.snd e.hom s.l) :=
    (IsPullback.of_hasPullback e.hom s.l).isIso_snd_of_isIso
  exact spanUpper_eq_of_iso (Span.comp c s) s (asIso (pullback.snd e.hom s.l)) rfl

/-- The lower-endpoint invariant respects every invertible Q-arrow, since
such an arrow is proved to arise from an ambient isomorphism. -/
theorem arrowLower_comp_of_isIso {X Y M : C}
    (e : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    [IsIso e]
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowLower (e ≫ f) = arrowLower f := by
  obtain ⟨a, rfl⟩ := exists_iso_of_isIso e
  exact arrowLower_comp_iso a f

/-- The upper-endpoint invariant respects every invertible Q-arrow. -/
theorem arrowUpper_comp_of_isIso {X Y M : C}
    (e : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    [IsIso e]
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowUpper (e ≫ f) = arrowUpper f := by
  obtain ⟨a, rfl⟩ := exists_iso_of_isIso e
  exact arrowUpper_comp_iso a f

/-- A span with arbitrary source, regarded as an object of the unrestricted
Q-inclusion comma category. -/
def allSpanComma {X M : C} (s : Q.AbelianSpan X M) :
    Devissage.QComma (⊤ : ObjectProperty C) M :=
  Devissage.spanComma (⊤ : ObjectProperty C) M (X := ⟨X, trivial⟩) s

/-- The canonical layer presentation is isomorphic to the original span
in the unrestricted inclusion comma category. -/
def allSpanLayerCommaIso {X M : C} (s : Q.AbelianSpan X M) :
    (Devissage.spanLayer (⊤ : ObjectProperty C) s trivial).comma ≅ allSpanComma s :=
  Devissage.spanCommaIsoOfIso (⊤ : ObjectProperty C) M
    (X := ⟨(Devissage.spanLayer (⊤ : ObjectProperty C) s trivial).quotient, trivial⟩)
    (Y := ⟨X, trivial⟩)
    (Devissage.spanLayer (⊤ : ObjectProperty C) s trivial).span s
    (Devissage.spanLayerQuotientIso (⊤ : ObjectProperty C) s trivial)
    (Subobject.underlyingIso s.r)
    (Devissage.cokernel_π_spanLayerQuotientIso_hom (⊤ : ObjectProperty C) s trivial).symm
    (Subobject.underlyingIso_hom_comp_eq_mk s.r)

set_option backward.isDefEq.respectTransparency false in
/-- Equal layer endpoints identify two Q-arrows up to a source Q-isomorphism.
Thus the endpoint invariant is complete, not just an invariant of chosen spans. -/
theorem exists_qIso_of_endpoints_eq {X Y M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (g : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (hl : arrowLower f = arrowLower g) (hu : arrowUpper f = arrowUpper g) :
    ∃ e : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ≅
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y,
      e.hom ≫ g = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  change Q.AbelianSpan X M at s
  change Q.AbelianSpan Y M at t
  have h : Devissage.spanLayer (⊤ : ObjectProperty C) s trivial =
      Devissage.spanLayer (⊤ : ObjectProperty C) t trivial := by
    apply Devissage.Layer.ext
    · exact hl
    · exact hu
  let e : allSpanComma s ≅ allSpanComma t :=
    (allSpanLayerCommaIso s).symm ≪≫
      eqToIso (congrArg (fun A : Devissage.Layer (⊤ : ObjectProperty C) M => A.comma) h) ≪≫
      allSpanLayerCommaIso t
  refine ⟨(Devissage.mapQ (⊤ : ObjectProperty C)).mapIso
    ((CostructuredArrow.proj (Devissage.mapQ (⊤ : ObjectProperty C)) (Q.of _ _ M)).mapIso e), ?_⟩
  exact CostructuredArrow.w e.hom

set_option backward.isDefEq.respectTransparency false in
/-- Factorization of Q-arrows implies the interval order on their endpoints. -/
theorem endpoints_order_of_fac {X Y M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (g : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (k : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    (w : k ≫ g = f) : arrowLower g ≤ arrowLower f ∧ arrowUpper f ≤ arrowUpper g := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  change Q.AbelianSpan X M at s
  change Q.AbelianSpan Y M at t
  let h : allSpanComma s ⟶ allSpanComma t :=
    CostructuredArrow.homMk ((Devissage.mapQ (⊤ : ObjectProperty C)).preimage k) (by
      rw [Functor.map_preimage]
      exact w)
  exact Devissage.Layer.le_of_comma_hom
    ((allSpanLayerCommaIso s).hom ≫ h ≫ (allSpanLayerCommaIso t).inv)

set_option backward.isDefEq.respectTransparency false in
/-- Every inequality of endpoint intervals comes from an actual Q-factorization. -/
theorem exists_factor_of_endpoints_order {X Y M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (g : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (hl : arrowLower g ≤ arrowLower f) (hu : arrowUpper f ≤ arrowUpper g) :
    ∃ k : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y,
      k ≫ g = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  change Q.AbelianSpan X M at s
  change Q.AbelianSpan Y M at t
  have hle : Devissage.spanLayer (⊤ : ObjectProperty C) s trivial ≤
      Devissage.spanLayer (⊤ : ObjectProperty C) t trivial := ⟨hl, hu⟩
  let h : allSpanComma s ⟶ allSpanComma t :=
    (allSpanLayerCommaIso s).inv ≫ Devissage.Layer.commaMap hle ≫
      (allSpanLayerCommaIso t).hom
  exact ⟨(Devissage.mapQ (⊤ : ObjectProperty C)).map h.left, CostructuredArrow.w h⟩

/-- Recovering endpoints from a canonical layer span returns the given layer. -/
theorem spanLayer_span {M : C} (A : Devissage.Layer (⊤ : ObjectProperty C) M) :
    Devissage.spanLayer (⊤ : ObjectProperty C) A.span trivial = A := by
  apply le_antisymm
  · exact Devissage.Layer.le_of_comma_hom (allSpanLayerCommaIso A.span).hom
  · exact Devissage.Layer.le_of_comma_hom (allSpanLayerCommaIso A.span).inv

@[simp]
theorem arrowLower_layerSpan {M : C} (A : Devissage.Layer (⊤ : ObjectProperty C) M) :
    arrowLower (Q.mkHom _ _ A.span) = A.lower :=
  congrArg Devissage.Layer.lower (spanLayer_span A)

@[simp]
theorem arrowUpper_layerSpan {M : C} (A : Devissage.Layer (⊤ : ObjectProperty C) M) :
    arrowUpper (Q.mkHom _ _ A.span) = A.upper :=
  congrArg Devissage.Layer.upper (spanLayer_span A)

set_option backward.isDefEq.respectTransparency false in
/-- A Q-arrow from zero is precisely a subobject: take the monomorphism
forming the right leg of any span representative. -/
def zeroArrowSubobject {M : C}
    (f : (abelianExactStructure C).qZero ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Subobject M := by
  refine Quotient.liftOn f (fun s : Q.AbelianSpan (0 : C) M => Subobject.mk s.r) ?_
  intro s t h
  change Q.AbelianSpan (0 : C) M at s t
  let : Mono s.r := (abelianExactStructure C).mono_of_inflation s.wr
  let : Mono t.r := (abelianExactStructure C).mono_of_inflation t.wr
  obtain ⟨e, _, hr⟩ := (Q.mkHom_eq_iff_apexIso _ _ s t).1 (Quotient.sound h)
  exact Subobject.mk_eq_mk_of_comm _ _ e hr

/-- Present a subobject by the Q-span whose left leg is the map to zero. -/
def zeroArrowOfSubobject {M : C} (S : Subobject M) :
    (abelianExactStructure C).qZero ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M :=
  Q.mkHom _ _ ⟨S, 0, S.arrow, (abelianExactStructure C).deflation_zero _,
    (abelianExactStructure_inflation_iff C _).2 inferInstance⟩

@[simp]
theorem zeroArrowSubobject_ofSubobject {M : C} (S : Subobject M) :
    zeroArrowSubobject (zeroArrowOfSubobject S) = S := Subobject.mk_arrow S

/-- The subobject completely determines the Q-arrow from zero, including its
apex-isomorphism quotient class. -/
theorem zeroArrowSubobject_injective {M : C} :
    Function.Injective (zeroArrowSubobject (C := C) (M := M)) := by
  intro f g h
  induction f using Quotient.inductionOn with | _ s =>
  induction g using Quotient.inductionOn with | _ t =>
  change Subobject.mk s.r = Subobject.mk t.r at h
  apply Q.mkHom_eq_of_apexIso _ _ s t (Subobject.isoOfMkEqMk s.r t.r h)
  · exact (isZero_zero C).eq_of_tgt _ _
  · simp

/-- Actual subobjects classify all Q-arrows from the zero vertex. -/
def zeroArrowSubobjectEquiv (M : C) :
    ((abelianExactStructure C).qZero ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) ≃
      Subobject M where
  toFun := zeroArrowSubobject
  invFun := zeroArrowOfSubobject
  left_inv _ := zeroArrowSubobject_injective (zeroArrowSubobject_ofSubobject _)
  right_inv := zeroArrowSubobject_ofSubobject

/-- Precomposing a span by an original zero-object isomorphism leaves its
classified subobject unchanged: the pullback projection is an isomorphism. -/
theorem zeroArrowSubobject_comp_iso {X M : C} (e : (0 : C) ≅ X)
    (s : Q.AbelianSpan X M) :
    zeroArrowSubobject (((abelianExactStructure C).qIsoOfIso e).hom ≫ Q.mkHom _ _ s) =
      Subobject.mk s.r := by
  have : IsIso (pullback.snd e.hom s.l) :=
    (IsPullback.of_hasPullback e.hom s.l).isIso_snd_of_isIso
  change Subobject.mk (pullback.snd e.hom s.l ≫ s.r) = Subobject.mk s.r
  exact Subobject.mk_eq_mk_of_comm _ _ (asIso (pullback.snd e.hom s.l)) rfl

end Quillen.Q

namespace Quillen.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The genuine quotient Q-functor carries lower layer endpoints by the
surjective exact subobject map. -/
theorem arrowLower_quotientMapQ {X M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Q.arrowLower ((quotientMapQ P).map f) =
      subobjectMap P.isoModSerre.Q P M (Q.arrowLower f) := by
  induction f using Quotient.inductionOn with | _ s =>
  exact (subobjectMap_spanLower P.isoModSerre.Q P s).symm

/-- The quotient Q-functor also carries upper layer endpoints by that map. -/
theorem arrowUpper_quotientMapQ {X M : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Q.arrowUpper ((quotientMapQ P).map f) =
      subobjectMap P.isoModSerre.Q P M (Q.arrowUpper f) := by
  induction f using Quotient.inductionOn with | _ s =>
  exact (subobjectMap_spanUpper P.isoModSerre.Q P s).symm

/-- The genuine target-zero comma category for the canonical quotient Q-map. -/
abbrev ZeroComma := CostructuredArrow (quotientMapQ P) (quotientExactStructure P).qZero

/-- Every source object occurring in the zero comma category belongs to the
Serre class. This is a consequence of the epi/mono legs of its structure arrow. -/
theorem zeroComma_object_mem (X : ZeroComma P) : P X.left.obj.of :=
  (quotient_isZero_obj_iff P X.left.obj.of).1
    ((quotientExactStructure P).isZero_source_of_qHom X.hom (isZero_zero _))

/-- The canonical zero comparison lifts the Q-inclusion to the zero comma
category. The components are exactly the ones used in the localization
nullhomotopy. -/
def serreToZeroComma : (CategoryTheory.ObjectProperty.subcategoryExactStructure P).QCategory ⥤
  ZeroComma P :=
  (Devissage.mapQ P).toCostructuredArrow (quotientMapQ P) _
    (fun X => (quotientInclusionZeroIso P).hom.app X) (fun f => by
      simpa using (quotientInclusionZeroIso P).hom.naturality f)

/-- Forgetting the structure arrow recovers the actual Q-inclusion strictly. -/
@[simp]
theorem serreToZeroComma_projection :
    serreToZeroComma P ⋙ CostructuredArrow.proj (quotientMapQ P)
      (quotientExactStructure P).qZero = Devissage.mapQ P := rfl

instance serreToZeroComma_faithful : (serreToZeroComma P).Faithful where
  map_injective h := (Devissage.mapQ P).map_injective
    (congrArg (fun f => f.left) h)

instance serreToZeroComma_full : (serreToZeroComma P).Full where
  map_surjective f := by
    refine ⟨(Devissage.mapQ P).preimage f.left, ?_⟩
    apply CostructuredArrow.hom_ext
    exact (Devissage.mapQ P).map_preimage f.left

instance serreToZeroComma_essSurj : (serreToZeroComma P).EssSurj where
  mem_essImage X := by
    let Y : (CategoryTheory.ObjectProperty.subcategoryExactStructure P).QCategory :=
      Q.of _ _ ⟨X.left.obj.of, zeroComma_object_mem P X⟩
    refine ⟨Y, ⟨CostructuredArrow.isoMk (Iso.refl _) ?_⟩⟩
    exact ((quotientExactStructure P).qHom_subsingleton_of_isZero _ _
      (isZero_zero _)).elim _ _

/-- The canonical lift of the inclusion is a genuine categorical equivalence. -/
instance serreToZeroComma_isEquivalence : (serreToZeroComma P).IsEquivalence where

/-- The Serre Q-category is equivalent to the actual zero comma category. -/
def zeroCommaEquivalence :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure P).QCategory ≌ ZeroComma P :=
  (serreToZeroComma P).asEquivalence

/-- Realization gives a homotopy equivalence with the canonical comparison
as its forward map, not just an abstract equivalence of homotopy types. -/
def zeroCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace
      (ClassifyingSpace (ZeroComma P)) :=
  equivalenceClassifyingHomotopyEquiv (zeroCommaEquivalence P)

@[simp]
theorem zeroCommaClassifyingHomotopyEquiv_apply
    (x : (CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace) :
    zeroCommaClassifyingHomotopyEquiv P x = classifyingSpaceMap (serreToZeroComma P) x := rfl

/-- The realized comparison lies strictly over the canonical inclusion map. -/
@[simp]
theorem zeroCommaClassifying_projection :
    (classifyingSpaceMap (CostructuredArrow.proj (quotientMapQ P)
      (quotientExactStructure P).qZero)).hom.comp
      (classifyingSpaceMap (serreToZeroComma P)).hom =
    (classifyingSpaceMap (Devissage.mapQ P)).hom := by
  change (classifyingSpaceMap (serreToZeroComma P) ≫
    classifyingSpaceMap (CostructuredArrow.proj (quotientMapQ P)
      (quotientExactStructure P).qZero)).hom = _
  rw [← classifyingSpaceMap_comp, serreToZeroComma_projection]

/-- The comma structure transformation restricts to precisely the canonical
natural zero comparison, so no new choice of nullhomotopy is introduced. -/
@[simp]
theorem serreToZeroComma_transformation :
    Functor.whiskerLeft (serreToZeroComma P)
      (TheoremB.commaTransformation (quotientMapQ P) (quotientExactStructure P).qZero) =
      (quotientInclusionZeroIso P).hom := rfl

/-- The canonical comma homotopy restricts pointwise to the chosen quotient
nullhomotopy, including its complete path coordinate. -/
theorem serreToZeroComma_nullhomotopy (t : unitInterval)
    (x : (CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace) :
    TheoremB.commaNullhomotopy (quotientMapQ P) (quotientExactStructure P).qZero
      (t, classifyingSpaceMap (serreToZeroComma P) x) =
      quotientInclusionNullhomotopy P (t, x) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (TheoremB.commaTransformation (quotientMapQ P) (quotientExactStructure P).qZero)
    (t, classifyingSpaceMap (serreToZeroComma P) x) =
    classifyingSpaceNaturalTransformationHomotopy (quotientInclusionZeroIso P).hom (t, x)
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    serreToZeroComma_transformation]
  rfl

/-- Composing the zero-comma equivalence with Theorem B's canonical comparison
recovers the existing localization-fiber map strictly, both in its projection
and in its path coordinate. -/
theorem serreToZeroComma_fiberComparison :
    (TheoremB.fiberComparison (quotientMapQ P) (quotientExactStructure P).qZero).comp
      (classifyingSpaceMap (serreToZeroComma P)).hom = localizationFiberComparison P := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.congr_fun (zeroCommaClassifying_projection P) x
  · apply ContinuousMap.ext
    intro t
    exact serreToZeroComma_nullhomotopy P t x

/-- The source-zero comma category used in Quillen's original localization
proof. It is distinct from the target-zero comma category above. -/
abbrev ZeroStructuredComma := StructuredArrow (quotientExactStructure P).qZero (quotientMapQ P)

/-- The Serre inclusion lifted to the structured comma category using the
inverse of the same canonical categorical zero comparison. -/
def serreToZeroStructuredComma :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure P).QCategory ⥤ ZeroStructuredComma P :=
  (Devissage.mapQ P).toStructuredArrow (quotientExactStructure P).qZero (quotientMapQ P)
    (fun X => (quotientInclusionZeroIso P).inv.app X) (fun f => by
      simpa using ((quotientInclusionZeroIso P).inv.naturality f).symm)

@[simp]
theorem serreToZeroStructuredComma_projection :
    serreToZeroStructuredComma P ⋙ StructuredArrow.proj
      (quotientExactStructure P).qZero (quotientMapQ P) = Devissage.mapQ P := rfl

/-- Lift categories of arbitrary quotient intervals admit the same concrete
join contraction, as soon as the specified endpoints are nested. -/
theorem subobjectIntervalLift_contractible (M : C)
    (S T : Subobject (P.isoModSerre.Q.obj M)) (h : S ≤ T) :
    ContractibleSpace (ClassifyingSpace (SubobjectIntervalLift P.isoModSerre.Q P M S T)) := by
  let := SubobjectIntervalLift.nonempty (L := P.isoModSerre.Q) (P := P) h
  exact classifyingSpace_contractible_of_semilatticeSup _

/-- The quotient structure arrow associated to an ambient Serre layer. -/
def layerStructureArrow {M : C} (A : Devissage.Layer P M) :
    (quotientExactStructure P).qZero ⟶
      (quotientMapQ P).obj (Q.of (abelianExactStructure C).deflation
        (abelianExactStructure C).inflation M) :=
  (quotientInclusionZeroIso P).inv.app A.comma.left ≫ (quotientMapQ P).map A.comma.hom

/-- A layer's structure arrow is classified by the localized upper endpoint. -/
theorem layerStructureArrow_subobject {M : C} (A : Devissage.Layer P M) :
    Q.zeroArrowSubobject (layerStructureArrow P A) =
      subobjectMap P.isoModSerre.Q P M A.upper := by
  let e := ((quotient_isZero_obj_iff P A.quotient).2 A.property).iso
    (isZero_zero (Quotient P))
  exact Q.zeroArrowSubobject_comp_iso e.symm
    ((quotientExactFunctor P).toQCompatibleFunctor.mapSpan A.span)

/-- Lifts of a fixed quotient subobject by ambient Serre layers. This is the
concrete poset occurring in the structured zero-comma comparison. -/
abbrev ZeroLayerLift (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :=
  {A : Devissage.Layer P M //
    subobjectMap P.isoModSerre.Q P M A.lower = S ∧
    subobjectMap P.isoModSerre.Q P M A.upper = S}

/-- Intersection of lower endpoints and sum of upper endpoints give the
actual join of two lifts of the same quotient subobject. -/
def zeroLayerLiftSup {M : C} {S : Subobject (P.isoModSerre.Q.obj M)}
    (A B : ZeroLayerLift P M S) : ZeroLayerLift P M S := by
  let h : A.val.lower ⊓ B.val.lower ≤ A.val.upper ⊔ B.val.upper :=
    inf_le_left.trans (A.val.le.trans le_sup_left)
  refine ⟨{ lower := A.val.lower ⊓ B.val.lower
            upper := A.val.upper ⊔ B.val.upper
            le := h
            property := cokernel_ofLE_mem_of_subobjectMap_eq P.isoModSerre.Q P h ?_ }, ?_, ?_⟩
  · rw [subobjectMap_inf, subobjectMap_sup, A.property.1, B.property.1,
      A.property.2, B.property.2, inf_idem, sup_idem]
  · simp only [subobjectMap_inf, A.property.1, B.property.1, inf_idem]
  · simp only [subobjectMap_sup, A.property.2, B.property.2, sup_idem]

instance instSemilatticeSupZeroLayerLift (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :
    SemilatticeSup (ZeroLayerLift P M S) where
  sup := zeroLayerLiftSup P
  le_sup_left _ _ := ⟨inf_le_left, le_sup_left⟩
  le_sup_right _ _ := ⟨inf_le_right, le_sup_right⟩
  sup_le _ _ _ h k := ⟨le_inf h.1 k.1, sup_le h.2 k.2⟩

/-- A single ambient subobject lift gives the diagonal Serre layer, so the
layer-lift poset is genuinely nonempty. -/
instance zeroLayerLift_nonempty (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :
    Nonempty (ZeroLayerLift P M S) := by
  obtain ⟨A, hA⟩ := subobjectMap_surjective P.isoModSerre.Q P M S
  let T : Devissage.Layer P M :=
    { lower := A
      upper := A
      le := le_rfl
      property := cokernel_ofLE_mem_of_subobjectMap_eq P.isoModSerre.Q P le_rfl rfl }
  exact ⟨⟨T, hA, hA⟩⟩

/-- The genuine realized layer-lift category is contractible by the explicit
join contraction; categorical connectedness is not used as a substitute. -/
theorem zeroLayerLift_contractible (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :
    ContractibleSpace (ClassifyingSpace (ZeroLayerLift P M S)) :=
  classifyingSpace_contractible_of_semilatticeSup _

/-- The actual comma fiber of the inclusion into the source-zero comma category. -/
abbrev ZeroStructuredFiber (X : ZeroStructuredComma P) :=
  CostructuredArrow (serreToZeroStructuredComma P) X

instance zeroStructuredFiber_thin (X : ZeroStructuredComma P) :
    Quiver.IsThin (ZeroStructuredFiber P X) := by
  intro A B
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  apply (Devissage.mapQ P).map_injective
  apply (cancel_mono B.hom.right).1
  exact (congrArg (fun k => k.right) (CostructuredArrow.w f)).trans
    (congrArg (fun k => k.right) (CostructuredArrow.w g)).symm

/-- A layer lifting the subobject classified by `X.hom` determines an object
of the actual comma fiber, using its quotient-to-ambient Q-span. -/
def zeroLayerToStructuredFiberObj (X : ZeroStructuredComma P)
    (A : ZeroLayerLift P X.right.obj.of (Q.zeroArrowSubobject X.hom)) :
    ZeroStructuredFiber P X :=
  CostructuredArrow.mk (Y := A.val.comma.left)
    (StructuredArrow.homMk A.val.comma.hom (by
      change layerStructureArrow P A.val = X.hom
      apply Q.zeroArrowSubobject_injective
      rw [layerStructureArrow_subobject]
      exact A.property.2))

/-- The actual layer comparison into the comma fiber. -/
def zeroLayerToStructuredFiber (X : ZeroStructuredComma P) :
    ZeroLayerLift P X.right.obj.of (Q.zeroArrowSubobject X.hom) ⥤ ZeroStructuredFiber P X where
  obj := zeroLayerToStructuredFiberObj P X
  map f := CostructuredArrow.homMk (Devissage.Layer.commaMap (leOfHom f)).left (by
    apply StructuredArrow.hom_ext
    exact CostructuredArrow.w (Devissage.Layer.commaMap (leOfHom f)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance zeroLayerToStructuredFiber_faithful (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance zeroLayerToStructuredFiber_full (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).Full where
  map_surjective {A B} f := by
    let g : A.val.comma ⟶ B.val.comma := CostructuredArrow.homMk f.left (by
      exact congrArg (fun k => k.right) (CostructuredArrow.w f))
    exact ⟨homOfLE (Devissage.Layer.le_of_comma_hom g), Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
instance zeroLayerToStructuredFiber_essSurj (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).EssSurj where
  mem_essImage Y := by
    let M := X.right.obj.of
    let Z : Devissage.QComma P M := CostructuredArrow.mk Y.hom.right
    let A := (Devissage.layerToComma P M).objPreimage Z
    let e := (Devissage.layerToComma P M).objObjPreimageIso Z
    have hw : layerStructureArrow P A = X.hom := by
      change (quotientInclusionZeroIso P).inv.app A.comma.left ≫
        (quotientMapQ P).map A.comma.hom = X.hom
      have he : (Devissage.mapQ P).map e.hom.left ≫ Z.hom = A.comma.hom :=
        CostructuredArrow.w e.hom
      rw [← he, Functor.map_comp, ← Category.assoc]
      have hn : (quotientInclusionZeroIso P).inv.app A.comma.left ≫
          (quotientMapQ P).map ((Devissage.mapQ P).map e.hom.left) =
          (quotientInclusionZeroIso P).inv.app Y.left := by
        have hn' := ((quotientInclusionZeroIso P).inv.naturality e.hom.left).symm
        change (quotientInclusionZeroIso P).inv.app A.comma.left ≫
          (quotientMapQ P).map ((Devissage.mapQ P).map e.hom.left) =
          𝟙 _ ≫ (quotientInclusionZeroIso P).inv.app Y.left at hn'
        exact hn'.trans (Category.id_comp _)
      rw [hn]
      exact StructuredArrow.w Y.hom
    have hu : subobjectMap P.isoModSerre.Q P M A.upper = Q.zeroArrowSubobject X.hom := by
      rw [← layerStructureArrow_subobject]
      exact congrArg Q.zeroArrowSubobject hw
    have hl : subobjectMap P.isoModSerre.Q P M A.lower = Q.zeroArrowSubobject X.hom :=
      (subobjectMap_eq_of_cokernel_ofLE_mem P.isoModSerre.Q P A.le A.property).trans hu
    refine ⟨⟨A, hl, hu⟩, ⟨CostructuredArrow.isoMk
      ((CostructuredArrow.proj (Devissage.mapQ P) (Q.of _ _ M)).mapIso e) ?_⟩⟩
    apply StructuredArrow.hom_ext
    exact CostructuredArrow.w e.hom

instance zeroLayerToStructuredFiber_isEquivalence (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).IsEquivalence where

/-- The actual structured-comma fiber is equivalent to the explicitly
contractible layer-lift poset. -/
def zeroStructuredFiberEquivalence (X : ZeroStructuredComma P) :
    ZeroLayerLift P X.right.obj.of (Q.zeroArrowSubobject X.hom) ≌ ZeroStructuredFiber P X :=
  (zeroLayerToStructuredFiber P X).asEquivalence

/-- Every actual comma fiber in the source-zero comparison is contractible. -/
theorem zeroStructuredFiber_contractible (X : ZeroStructuredComma P) :
    ContractibleSpace (ClassifyingSpace (ZeroStructuredFiber P X)) := by
  let := zeroLayerLift_contractible P X.right.obj.of (Q.zeroArrowSubobject X.hom)
  exact (equivalenceClassifyingHomotopyEquiv (zeroStructuredFiberEquivalence P
    X)).symm.contractibleSpace

/-- Quillen's source-zero comma comparison is a genuine homotopy equivalence,
with the canonical inclusion lift as its forward map. -/
def zeroStructuredCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace
      (ClassifyingSpace (ZeroStructuredComma P)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (serreToZeroStructuredComma P)
    (zeroStructuredFiber_contractible P)

@[simp]
theorem zeroStructuredCommaClassifyingHomotopyEquiv_toFun :
    (zeroStructuredCommaClassifyingHomotopyEquiv P).toFun =
      (classifyingSpaceMap (serreToZeroStructuredComma P)).hom := rfl

/-- The isomorphism objects in a quotient structured comma category. -/
def isoStructureProperty (V : (quotientExactStructure P).QCategory) :
    ObjectProperty (StructuredArrow V (quotientMapQ P)) := fun X => IsIso X.hom

/-- The full subcategory of arrows from `V` to `quotientMapQ P` whose structure Q-arrow is an
isomorphism. -/
abbrev IsoStructuredComma (V : (quotientExactStructure P).QCategory) :=
  (isoStructureProperty P V).FullSubcategory

instance isoStructure_arrow_isIso {V : (quotientExactStructure P).QCategory}
    (A : IsoStructuredComma P V) : IsIso A.obj.hom := A.property

/-- Inclusion of the objects whose structure Q-arrow is invertible. -/
@[implicit_reducible]
def isoStructuredInclusion (V : (quotientExactStructure P).QCategory) :
    IsoStructuredComma P V ⥤ StructuredArrow V (quotientMapQ P) :=
  (isoStructureProperty P V).ι

/-- The costructured-arrow category of maps from isomorphism objects to a fixed quotient
structured-comma object `X`; this is the comma fiber of `isoStructuredInclusion P V` over
`X`. -/
abbrev IsoStructuredFiber {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) := CostructuredArrow (isoStructuredInclusion P V) X

/-- The concrete interval-lift model for the comma fiber over `X`. -/
abbrev IsoFiberIntervals {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) :=
  SubobjectIntervalLift P.isoModSerre.Q P X.right.obj.of
    (Q.arrowLower X.hom) (Q.arrowUpper X.hom)

/-- A lifted interval defines its ordinary quotient-to-ambient layer. -/
def isoFiberIntervalLayer {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    Devissage.Layer (⊤ : ObjectProperty C) X.right.obj.of where
  lower := A.lower
  upper := A.upper
  le := A.le
  property := trivial

/-- The actual ambient Q-arrow associated to a lifted interval. -/
def isoFiberIntervalArrow {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      (isoFiberIntervalLayer P A).quotient ⟶ X.right :=
  Q.mkHom _ _ (isoFiberIntervalLayer P A).span

@[simp]
theorem isoFiberIntervalArrow_lower {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    Q.arrowLower (isoFiberIntervalArrow P A) = A.lower := Q.arrowLower_layerSpan _

@[simp]
theorem isoFiberIntervalArrow_upper {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    Q.arrowUpper (isoFiberIntervalArrow P A) = A.upper := Q.arrowUpper_layerSpan _

/-- Completeness of the layer invariant identifies the localized source
with the required base object. This is an actual Q-isomorphism. -/
def isoFiberIntervalSourceIso {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    (quotientMapQ P).obj (Q.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation (isoFiberIntervalLayer P A).quotient) ≅ V :=
  (Q.exists_qIso_of_endpoints_eq ((quotientMapQ P).map (isoFiberIntervalArrow P A)) X.hom
    (by erw [arrowLower_quotientMapQ, isoFiberIntervalArrow_lower]; exact A.map_lower)
    (by erw [arrowUpper_quotientMapQ, isoFiberIntervalArrow_upper]; exact A.map_upper)).choose

/-- The chosen source identification commutes with the structure arrow. -/
lemma isoFiberIntervalSourceIso_hom_comp {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    (isoFiberIntervalSourceIso P A).hom ≫ X.hom =
      (quotientMapQ P).map (isoFiberIntervalArrow P A) :=
  (Q.exists_qIso_of_endpoints_eq ((quotientMapQ P).map (isoFiberIntervalArrow P A)) X.hom
    (by erw [arrowLower_quotientMapQ, isoFiberIntervalArrow_lower]; exact A.map_lower)
    (by erw [arrowUpper_quotientMapQ, isoFiberIntervalArrow_upper]; exact A.map_upper)).choose_spec

/-- An interval lift gives an object of the actual isomorphism-inclusion comma fiber. -/
def isoFiberIntervalObj {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    IsoStructuredFiber P X := by
  let Y : IsoStructuredComma P V :=
    ⟨StructuredArrow.mk (Y := Q.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation (isoFiberIntervalLayer P A).quotient)
      (isoFiberIntervalSourceIso P A).inv, by dsimp [isoStructureProperty]; infer_instance⟩
  exact CostructuredArrow.mk (Y := Y)
    (StructuredArrow.homMk (isoFiberIntervalArrow P A) (by
      change (isoFiberIntervalSourceIso P A).inv ≫
        (quotientMapQ P).map (isoFiberIntervalArrow P A) = X.hom
      rw [← isoFiberIntervalSourceIso_hom_comp]
      simp))

/-- In the actual fiber, the Q-arrow into the fixed target determines every morphism. -/
instance isoStructuredFiber_thin {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : Quiver.IsThin (IsoStructuredFiber P X) := by
  intro A B
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply (cancel_mono B.hom.right).1
  exact (congrArg (fun k => k.right) (CostructuredArrow.w f)).trans
    (congrArg (fun k => k.right) (CostructuredArrow.w g)).symm

set_option backward.isDefEq.respectTransparency false in
/-- An actual ambient Q-factorization uniquely lifts to a morphism of the
isomorphism-inclusion comma fibers. Its structure triangle follows by monicity. -/
def isoStructuredFiberHomMk {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} {A B : IsoStructuredFiber P X}
    (k : A.left.obj.right ⟶ B.left.obj.right) (hk : k ≫ B.hom.right = A.hom.right) : A ⟶ B :=
  CostructuredArrow.homMk (ObjectProperty.homMk (StructuredArrow.homMk k (by
    have : Mono ((quotientMapQ P).map B.hom.right) :=
      Q.abelianQ_mono (C := Quotient P) _
    apply (cancel_mono ((quotientMapQ P).map B.hom.right)).1
    rw [Category.assoc, ← Functor.map_comp, hk]
    exact (StructuredArrow.w A.hom).trans (StructuredArrow.w B.hom).symm)))
    (by apply StructuredArrow.hom_ext; exact hk)

/-- A compatible source Q-isomorphism gives an actual isomorphism of comma fibers. -/
def isoStructuredFiberIsoMk {V : (quotientExactStructure P).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} {A B : IsoStructuredFiber P X}
    (k : A.left.obj.right ≅ B.left.obj.right) (hk : k.hom ≫ B.hom.right = A.hom.right) : A ≅ B where
  hom := isoStructuredFiberHomMk P k.hom hk
  inv := isoStructuredFiberHomMk P k.inv (by rw [← hk]; simp)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The concrete interval comparison, using the actual Q-factorizations
classified by interval inequalities. -/
def intervalToIsoStructuredFiber {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : IsoFiberIntervals P X ⥤ IsoStructuredFiber P X where
  obj := isoFiberIntervalObj P
  map {A B} h := isoStructuredFiberHomMk P
    (Q.exists_factor_of_endpoints_order (isoFiberIntervalArrow P A) (isoFiberIntervalArrow P B)
      (by simpa only [isoFiberIntervalArrow_lower] using (leOfHom h).1)
      (by simpa only [isoFiberIntervalArrow_upper] using (leOfHom h).2)).choose
    (Q.exists_factor_of_endpoints_order (isoFiberIntervalArrow P A) (isoFiberIntervalArrow P B)
      (by simpa only [isoFiberIntervalArrow_lower] using (leOfHom h).1)
      (by simpa only [isoFiberIntervalArrow_upper] using (leOfHom h).2)).choose_spec
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance intervalToIsoStructuredFiber_faithful {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance intervalToIsoStructuredFiber_full {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).Full where
  map_surjective {A B} f := by
    have h := Q.endpoints_order_of_fac (isoFiberIntervalArrow P A) (isoFiberIntervalArrow P B)
      f.left.hom.right (congrArg (fun k => k.right) (CostructuredArrow.w f))
    have hab : A ≤ B := by
      change B.lower ≤ A.lower ∧ A.upper ≤ B.upper
      simpa only [isoFiberIntervalArrow_lower, isoFiberIntervalArrow_upper] using h
    exact ⟨homOfLE hab, Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
instance intervalToIsoStructuredFiber_essSurj {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).EssSurj where
  mem_essImage Y := by
    let : IsIso Y.left.obj.hom := Y.left.property
    let g := Y.hom.right
    have hl : subobjectMap P.isoModSerre.Q P X.right.obj.of (Q.arrowLower g) =
        Q.arrowLower X.hom := by
      calc
        _ = Q.arrowLower ((quotientMapQ P).map g) := (arrowLower_quotientMapQ P g).symm
        _ = Q.arrowLower (Y.left.obj.hom ≫ (quotientMapQ P).map g) :=
          (Q.arrowLower_comp_of_isIso Y.left.obj.hom _).symm
        _ = _ := congrArg Q.arrowLower (StructuredArrow.w Y.hom)
    have hu : subobjectMap P.isoModSerre.Q P X.right.obj.of (Q.arrowUpper g) =
        Q.arrowUpper X.hom := by
      calc
        _ = Q.arrowUpper ((quotientMapQ P).map g) := (arrowUpper_quotientMapQ P g).symm
        _ = Q.arrowUpper (Y.left.obj.hom ≫ (quotientMapQ P).map g) :=
          (Q.arrowUpper_comp_of_isIso Y.left.obj.hom _).symm
        _ = _ := congrArg Q.arrowUpper (StructuredArrow.w Y.hom)
    let A : IsoFiberIntervals P X :=
      { lower := Q.arrowLower g
        upper := Q.arrowUpper g
        le := Q.arrowLower_le_upper g
        map_lower := hl
        map_upper := hu }
    obtain ⟨e, he⟩ := Q.exists_qIso_of_endpoints_eq (isoFiberIntervalArrow P A) g
      (isoFiberIntervalArrow_lower P A) (isoFiberIntervalArrow_upper P A)
    exact ⟨A, ⟨isoStructuredFiberIsoMk P e he⟩⟩

instance intervalToIsoStructuredFiber_isEquivalence {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).IsEquivalence
      where

/-- The actual fiber of the inclusion of isomorphism objects is equivalent
to the concrete join-semilattice of ambient interval lifts. -/
def isoStructuredFiberEquivalence {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) :
    IsoFiberIntervals P X ≌ IsoStructuredFiber P X :=
  (intervalToIsoStructuredFiber P X).asEquivalence

/-- Every actual comma fiber of the isomorphism-object inclusion is
contractible by an explicit join contraction. -/
theorem isoStructuredFiber_contractible {V : (quotientExactStructure P).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) :
    ContractibleSpace (ClassifyingSpace (IsoStructuredFiber P X)) := by
  let := subobjectIntervalLift_contractible P X.right.obj.of
    (Q.arrowLower X.hom) (Q.arrowUpper X.hom) (Q.arrowLower_le_upper X.hom)
  exact (equivalenceClassifyingHomotopyEquiv (isoStructuredFiberEquivalence P
    X)).symm.contractibleSpace

/-- The inclusion of isomorphism objects into any quotient structured comma
category is a genuine homotopy equivalence. This is the first auxiliary lemma
of Quillen's localization proof, with its prescribed inclusion as forward map. -/
def isoStructuredInclusionClassifyingHomotopyEquiv (V : (quotientExactStructure P).QCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (IsoStructuredComma P V))
      (ClassifyingSpace (StructuredArrow V (quotientMapQ P))) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (isoStructuredInclusion P V)
    (isoStructuredFiber_contractible P)

@[simp]
theorem isoStructuredInclusionClassifyingHomotopyEquiv_toFun
    (V : (quotientExactStructure P).QCategory) :
    (isoStructuredInclusionClassifyingHomotopyEquiv P V).toFun =
      (classifyingSpaceMap (isoStructuredInclusion P V)).hom := rfl

end Quillen.SerreLocalization
