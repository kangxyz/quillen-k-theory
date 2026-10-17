/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0OuterBridge

/-!
# Actual common-unit transport of all five J0 outer nodes

The original geometric and normalization unit squares transport the whole old and new
three-node families, including raw intermediates. The accepted coefficient unit equation
then identifies their source action with the actual commonUnit, retaining the original
reference anchors and entire shifted movement word.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open Quillen.FunctorIdentityAutomorphism
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0ShiftedBridge
open BassH0Merge CommonReferenceNerve LaurentUnitReferenceSpecialization
open CoefficientBassPositiveJ0OuterBridge

private theorem prism_shift {V W : Model.{v}} (F G H : V ⟶ W)
    (e : F.functor ≅ G.functor) (n : G.functor ≅ H.functor)
    (α : F.functor ≅ F.functor) (β : G.functor ≅ G.functor)
    (δ : H.functor ≅ H.functor)
    (he : e.hom ≫ β.hom = α.hom ≫ e.hom)
    (hn : β.hom ≫ n.hom = n.hom ≫ δ.hom) (i : Fin 3) :
    anchorNode α (UnitPrismNodes.nodes F G H e n α β δ (Fin.castAdd 3 i)) =
      UnitPrismNodes.nodes F G H e n α β δ (Fin.natAdd 3 i) := by
  have he' : α ≪≫ e = e ≪≫ β := Iso.ext he.symm
  have hn' : β ≪≫ n = n ≪≫ δ := Iso.ext hn
  fin_cases i
  · change (⟨F, α ≪≫ Iso.refl _⟩ : Node F) = ⟨F, α⟩
    rw [Iso.trans_refl]
  · change (⟨G, α ≪≫ e⟩ : Node F) = ⟨G, e ≪≫ β⟩
    exact congrArg (fun ρ ↦ (⟨G, ρ⟩ : Node F)) he'
  · change (⟨H, α ≪≫ (e ≪≫ n)⟩ : Node F) = ⟨H, (e ≪≫ n) ≪≫ δ⟩
    apply congrArg (fun ρ ↦ (⟨H, ρ⟩ : Node F))
    calc
      α ≪≫ (e ≪≫ n) = (α ≪≫ e) ≪≫ n := (Iso.trans_assoc _ _ _).symm
      _ = (e ≪≫ β) ≪≫ n := congrArg (fun ρ ↦ ρ ≪≫ n) he'
      _ = e ≪≫ (β ≪≫ n) := Iso.trans_assoc _ _ _
      _ = e ≪≫ (n ≪≫ δ) := congrArg (fun ρ ↦ e ≪≫ ρ) hn'
      _ = (e ≪≫ n) ≪≫ δ := (Iso.trans_assoc _ _ _).symm

private theorem anchor_square {V W : Model.{v}} {F G : V ⟶ W}
    (α : F.functor ≅ F.functor) (ε : F.functor ≅ G.functor)
    (β : G.functor ≅ G.functor) (h : α ≪≫ ε = ε ≪≫ β) (N : Node G) :
    anchorNode α (anchorNode ε N) = anchorNode ε (anchorNode β N) := by
  rcases N with ⟨H, ρ⟩
  change (⟨H, α ≪≫ (ε ≪≫ ρ)⟩ : Node F) = ⟨H, ε ≪≫ (β ≪≫ ρ)⟩
  apply congrArg (fun ν ↦ (⟨H, ν⟩ : Node F))
  exact (Iso.trans_assoc _ _ _).symm.trans
    ((congrArg (fun ν ↦ ν ≪≫ ρ) h).trans (Iso.trans_assoc _ _ _))

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

/-- The actual old source unit, with its original scalar pullback and chosen-zero conjugation. -/
def sourceUnit := UnitTrackPostcompSimplex.sourceUnit
  (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a) (laurentUnit P a)

/-- All old raw and normalized nodes shift using the original two commuting unit squares. -/
theorem old_shift (i : Fin 3) :
    anchorNode (sourceUnit P w)
      (CoefficientLaurentUnitTenNodes.oldNodes P w (Fin.castAdd 3 i)) =
      CoefficientLaurentUnitTenNodes.oldNodes P w (Fin.natAdd 3 i) :=
  prism_shift _ _ _ _ _ _ _ _
    (UnitTrackPostcompSimplex.small_geometric_unit _ _ _)
    (UnitTrackPostcompSimplex.small_normalization_unit _ _ _) i

/-- All new nodes shift through precisely the existing sourceIso unit-naturality square. -/
theorem new_shift (i : Fin 3) :
    anchorNode (sourceUnit P w)
      (CoefficientLaurentUnitTenNodes.newNodes P w (Fin.castAdd 3 i)) =
      CoefficientLaurentUnitTenNodes.newNodes P w (Fin.natAdd 3 i) := by
  have h := anchor_square (sourceUnit P w) (CoefficientLaurentUnitTenNodes.sourceIso P w)
    (UnitTrackPrecompSimplex.sourceUnit (laurentProjection P b) (coefficientMap P w)
      (laurentUnit P b)) (CoefficientLaurentUnitTenNodes.source_unit_reference P w)
    (CoefficientLaurentUnitTenNodes.newNativeNodes P w (Fin.castAdd 3 i))
  exact h.trans (congrArg (anchorNode (CoefficientLaurentUnitTenNodes.sourceIso P w))
    (prism_shift _ _ _ _ _ _ _ _
      (UnitTrackPrecompSimplex.small_geometric_unit _ _ _)
      (UnitTrackPrecompSimplex.small_normalization_unit _ _ _) i))

/-- The original pulled Laurent unit equals the prescribed target unit before any normalization. -/
theorem sourceUnit_action : sourceUnit P w =
    onFunctor (CoefficientLaurentUnitTenNodes.source P w).functor (smallUnit P b) := by
  unfold sourceUnit UnitTrackPostcompSimplex.sourceUnit UnitTrackPostcompSimplex.sourceUnitIso
  change isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((boundedFlatPullbackNormalizationIso _).symm ≪≫
      boundedFlatPerfectPullbackUnitIso _ (Units.map
        (coefficientMap P ((laurentUnderFunctor R).map w)).appTop.hom.toMonoidHom
        (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
          (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))) ≪≫
      boundedFlatPullbackNormalizationIso _) AsSmall.up) = _
  rw [boundedFlatCoefficientLaurentUnit_coefficient]
  exact GlobalUnitReferenceNaturality.normalizedModelUnit_eq_onFunctor
    (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj b)) _ _

/-- The shifted five-node ordered face, distinct from the entire lower five-node face. -/
def unitShiftedFace : ⦋4⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7, 8, 9], by decide⟩

/-- Every one of the five full lower references shifts to its prescribed original upper node. -/
theorem five_shift (i : Fin 5) :
    anchorNode (sourceUnit P w)
      (CoefficientLaurentUnitTenNodes.nodes P w (unitLowerFace.toOrderHom i)) =
      CoefficientLaurentUnitTenNodes.nodes P w (unitShiftedFace.toOrderHom i) := by
  fin_cases i
  · exact old_shift P w 0
  · exact old_shift P w 1
  · exact old_shift P w 2
  · exact new_shift P w 1
  · exact new_shift P w 2

variable {c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Actual commonUnit intertwines every supplied full original total reference. -/
private theorem common_source_square (w : a ⟶ c)
    (ε : (BassOverlap.commonReference P p q).functor ≅
      (CoefficientLaurentUnitTenNodes.source P w).functor) :
    commonUnit P p q ≪≫ ε = ε ≪≫ sourceUnit P w := by
  rw [commonUnit_eq_action, sourceUnit_action]
  exact GlobalUnitReferenceNaturality.reference_intertwine
    (op P, (laurentUnderFunctor R).obj c) (laurentUnit P c) _ _ ε

/-- Full raw-to-shifted-node bridge, before applying native evaluation or forgetting references. -/
theorem anchored_five_shift (w : a ⟶ c)
    (ε : (BassOverlap.commonReference P p q).functor ≅
      (CoefficientLaurentUnitTenNodes.source P w).functor) (i : Fin 5) :
    anchorNode (commonUnit P p q)
      (anchorNode ε (BassH0Diagram.nodes P w (rawOuterFace.toOrderHom i))) =
      anchorNode ε
        (CoefficientLaurentUnitTenNodes.nodes P w (unitShiftedFace.toOrderHom i)) := by
  rw [outer_nodes]
  exact (anchor_square (commonUnit P p q) ε (sourceUnit P w)
    (common_source_square P p q w ε) _).trans (congrArg (anchorNode ε) (five_shift P w i))

/-- Whole unchanged shifted movement word, including its inverse and both original binary paths. -/
theorem shifted_word (s : I) : embed unitShiftedFace (outerWord s) =
    (CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1) s :=
  map_trans_values (embed unitShiftedFace) _ _ _ _
    (fun t ↦ map_binaryPath unitShiftedFace 0 1 2 (unitInterval.symm t))
    (map_binaryPath unitShiftedFace 0 3 4) s

/-- Entire original shifted raw movement matches the actual shifted unit-pasting boundary. -/
theorem anchored_shifted_parameter (w : a ⟶ c)
    (ε : (BassOverlap.commonReference P p q).functor ≅
      (CoefficientLaurentUnitTenNodes.source P w).functor) (s : I) :
    mapParameter (anchorNode (commonUnit P p q))
      (mapParameter (anchorNode ε)
        (parameter (BassH0Diagram.reference P w) (BassH0Diagram.nodes P w)
          (ProjectionRectangleParameters.T BassH0Diagram.plusFace s))) =
    mapParameter (anchorNode ε)
      (parameter (CoefficientLaurentUnitTenNodes.source P w)
        (CoefficientLaurentUnitTenNodes.nodes P w)
        ((CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1) s)) := by
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    ← raw_outer_word, ← shifted_word]
  change parameter (BassOverlap.commonReference P p q)
      (fun i ↦ anchorNode (commonUnit P p q) (anchorNode ε (BassH0Diagram.nodes P w i)))
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (BassOverlap.commonReference P p q)
      (fun i ↦ anchorNode ε (CoefficientLaurentUnitTenNodes.nodes P w i))
      (StdSimplex.map unitShiftedFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → Node (BassOverlap.commonReference P p q) ↦
    parameter _ N (outerWord s)) (funext (anchored_five_shift P p q w ε))

/-- Actual direct-l five-node bridge uses the prescribed p;q=l anchor, not an arbitrary cast. -/
theorem actual_five_shift (d : Under R) (i : Fin 5) :
    anchorNode (commonUnit P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d))
      (anchorNode (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d))
        (BassH0Diagram.nodes P ((laurentUnderCoefficient R).app d)
          (rawOuterFace.toOrderHom i))) =
    anchorNode (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d))
      (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d)
        (unitShiftedFace.toOrderHom i)) :=
  anchored_five_shift P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
    ((laurentUnderCoefficient R).app d) _ i

/-- Actual direct-l whole shifted word, with the original source equality and forward unit. -/
theorem actual_shifted_parameter (d : Under R) (s : I) :
    mapParameter (anchorNode
      (commonUnit P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)))
      (mapParameter (anchorNode
        (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d)))
        (parameter (BassH0Diagram.reference P ((laurentUnderCoefficient R).app d))
          (BassH0Diagram.nodes P ((laurentUnderCoefficient R).app d))
          (ProjectionRectangleParameters.T BassH0Diagram.plusFace s))) =
    mapParameter (anchorNode
      (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d)))
      (parameter (CoefficientLaurentUnitTenNodes.source P ((laurentUnderCoefficient R).app d))
        (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d))
        ((CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1) s)) :=
  anchored_shifted_parameter P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
    ((laurentUnderCoefficient R).app d) _ s

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0ShiftedBridge
