/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.KTheory.MilnorK.K2.FiniteField
public import Quillen.Aglib.KTheory.MilnorK.K2.DVR.TameKernel
public import Mathlib.Algebra.Field.ZMod

/-! Direct Aglib Milnor objects and their two additional downstream theorem leaves. -/
@[expose] public section

noncomputable section

namespace Consumer.MilnorInterfaces

/-- Both public presentations include the smallest finite fields. -/
theorem smallFields :
    Subsingleton (MilnorK.K (ZMod 2) 2) ∧ Subsingleton (MilnorK.K2.Group (ZMod 3)) :=
  ⟨inferInstance, inferInstance⟩

/-- The uniform group is used directly, without rebuilding its presentation. -/
theorem finiteFieldUniform (k : Type*) [Field k] [Finite k] (x : MilnorK.K k 2) :
    x = 0 :=
  MilnorK.k2_eq_zero_of_finite x

/-- The tensor comparison retains the actual field map in independent universes. -/
theorem tensorFieldMap {k l : Type*} [Field k] [Field l] (f : k →+* l)
    (x : MilnorK.K k 2) :
    MilnorK.twoEquiv l (MilnorK.map 2 f x) =
      MilnorK.K2.map f (MilnorK.twoEquiv k x) :=
  MilnorK.twoEquiv_map f x

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A last-slot uniformizer gives the literal residue of the first ring-unit coordinate. -/
theorem orderedResidue {π : R} (hπ : Irreducible π) (a : Fin 1 → Rˣ) :
    MilnorK.DVR.residue R K 1
        (MilnorK.symbol (Fin.snoc (MilnorK.K2.DVR.fieldUnits R K ∘ a)
          (MilnorK.K2.DVR.uniformizer (K := K) hπ))) =
      MilnorK.symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) :=
  MilnorK.DVR.residue_ring_units_uniformizer R K hπ 1 a

/-- The uniform kernel uses the supplied marked comparison and the original unit-symbol span. -/
theorem uniformKernel :
    (MilnorK.DVR.residue R K 1).ker =
      (MilnorK.K2.DVR.unitSymbolSpan R K).comap (MilnorK.twoEquiv K).toLinearMap :=
  MilnorK.DVR.ker_residue_one_eq_unitSymbolSpan_comap R K

end Consumer.MilnorInterfaces
