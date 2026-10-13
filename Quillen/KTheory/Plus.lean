/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionPositiveKNaturality
public import Quillen.KTheory.Plus.ProjectiveCompletionZeroLoops
public import Quillen.KTheory.Plus.ProjectiveCompletionZerothHomotopy
public import Quillen.KTheory.Plus.ProjectiveTelescopeKZero
public import Quillen.KTheory.Plus.StableGeneralLinearPlus

/-!
# Ring-specific plus construction and Quillen comparison

This selected entrypoint exposes the stable general linear plus certificate,
the completion-to-original-Q loop and positive K-group comparisons, their
ring-change naturality, and the separate zeroth-homotopy and virtual K-zero
interfaces. The construction applies to arbitrary rings using right modules;
the plus certificate states its local-coefficient universe explicitly.
-/

@[expose] public section
