/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# Pointed cones in `ConvexSpace`s

This file shows a pointed cone is a convex set.
-/

@[expose] public section

section Convexity

namespace PointedCone

open Convexity

section Ring

variable {R M : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
    [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M] {s : Set M}

lemma isConvexSet (P : PointedCone R M) :
    IsConvexSet R (P : Set M) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  rw [sConvexComb_eq_sum w]
  refine P.finsuppSum_mem _ _ (fun i r ↦ r • i) (fun c hc ↦ ?_)
  exact P.smul_mem (w.weights_nonneg c) <| hw (Finsupp.mem_support_iff.mpr hc)

end Ring
