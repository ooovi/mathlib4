/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Geometry.Convex.Hull
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

lemma isConvexSet (P : PointedCone R M) : IsConvexSet R (P : Set M) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  rw [sConvexComb_eq_sum w]
  refine P.finsuppSum_mem _ _ (fun i r ↦ r • i) (fun c hc ↦ ?_)
  exact P.smul_mem (w.weights_nonneg c) <| hw (Finsupp.mem_support_iff.mpr hc)

@[coe]
def toConvexSet (P : PointedCone R M) : ConvexSet R M := ⟨_, P.isConvexSet⟩

instance : Coe (PointedCone R M) (ConvexSet R M) := ⟨toConvexSet⟩

@[simp] theorem hull_convexHull (t : Set M) :
    hull R (Convexity.convexHull R t) = hull R t := by
  apply le_antisymm
  · exact sInf_le <| Convexity.convexHull_min subset_hull (isConvexSet _)
  · exact Submodule.span_mono Convexity.subset_convexHull_self

end Ring

end PointedCone
