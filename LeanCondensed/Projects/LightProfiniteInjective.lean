/-
Authors: Lenny Taelman
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Condensed.Discrete.Basic
import Mathlib.Topology.Category.LightProfinite.Sequence
import LeanCondensed.Mathlib.Condensed.Light.Limits
import LeanCondensed.Projects.InternallyProjective
/-!

# Project: show that non-empty light profinite spaces are injective in all profinite spaces

This is used in particular in the proof the the null sequence module is projective
in light abelian condensed sets.

-/
noncomputable section

universe u

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory MonoidalClosed

namespace LightProfinite

-- this is the target theorem!
theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  sorry

end LightProfinite
