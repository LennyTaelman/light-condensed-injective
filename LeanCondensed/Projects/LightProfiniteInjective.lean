/-
Authors: Lenny Taelman
-/
import Mathlib.CategoryTheory.Preadditive.Injective
-- import Mathlib.CategoryTheory.FinCategory
import Mathlib.Topology.Category.LightProfinite.Sequence
-- import LeanCondensed.Mathlib.Condensed.Light.Limits
/-!

# Project: show that non-empty light profinite spaces are injective in all profinite spaces

This is used in particular in the proof the the null sequence module is projective
in light abelian condensed sets.

-/
noncomputable section

universe u

open CategoryTheory LightProfinite OnePoint Limits

namespace LightProfinite

lemma bla (X Y : Profinite.{u}) : ∃ f : X → Y, Continuous f := sorry



-- key factorization lemma in topology
lemma to_discrete_lifts_along_injective_profinite
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [Nonempty S]
  (X Y : Profinite.{u}) (f : X → Y) (f_cont: Continuous f) (f_inj: Function.Injective f)
  (g : X → S) (g_cont : Continuous g) :
  ∃ h : Y → S, (h ∘ f = g) ∧ (Continuous h) := by
  -- write X and Y as compatible limits of finite sets

  sorry




-- this is the target theorem!
theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  constructor
  intro X Y f g h
  -- write
  sorry

end LightProfinite
