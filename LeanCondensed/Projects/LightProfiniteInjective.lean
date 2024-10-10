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




-- key extension lemma in topology
lemma to_discrete_lifts_along_injective_profinite
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [Nonempty S]
  (X Y : Profinite.{u}) (f : X → Y) (f_cont: Continuous f) (f_inj: Function.Injective f)
  (g : X → S) (g_cont : Continuous g) :
  ∃ h : Y → S, (h ∘ f = g) ∧ (Continuous h) := by
  -- write Y as lim Y_i with Y_i discrete
  have Y_fin : DiscreteQuotient Y ⥤ TopCat.{u} := Y.diagram ⋙ Profinite.toTopCat
  -- for ever i in DiscreteQuotient Y we have that Y_i is discrete
  have Y_fin_discrete : ∀ Z : DiscreteQuotient Y, Discrete (Y_fin.obj Z) := by
    intro Z

    sorry

  #check Y_fin.obj
  #check Y_fin.map


  -- define X_i = im(X→Y→Y_i)
  def X_fin : DiscreteQuotient Y ⥤ FintypeCat.{u} where
    obj Z := Y_fin.obj Z
    map f := Y_fin.map f
    map_comp f g := sorry
    map_id Z := sorry


  -- show X → lim X_i is iso

  -- there exists i such that g : X → S factors over X_i → S

  -- now build h : Y → S via Y → Y_i → S

  sorry




-- this is the target theorem!
theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  constructor
  intro X Y f g h
  -- write
  sorry

end LightProfinite
