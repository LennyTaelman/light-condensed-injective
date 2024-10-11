/-
Authors: Lenny Taelman
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import LeanCondensed.Mathlib.Condensed.Light.Limits
/-!

# Project: show that non-empty light profinite spaces are injective in all profinite spaces

This is used in particular in the proof the the null sequence module is projective
in light abelian condensed sets.

-/
noncomputable section

universe u

open CategoryTheory LightProfinite Limits

-- SCRATCHPAD START


-- moving from objects in TopCat.{u} to topological spaces and back

variable (X : TopCat.{u})


#check Bundled.α X
#check TopCat.of (Bundled.α X)

def sanity : X ≅ TopCat.of (Bundled.α X) where
  hom := 𝟙 X
  inv := 𝟙 X

-- from morphism to continuous map

variable (Y : TopCat.{u}) (f : X ⟶ Y)
#check f.toFun
instance cont_f : Continuous f.toFun := by continuity

-- from continuous map to morphism
variable (X_0 Y_0 : Type u) [TopologicalSpace X_0] [TopologicalSpace Y_0]
variable (g : C(X_0, Y_0))
#check g -- g : C(X_0, Y_0)
#check g.toFun -- g.toFun : X_0 → Y_0

#check TopCat.of X_0
#check (g : TopCat.of X_0 ⟶ TopCat.of Y_0)


-- image of a morphism in TopCat.{u}
variable (X Y : Profinite.{u}) (f : X ⟶ Y)
-- #check (inferInstance : HasImage f)

-- fails to synthesize, so let's work concretely
-- goal: produce a subtype S of
variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
variable (T : DiscreteQuotient Y)
#check (T.proj : Y → T)
#check T.toSetoid


#check T












#print inferInstance


open MonoFactorisation

def mf := MonoFactorisation f
#check (mf X Y f)

#check mf.I
#check mf.e
#check mf.m
#check mf.fac













-- underlying discrete space of S




-- implement range of f
def fund : X → Y := f
#check f
#check (f: X→ Y)

def range (f : X ⟶ Y) : Set Y := { y | ∃ x, f x = y }


variable (S T : DiscreteQuotient Y) (g : S ⟶ T)
#check S
#check g
#check (S : Type u)




-- SCRATCHPAD END


/- given continuous map f : X → Y of profinite spaces,
  with Y = lim Y_i the canonical diagram of Y,
  produce a diagram of X with X_i = im(X → Y → Y_i)
  and a map X → lim X_i compatible with f -/

def diagram_of_injection {X Y : Profinite.{u}} (f : X → Y) (f_cont: Continuous f) :
    DiscreteQuotient Y ⥤ Type u where
  obj S := Set.range (S.proj ∘ f)
  map {S T} g := λ x ↦ g (f x)

-- having difficulty formalizing this. TODO: find baby case, split up in smaller problems
-- minimal example?



/- if moreover f is injective, then the map X → lim X_i is an iso -/



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
