/-
Authors: Lenny Taelman
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Topology.Separation
import LeanCondensed.Mathlib.Condensed.Light.Limits

/-!

# Project: show that non-empty light profinite spaces are injective in all profinite spaces

This is used in particular in the proof the the null sequence module is projective
in light abelian condensed sets.

-/

noncomputable section

universe u

open CategoryTheory LightProfinite Profinite Limits Topology

-- SCRATCHPAD START

-- some point-set topology first

-- let X be a profinite topological space

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]


open Classical


-- crucial step: disjoint closed subsets in a profinite space can be separated by clopens

lemma clopen_separation (Y Z : Set X)
    (hY : IsClosed Y) (hZ : IsClosed Z) (hYZ : Y ∩ Z = ∅) :
    ∃ C : Set X, IsClopen C ∧ Y ⊆ C ∧ Z ⊆ Cᶜ := by
  have Zc_open : IsOpen Zᶜ := by rw [isOpen_compl_iff]; exact hZ
  -- the complement Zᶜ can be covered by clopen sets Cx
  have h : ∀ x : X,  x ∈ Zᶜ → (∃ Cx : Set X, IsClopen Cx ∧ x ∈ Cx ∧ Cx ⊆ Zᶜ) := by
    intro x
    exact compact_exists_isClopen_in_isOpen Zc_open
  -- produce an open cover
  let I : Type u := Subtype Zᶜ ⊕ PUnit
  let U : I → Set X
    | Sum.inl ⟨x, hx⟩ => Classical.choice (nonempty_of_exists (h x hx))
    | Sum.inr _ => Yᶜ
  -- prove that it is a cover
  have h2 : (⋃ i, U i) = Set.univ := by
    ext x
    constructor
    · tauto
    · intro hx
      by_cases h : x ∈ Z
      · apply Set.mem_iUnion.2
        use Sum.inr PUnit.unit
        dsimp [U]
        simp

        intro h2


        sorry
      · sorry

  -- since X is compact, there is a finite subcover

  sorry


-- version with finitely many closed sets



-- can now prove key extension lemma

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
