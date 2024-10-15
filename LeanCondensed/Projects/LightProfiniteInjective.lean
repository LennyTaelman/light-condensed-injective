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


-- crucial step: disjoint closed subsets in a profinite space can be separated by clopens

lemma clopen_sandwich (Z U : Set X) (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every z ∈ Z has clopen nbhd Vz z ⊆ U
  have h_clopen_nbhd : ∀ z ∈ Z, ∃ V : Set X, IsClopen V ∧ z ∈ V ∧ V ⊆ U := by
    intro z hz
    exact compact_exists_isClopen_in_isOpen hU (hZU hz)
  choose V hV using h_clopen_nbhd
  let Vz : Z → Set X := fun z ↦ V z.val z.property
  -- the V z cover Z
  have h_cover : Z ⊆ Set.iUnion Vz := by
    intro z hz
    rw [Set.mem_iUnion]
    use ⟨z, hz⟩
    exact (hV z hz).2.1
  -- the V z are open and closed
  have h_open : ∀ z : Subtype Z, IsOpen (Vz z) := fun ⟨z, hz⟩ ↦ (hV z hz).1.2
  have h_clopen : ∀ z : Subtype Z, IsClopen (Vz z) := fun ⟨z, hz⟩ ↦ (hV z hz).1
  -- Z is compact
  have h_compact := IsClosed.isCompact hZ
  -- there is a finite subcover
  choose I hI using IsCompact.elim_finite_subcover h_compact Vz h_open h_cover
  -- instance : Finite I := by sorry
  -- let C be the union of the V i
  let C := ⋃ i ∈ I, Vz i
  -- C is clopen
  have h_C_clopen : IsClopen C := by
    apply Set.Finite.isClopen_biUnion
    · exact Finset.finite_toSet I
    · intro i _
      exact h_clopen i
  -- C ⊆ U
  have h_CU : C ⊆ U := by
    apply Set.iUnion_subset
    intro i _
    sorry


  sorry







  -- have h_fin : ∃ I : Finset Z, Z ⊆ Set.iUnion (Vz ∘ Subtype.val) := by sorry

  sorry












-- lemma clopen_separation (Y Z : Set X)
--     (hY : IsClosed Y) (hZ : IsClosed Z) (hYZ : Y ∩ Z = ∅) :
--     ∃ C : Set X, IsClopen C ∧ Y ⊆ C ∧ Z ⊆ Cᶜ := by
--   have hZc : IsOpen Zᶜ := by rw [isOpen_compl_iff]; exact hZ
--   -- the complement Zᶜ can be covered by clopen sets Cx
--   have h : ∀ x : Subtype Zᶜ, ∃ Cx : Set X, IsClopen Cx ∧ x.val ∈ Cx ∧ Cx ⊆ Zᶜ := by
--     intro x
--     exact compact_exists_isClopen_in_isOpen hZc x.property
--   -- choose such Cx for every x in Zᶜ
--   choose Cx hCx using h
--   -- together with the complement of Y we get an open cover of X
--   have h2 : (Set.iUnion Cx) ∪ Yᶜ = Set.univ := by
--     ext x
--     constructor
--     · tauto
--     · intro hx
--       by_cases hYx : x ∈ Y
--       · left

--   -- since X is compact, there is a finite subcover

--   sorry



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
