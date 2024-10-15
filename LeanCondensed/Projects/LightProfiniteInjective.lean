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


variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]


-- For every closed ⊆ open in a profinite, there is intermediate clopen

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

  -- there is a finite subcover, let C be its union
  have h_compact := IsClosed.isCompact hZ
  choose I hI using IsCompact.elim_finite_subcover h_compact Vz h_open h_cover
  let C := ⋃ (i ∈ I), Vz i

  -- C is clopen
  have h_C_clopen : IsClopen C := by
    apply Set.Finite.isClopen_biUnion
    · exact Finset.finite_toSet I
    · intro i _
      exact h_clopen i

  -- done; C is the desired clopen set
  exact ⟨C, h_C_clopen, by tauto, by aesop⟩



-- can now prove key extension lemma for functions to nonempty finite sets

lemma to_discrete_lifts_along_injective_profinite
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [Nonempty S] [Finite S]
  (X Y : Profinite.{u}) (f : X → Y) (f_cont: Continuous f) (f_inj: Function.Injective f)
  (g : X → S) (g_cont : Continuous g) :
  ∃ h : Y → S, (h ∘ f = g) ∧ (Continuous h) := by
  -- let Z s be the inverse image of s
  let Z : S → Set X := fun s ↦ g ⁻¹' {s}
  have hZ : ∀ s, IsClosed (Z s) := by
    intro s
    apply IsClosed.preimage g_cont isClosed_singleton
  -- let U s be the complememnt of all the  Z t with t ≠ s



  sorry
  -- write Y as lim Y_i with Y_i discrete




-- this is the target theorem!
theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  constructor
  intro X Y f g h
  -- write
  sorry
