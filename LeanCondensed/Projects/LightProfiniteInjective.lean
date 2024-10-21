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


-- For every closed ⊆ open in a profinite, there is an intermediate clopen

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
  exact ⟨C, h_C_clopen, by tauto, by aesop⟩




lemma fin_clopen_separation (n : ℕ) (Z : Fin n → Set X) (U : Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (Z_disj : ∀ i j, i ≠ j → (Z i) ∩ (Z j) = ∅ )
    (U_open : IsOpen U) (hZU : ∀ i, Z i ⊆ U) :
    ∃ C : Fin n → Set X, ∀ i, IsClopen (C i) ∧ Z i ⊆ C i ∧ C i ⊆ U ∧
    ∀ i j, i ≠ j → C i ∩ C j = ∅ := by
  induction' n with n ih generalizing U
  · use fun i => ∅ -- can use junk, domain is empty
    intro i; apply Fin.elim0 i
  · -- let Z' be the restriction along succ : Fin n → Fin (n+1)
    let Z' : Fin n → Set X := fun i ↦ Z (Fin.succ i)
    have Z'_closed : ∀ i, IsClosed (Z' i) := fun i ↦ Z_closed (Fin.succ i)
    have Z'_disj : ∀ i j, i ≠ j → (Z' i) ∩ (Z' j) = ∅ := fun i j hij =>
      Z_disj (Fin.succ i) (Fin.succ j) (fun h ↦ hij (Fin.succ_inj.1 h))
    -- find Z0 ⊆ V ⊆ U disjoint from the Zi with i>0
    let V : Set X  := U \ (⋃ (i : Fin n), Z' i)
    have V_open : IsOpen V := IsOpen.sdiff U_open (isClosed_iUnion_of_finite Z'_closed)
    have Z0_in_V : Z 0 ⊆ V := by
      apply Set.subset_diff.mpr
      constructor
      · exact hZU 0
      · apply Set.disjoint_iUnion_right.mpr
        intro i
        apply Set.disjoint_iff_inter_eq_empty.mpr
        apply Z_disj
        exact Ne.symm (Fin.succ_ne_zero i)
    have V_disj_Z' : ∀ i : Fin n, Disjoint V (Z' i) := by
      intro i
      have h : Z i.succ ⊆ ⋃ (i : Fin n), Z (Fin.succ i) := Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
      exact Disjoint.mono_right h Set.disjoint_sdiff_left
    -- pick clopen Z0 ⊆ C0 ⊆ V
    choose C0 hC0 using clopen_sandwich X (Z 0) V (Z_closed 0) V_open Z0_in_V
    -- now let W be the complement of C0,
    let W : Set X := C0ᶜ
    have W_open : IsOpen W := isOpen_compl_iff.mpr hC0.1.1
    have Z'_in_W : ∀ i : Fin n, Z' i ⊆ W := by
      intro i
      apply Disjoint.subset_compl_left
      exact Disjoint.mono_left hC0.2.2 (V_disj_Z' i)
    -- use induction hypothesis to choose Z i ⊆ Ci ⊆ W clopen and mutually disjoint for i>0
    choose Ci hCi using ih Z' W Z'_closed Z'_disj W_open Z'_in_W
    -- now define C succ i = Ci i and C 0 = C0
    -- bah, disjointness might be a messy case distinction. Maybe change all ≠ to < ???


    sorry




-- can now prove key extension lemma for functions to nonempty finite sets

lemma to_discrete_lifts_along_injective_profinite
    (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [Nonempty S] [fin : Finite S]
    (X Y : Profinite.{u}) (f : X → Y) (f_cont: Continuous f) (f_inj: Function.Injective f)
    (g : X → S) (g_cont : Continuous g) :
    ∃ h : Y → S, (h ∘ f = g) ∧ (Continuous h) := by
  -- let Z s be the inverse image of s
  let Z : S → Set X := fun s ↦ g ⁻¹' {s}
  have hZ : ∀ s, IsClosed (Z s) := by
    intro s
    apply IsClosed.preimage g_cont isClosed_singleton
  -- let Z' s be the union of all the  Z t with t ≠ s
  let Z' : S → Set X := fun s ↦ ⋃ t ≠ s, Z t
  have hZ' : ∀ s, IsClosed (Z' s) := by
    intro s
    refine Set.Finite.isClosed_biUnion ?hs fun i a ↦ hZ i
    exact Set.toFinite fun t ↦ t = s → False
  -- let U s be the complement of Z' s
  let U : S → Set X := fun s ↦ (Z' s)ᶜ
  have hU : ∀ s, IsOpen (U s) := by
    intro s
    exact IsClosed.isOpen_compl
  sorry

  -- write Y as lim Y_i with Y_i discrete




-- this is the target theorem!
theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  constructor
  intro X Y f g h
  -- write
  sorry
