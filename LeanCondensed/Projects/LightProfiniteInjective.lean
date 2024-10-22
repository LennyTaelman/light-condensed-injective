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

open CategoryTheory LightProfinite Profinite Limits Topology Set


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
  have V_cover : Z ⊆ iUnion Vz := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV z hz).2.1⟩
  -- the V z are open and closed
  have V_open : ∀ z : Subtype Z, IsOpen (Vz z) := fun ⟨z, hz⟩ ↦ (hV z hz).1.2
  have V_clopen : ∀ z : Subtype Z, IsClopen (Vz z) := fun ⟨z, hz⟩ ↦ (hV z hz).1
  -- there is a finite subcover, let C be its union
  have Z_compact := IsClosed.isCompact hZ
  choose I hI using IsCompact.elim_finite_subcover Z_compact Vz V_open V_cover
  let C := ⋃ (i ∈ I), Vz i
  -- C is clopen
  have C_clopen : IsClopen C := by
    apply Finite.isClopen_biUnion
    · exact Finset.finite_toSet I
    · intro i _
      exact V_clopen i
  -- this C does the job
  exact ⟨C, C_clopen, by tauto, by aesop⟩


/- every finite family of disjoint closed contained in an open U can
   be separated by disjoint clopens contained in U
-/

open Fin

lemma fin_clopen_separation (n : ℕ) (Z : Fin n → Set X) (U : Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) )
    (U_open : IsOpen U) (hZU : ∀ i, Z i ⊆ U) :
    ∃ C : Fin n → Set X, (∀ i, IsClopen (C i) ∧ Z i ⊆ C i ∧ C i ⊆ U) ∧
    ∀ i j, i < j → Disjoint (C i) (C j) := by
  induction' n with n ih generalizing U
  · exact ⟨fun _ ↦ ∅, fun i ↦ elim0 i, fun i ↦ elim0 i ⟩
  · -- for induction step, let Z' be the restriction of Z along succ : Fin n → Fin (n+1)
    let Z' : Fin n → Set X := fun i ↦ Z (succ i)
    have Z'_closed : ∀ i, IsClosed (Z' i) := fun i ↦ Z_closed (succ i)
    have Z'_disj : ∀ i j, i < j → Disjoint (Z' i) (Z' j)  := fun i j hij =>
      Z_disj (succ i) (succ j) (succ_lt_succ_iff.mpr hij)
    -- find Z0 ⊆ V ⊆ U disjoint from the Zi with i>0
    let V : Set X  := U \ (⋃ (i : Fin n), Z' i)
    have V_open : IsOpen V := IsOpen.sdiff U_open (isClosed_iUnion_of_finite Z'_closed)
    have Z0_subset_V : Z 0 ⊆ V := by
      apply subset_diff.mpr
      constructor
      · exact hZU 0
      · exact disjoint_iUnion_right.mpr (fun i ↦ Z_disj 0 (succ i) (succ_pos i))
    have Z'_disj_V : ∀ i : Fin n, Disjoint (Z' i) V := by
      intro i
      exact Disjoint.mono_left (subset_iUnion_of_subset i fun ⦃x⦄ hx ↦ hx) disjoint_sdiff_right
    -- pick clopen Z0 ⊆ C0 ⊆ V
    choose C0 hC0 using clopen_sandwich X (Z 0) V (Z_closed 0) V_open Z0_subset_V
    -- now let W be the complement of C0
    let W : Set X := U \ C0
    have W_open : IsOpen W := IsOpen.sdiff U_open hC0.1.1
    have Z'_subset_W : ∀ i : Fin n, Z' i ⊆ W := by
      intro i; rw [subset_diff]
      exact ⟨hZU (succ i), Disjoint.mono_right hC0.2.2 (Z'_disj_V i)⟩
    -- use induction hypothesis to choose Z i ⊆ Ci ⊆ W clopen and mutually disjoint for i>0
    choose C' hC' using ih Z' W Z'_closed Z'_disj W_open Z'_subset_W
    -- desired C given by C0 = C0 and C (succ i) = C' i
    let C : Fin (n+1) → Set X := cases C0 C'
    use C
    constructor
    · -- C i are clopen and Z i ⊆ C i ⊆ U
      intro i
      by_cases h : i = 0
      · rw [h]
        exact ⟨hC0.1, hC0.2.1, Subset.trans hC0.2.2 diff_subset⟩
      · rw [(pred_eq_iff_eq_succ h).mp rfl] -- i = succ _
        exact ⟨(hC'.1 _).1, (hC'.1 _).2.1, Subset.trans (hC'.1 _).2.2 diff_subset⟩
    · -- C i are pairwise disjoint
      intro i j hij
      by_cases h : i = 0
      · rw [h]; rw [h] at hij
        rw [(pred_eq_iff_eq_succ (pos_iff_ne_zero.mp hij)).mp rfl] -- j = succ _
        exact Disjoint.mono_right (hC'.1 _).2.2 disjoint_sdiff_right
      · let i_pred := i.pred h
        have hj : j ≠ 0 := ne_zero_of_lt hij
        let j_pred := j.pred hj
        rw [(pred_eq_iff_eq_succ h).mp rfl, (pred_eq_iff_eq_succ hj).mp rfl]
        exact hC'.2 i_pred j_pred (pred_lt_pred_iff.mpr hij)





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
