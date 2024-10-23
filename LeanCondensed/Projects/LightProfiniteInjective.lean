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
variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

open Set

-- For every closed ⊆ open in a profinite, there is an intermediate clopen

lemma clopen_sandwich (Z U : Set X) (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every z ∈ Z has clopen neighborhood V z ⊆ U
  choose V hV using fun (z : Z) ↦ compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the V z cover Z
  have V_cover : Z ⊆ iUnion V := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- the V z are open and closed
  have V_open : ∀ z : Subtype Z, IsOpen (V z) := fun z ↦ (hV z).1.2
  have V_clopen : ∀ z : Subtype Z, IsClopen (V z) := fun z ↦ (hV z).1
  -- there is a finite subcover, let C be its union; this does the job
  have Z_compact := IsClosed.isCompact hZ
  choose I hI using IsCompact.elim_finite_subcover Z_compact V V_open V_cover
  let C := ⋃ (i ∈ I), V i
  have C_clopen : IsClopen C := Finite.isClopen_biUnion (Finset.finite_toSet I)
    (fun i _ ↦ V_clopen i)
  have C_subset_U : C ⊆ U := by simp_all only [iUnion_subset_iff, C, implies_true]
  exact ⟨C, C_clopen, hI, C_subset_U⟩



open Fin

/- every finite family of disjoint closed subsets contained in an open U in
  a profinite space can be separated by disjoint clopens contained in U
-/

lemma finite_clopen_separation (n : ℕ) (Z : Fin n → Set X) (U : Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) )
    (U_open : IsOpen U) (hZU : ∀ i, Z i ⊆ U) :
    ∃ C : Fin n → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ U) ∧
    (∀ i j, i < j → Disjoint (C i) (C j)) := by
  induction n generalizing U
  case zero =>
    -- base step is trivial, Fin 0 is empty
    exact ⟨λ _ ↦ ∅, elim0, λ i ↦ elim0 i, elim0, λ i ↦ elim0 i⟩
  case succ n ih =>
    -- let Z' be the restriction of Z along succ : Fin n → Fin (n+1)
    let Z' : Fin n → Set X := fun i ↦ Z (succ i)
    have Z'_closed (i : Fin n) : IsClosed (Z' i) := Z_closed (succ i)
    have Z'_disj (i j : Fin n) (hij : i < j) : Disjoint (Z' i) (Z' j)  :=
      Z_disj (succ i) (succ j) (succ_lt_succ_iff.mpr hij)
    -- find Z0 ⊆ V ⊆ U disjoint from the Zi with i>0
    let V : Set X  := U \ (⋃ (i : Fin n), Z' i)
    have V_open : IsOpen V := IsOpen.sdiff U_open (isClosed_iUnion_of_finite Z'_closed)
    have Z0_subset_V : Z 0 ⊆ V := subset_diff.mpr ⟨hZU 0,
      disjoint_iUnion_right.mpr (fun i ↦ Z_disj 0 (succ i) (succ_pos i))⟩
    have Z'_disj_V (i : Fin n) : Disjoint (Z' i) V := Disjoint.mono_left
      (subset_iUnion_of_subset i fun ⦃x⦄ hx ↦ hx) disjoint_sdiff_right
    -- use clopen_sandwitch to pick clopen Z0 ⊆ C0 ⊆ V
    obtain ⟨C0, C0_clopen, Z0_subset_C0, C0_subset_V⟩ :=
      clopen_sandwich X (Z 0) V (Z_closed 0) V_open Z0_subset_V
    have C0_subset_U : C0 ⊆ U := subset_trans C0_subset_V diff_subset
    -- use induction hypothesis to choose Z i ⊆ C i ⊆ W = U \ C0 for i>0
    let W : Set X := U \ C0
    have W_open : IsOpen W := IsOpen.sdiff U_open C0_clopen.1
    have Z'_subset_W (i : Fin n) : Z' i ⊆ W := subset_diff.mpr
      ⟨hZU (succ i), Disjoint.mono_right C0_subset_V (Z'_disj_V i)⟩
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_W, C'_disj⟩ :=
      ih Z' W Z'_closed Z'_disj W_open Z'_subset_W
    -- desired C given by C0 = C0 and C (succ i) = C' i
    let C : Fin (n+1) → Set X := cases C0 C'
    have C'_subset_U (i : Fin n) : C' i ⊆ U := subset_trans (C'_subset_W  i) diff_subset
    have C_disj (i j : Fin (n+1)) (hij : i < j) : Disjoint (C i) (C j) := by
      by_cases hi : i = 0
      · rw [hi]; rw [hi] at hij
        rw [(pred_eq_iff_eq_succ (pos_iff_ne_zero.mp hij)).mp rfl] -- j = succ _
        exact Disjoint.mono_right (C'_subset_W _) disjoint_sdiff_right
      · have hj : j ≠ 0 := ne_zero_of_lt hij
        rw [(pred_eq_iff_eq_succ hi).mp rfl, (pred_eq_iff_eq_succ hj).mp rfl]
        exact C'_disj (i.pred hi) (j.pred hj) (pred_lt_pred_iff.mpr hij)
    exact ⟨C, cases C0_clopen C'_clopen, cases Z0_subset_C0 Z'_subset_C',
      cases C0_subset_U C'_subset_U, C_disj⟩




-- can now prove key extension lemma for functions to nonempty finite sets

lemma to_finite_lifts_along_injective_profinite
    (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [non_empty : Nonempty S] [fin : Finite S]
    (X Y : Profinite.{u}) (f : X → Y) (f_cont: Continuous f) (f_inj: Function.Injective f)
    (g : X → S) (g_cont : Continuous g) :
    ∃ h : Y → S, (h ∘ f = g) ∧ (Continuous h) := by
  -- choose bijection φ': S → Fin n, with n>0
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin S
  let φ' := φ.symm
  -- have n_pos : 0 < n := pos_iff_nonempty.mpr ((Equiv.nonempty_congr φ).mp non_empty)
  -- let Z : Fin n → Set Y map i to f g⁻¹ {φ⁻¹ i}
  let Z : Fin n → Set Y := fun i ↦ f '' (g⁻¹' {φ' i})
  have f_closed : ClosedEmbedding f := Continuous.closedEmbedding f_cont f_inj
  have Z_closed : ∀ i, IsClosed (Z i) := fun i ↦
    (ClosedEmbedding.closed_iff_image_closed f_closed).mp
    (IsClosed.preimage g_cont isClosed_singleton)
  have Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) := fun i j hij ↦
    (disjoint_image_iff f_inj).mpr (Disjoint.preimage g (disjoint_singleton.mpr
    (Function.Injective.ne (Equiv.injective φ') (Fin.ne_of_lt hij))))
  have Z_subset_Y : ∀ i, Z i ⊆ univ := fun i ↦ subset_univ _
  -- choose Z_i ⊆ C_i clopen and disjoint
  obtain ⟨C, C_clopen, Z_subset_C, _, C_disj⟩ :=
    finite_clopen_separation Y n Z univ Z_closed Z_disj isOpen_univ Z_subset_Y
  -- let C' be the complement of the union of the C i
  let C' : Set Y := univ \ (⋃ (i : Fin n), C i)
  have C'_clopen : IsClopen C' := IsClopen.diff isClopen_univ
    (isClopen_iUnion_of_finite C_clopen)
  -- pick a `base point' in S
  let s : S := Classical.arbitrary S
  -- now define h : Y → S by mapping C i to φ i and C' to s








  sorry



open CategoryTheory

-- this is the target theorem!
theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  constructor
  intro X Y f g h
  -- write
  sorry
