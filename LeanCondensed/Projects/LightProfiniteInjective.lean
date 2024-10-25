/-
Authors: Lenny Taelman
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Topology.Separation
import LeanCondensed.Mathlib.Condensed.Light.Limits

/-!

# Project: show that non-empty light profinite spaces are injective in all profinite spaces

This is used in particular in the proof the the null sequence module is projective
in light condensed abelian groups.

-/

noncomputable section


universe u
variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

open Set

-- For every closed ⊆ open in a profinite, there is an intermediate clopen

lemma clopen_of_closed_subset_open (Z U : Set X) (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
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

/-
  given a nonempty finite family Z of disjoint closed subsets in a clopen D
  in a profinite space X, there is a clopen partition C of D with Z i ⊆  C i
  (the superflous variable D is to make the induction work)
-/

lemma clopen_partition_of_disjoint_closeds_in_clopen (n : ℕ) (Z : Fin (n+1) → Set X) (D : Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : IsClopen D)
    (Z_subset_D : ∀ i, Z i ⊆ D) (Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) ) :
    ∃ C : Fin (n+1) → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D) ∧
    D ⊆ (⋃ i, C i)  ∧ (∀ i j, i < j → Disjoint (C i) (C j)) := by
  induction n generalizing D
  case zero =>
    -- single Z given, can take C 0 = D
    use fun _ ↦ D
    simp
    exact ⟨D_clopen, Z_subset_D, subset_iUnion_of_subset 0 fun ⦃a⦄ a ↦ a⟩
  case succ n ih =>
    -- let Z' be the restriction of Z along succ : Fin n → Fin (n+1)
    let Z' : Fin (n+1) → Set X := fun i ↦ Z (succ i)
    have Z'_closed (i : Fin (n+1)) : IsClosed (Z' i) := Z_closed (succ i)
    have Z'_disj (i j : Fin (n+1)) (hij : i < j) : Disjoint (Z' i) (Z' j)  :=
      Z_disj (succ i) (succ j) (succ_lt_succ_iff.mpr hij)
    -- find Z0 ⊆ U open, disjoint from the Zi with i>0
    let U : Set X  := D \ iUnion Z'
    have U_open : IsOpen U := IsOpen.sdiff D_clopen.2
      (isClosed_iUnion_of_finite Z'_closed)
    have Z0_subset_U : Z 0 ⊆ U := subset_diff.mpr ⟨Z_subset_D 0,
      disjoint_iUnion_right.mpr (fun i ↦ Z_disj 0 (succ i) (succ_pos ↑↑i))⟩
    have Z'_disj_U (i : Fin (n+1)) : Disjoint (Z' i) U := Disjoint.mono_left
      (subset_iUnion_of_subset i fun ⦃x⦄ hx ↦ hx) disjoint_sdiff_right
    -- use clopen_sandwitch to pick clopen Z0 ⊆ C0 ⊆ U, and let D' = D \ C0
    obtain ⟨C0, C0_clopen, Z0_subset_C0, C0_subset_U⟩ :=
      clopen_of_closed_subset_open X (Z 0) U (Z_closed 0) U_open Z0_subset_U
    have C0_subset_D : C0 ⊆ D := subset_trans C0_subset_U diff_subset
    let D' : Set X := D \ C0
    have D'_clopen : IsClopen D' := IsClopen.diff D_clopen C0_clopen
    have Z'_subset_D' (i : Fin (n+1)) : Z' i ⊆ D' := subset_diff.mpr
      ⟨Z_subset_D (succ i), Disjoint.mono_right C0_subset_U (Z'_disj_U i)⟩
    -- use induction hypothesis to partition D' in clopens C' i with Z' i ⊆ C' i
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      ih Z' D' Z'_closed D'_clopen Z'_subset_D' Z'_disj
    have C'_subset_D (i : Fin (n+1)): C' i ⊆ D := subset_trans
      (C'_subset_D' i) diff_subset
    -- add C0 back in to get C := cases C0 C', and verify the needed properties
    let C : Fin (n+2) → Set X := cases C0 C'
    have C_clopen : ∀ i, IsClopen (C i) := cases C0_clopen C'_clopen
    have Z_subset_C : ∀ i, Z i ⊆ C i := cases Z0_subset_C0 Z'_subset_C'
    have C_subset_D : ∀ i, C i ⊆ D := cases C0_subset_D C'_subset_D
    have C_cover_D : D ⊆ (⋃ i, C i) := by
      intro x hx
      simp
      by_cases hx0 : x ∈ C0
      · exact ⟨0, hx0⟩
      · have xD' : x ∈ D' := mem_diff_of_mem hx hx0
        obtain ⟨i, hi⟩ := mem_iUnion.mp (C'_cover_D' xD')
        exact ⟨i.succ, hi⟩
    have C_disj (i j : Fin (n+2)) (hij : i < j) : Disjoint (C i) (C j) := by
      by_cases hi : i = 0
      · rw [hi]; rw [hi] at hij
        rw [(pred_eq_iff_eq_succ (pos_iff_ne_zero.mp hij)).mp rfl] -- j = succ _
        exact Disjoint.mono_right (C'_subset_D' _) disjoint_sdiff_right
      · have hj : j ≠ 0 := ne_zero_of_lt hij
        rw [(pred_eq_iff_eq_succ hi).mp rfl, (pred_eq_iff_eq_succ hj).mp rfl]
        exact C'_disj (i.pred hi) (j.pred hj) (pred_lt_pred_iff.mpr hij)
    exact ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩


/-
  given a nonempty finite family Z of disjoint closed subsets in a profinite space X,
  there is a clopen partition C with Z i ⊆  C i
  (case D=X in clopen_partition_of_disjoint_closeds_in_clopen)
-/


lemma clopen_partition_of_disjoint_closeds (n : ℕ) (Z : Fin (n+1) → Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) ) :
    ∃ C : Fin (n+1) → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ univ) ∧
    (univ ⊆ (⋃ i, C i)) ∧ (∀ i j, i < j → Disjoint (C i) (C j)) :=
    clopen_partition_of_disjoint_closeds_in_clopen
      X n Z univ Z_closed isClopen_univ (λ _ ↦ subset_univ _) Z_disj

-- wow, the above was generated by copilot with just one tab complete!


/-
  key extension lemma: if f : X → Y is injective map of profinite spaces
  and g is a map from X to a non-empty finite discrete space,
  then g extends along f.
-/


lemma to_fin_lifts_along_injective_profinite
    (n : ℕ) [DiscreteTopology (Fin (n+1))]
    (X Y : Profinite.{u}) (f : X → Y) (f_cont: Continuous f) (f_inj: Function.Injective f)
    (g : X → Fin (n+1)) (g_cont : Continuous g) :
    ∃ h : Y → Fin (n+1), (h ∘ f = g) ∧ (Continuous h) := by
  -- let Z i be the image in Y of the fiber of g at i
  let Z : Fin (n+1) → Set Y := fun i ↦ f '' (g⁻¹' {i})
  have f_closed : ClosedEmbedding f := Continuous.closedEmbedding f_cont f_inj
  have Z_closed (i) : IsClosed (Z i) :=
    (ClosedEmbedding.closed_iff_image_closed f_closed).mp
    (IsClosed.preimage g_cont isClosed_singleton)
  have Z_disj (i j) (hij : i < j) : Disjoint (Z i) (Z j) :=
    (disjoint_image_iff f_inj).mpr (Disjoint.preimage g (disjoint_singleton.mpr
    (Fin.ne_of_lt hij)))
  -- choose Z_i ⊆ C_i clopen and disjoint, covering Y
  obtain ⟨C, C_clopen, Z_subset_C, _, univ_cover_C, C_disj⟩ :=
    clopen_partition_of_disjoint_closeds Y n Z Z_closed Z_disj
  have h_glue (i j : Fin (n+1)) (x : Y) (hxi : x ∈ C i) (hxj : x ∈ C j) :  i = j := by
    by_cases hij : i = j
    · exact hij
    · by_cases hij' : i < j
      · exfalso
        exact Set.disjoint_iff.mp (C_disj i j hij') (mem_inter hxi hxj)
      · have hji' : j < i := lt_of_le_of_ne (not_lt.mp hij') (hij ∘ Eq.symm)
        exfalso
        exact Set.disjoint_iff.mp (C_disj j i hji') (mem_inter hxj hxi)
  have C_cover : (⋃ i, C i) = univ := by aesop -- TODO: unfold the aesop
  let h := liftCover C (λ i _ ↦ i) h_glue C_cover
  have C_eq_fiber (i) : C i = h⁻¹' {i} := by
    ext y
    exact ⟨liftCover_of_mem, by rw [preimage_liftCover]; simp⟩
  have h_cont : Continuous h := by
    have h_loc_cst : IsLocallyConstant h := by
      apply IsLocallyConstant.iff_isOpen_fiber.mpr
      intro i
      rw [←C_eq_fiber]
      exact (C_clopen i).2
    exact { isOpen_preimage := fun s _ ↦ h_loc_cst s }
  have h_lift : h ∘ f = g := by
    unfold h
    ext x
    dsimp
    rw [liftCover_of_mem]
    exact Z_subset_C _  (mem_image_of_mem f rfl)
  exact ⟨h, h_lift, h_cont⟩



open CategoryTheory


-- warming up: injectivity of finite discrete spaces in Profinite spaces

lemma injective_of_finite (S : Profinite.{u}) [Nonempty S] [Finite S]:
  Injective (S) := by
  refine { factors := ?factors }



  sorry

-- this is the target theorem!
theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  constructor
  intro X Y f g h
  -- write
  sorry
