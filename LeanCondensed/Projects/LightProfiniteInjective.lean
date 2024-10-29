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
  refinement, given finite family Z i ⊆ D i of closed subsets in clopens
  such that the Z i are disjoint, then there are clopens Z i ⊆ C i ⊆ D i
  with the C i disjoint, and such that ∪ C i = ∪ D i
  NOTE: this is more elegant, works for empty family!
-/

lemma clopen_partition_of_disjoint_closeds_in_clopen' (n : ℕ)
    (Z : Fin n → Set X) (D : Fin n → Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : ∀ i, IsClopen (D i))
    (Z_subset_D : ∀ i, Z i ⊆ D i) (Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) ) :
    ∃ C : Fin n → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D i) ∧
    (⋃ i, D i) ⊆ (⋃ i, C i)  ∧ (∀ i j, i < j → Disjoint (C i) (C j)) := by
  induction n
  case zero =>
    -- single Z given, can take C 0 = D
    use fun _ ↦ univ -- empty range, can use junk
    exact ⟨elim0, fun i ↦ elim0 i, fun i ↦ elim0 i, by
      simp only [iUnion_of_empty]; trivial, fun i j ↦ elim0 i⟩
  case succ n ih =>
    -- let Z' be the restriction of Z along succ : Fin n → Fin (n+1)
    let Z' : Fin n → Set X := fun i ↦ Z (succ i)
    have Z'_closed (i : Fin n) : IsClosed (Z' i) := Z_closed (succ i)
    have Z'_disj (i j : Fin n) (hij : i < j) : Disjoint (Z' i) (Z' j)  :=
      Z_disj (succ i) (succ j) (succ_lt_succ_iff.mpr hij)
    -- find Z 0 ⊆ V ⊆ D 0 \ ⋃ Z' using clopen_sandwich
    let U : Set X  := D 0 \ iUnion Z'
    have U_open : IsOpen U := IsOpen.sdiff (D_clopen 0).2
      (isClosed_iUnion_of_finite Z'_closed)
    have Z0_subset_U : Z 0 ⊆ U := subset_diff.mpr ⟨Z_subset_D 0,
      disjoint_iUnion_right.mpr (fun i ↦ Z_disj 0 (succ i) (succ_pos ↑↑i))⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      clopen_of_closed_subset_open X (Z 0) U (Z_closed 0) U_open Z0_subset_U
    have V_subset_D0 : V ⊆ D 0 := subset_trans V_subset_U diff_subset
    -- choose Z' i ⊆ C' i ⊆ D' i = D i.succ \ V using induction hypothesis
    let D' : Fin n → Set X := fun i ↦ D (succ i) \ V
    have D'_clopen (i : Fin n): IsClopen (D' i) := IsClopen.diff (D_clopen i.succ) V_clopen
    have Z'_subset_D' (i : Fin n) : Z' i ⊆ D' i := by
      apply subset_diff.mpr
      constructor
      · exact Z_subset_D (succ i)
      · apply Disjoint.mono_right V_subset_U
        exact Disjoint.mono_left (subset_iUnion_of_subset i fun ⦃_⦄ h ↦ h) disjoint_sdiff_right
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      ih Z' D' Z'_closed D'_clopen Z'_subset_D' Z'_disj
    have C'_subset_D (i : Fin n): C' i ⊆ D (succ i) := subset_trans (C'_subset_D' i) diff_subset
    -- now choose C0 = D 0 \ ⋃ C' i
    let C0 : Set X := D 0 \ iUnion (fun i ↦ C' i)
    have C0_subset_D0 : C0 ⊆ D 0 := diff_subset
    have C0_clopen : IsClopen C0 := IsClopen.diff (D_clopen 0) (isClopen_iUnion_of_finite C'_clopen)
    have Z0_subset_C0 : Z 0 ⊆ C0 := by
      unfold C0
      apply subset_diff.mpr
      constructor
      · exact Z_subset_D 0
      · apply Disjoint.mono_left Z0_subset_V
        exact disjoint_iUnion_right.mpr fun i ↦ Disjoint.mono_right (C'_subset_D' i) disjoint_sdiff_right
    -- patch together to define C := cases C0 C', and verify the needed properties
    let C : Fin (n+1) → Set X := cases C0 C'
    have C_clopen : ∀ i, IsClopen (C i) := cases C0_clopen C'_clopen
    have Z_subset_C : ∀ i, Z i ⊆ C i := cases Z0_subset_C0 Z'_subset_C'
    have C_subset_D : ∀ i, C i ⊆ D i := cases C0_subset_D0 C'_subset_D
    have C_cover_D : (⋃ i, D i) ⊆ (⋃ i, C i) := by
      intro x hx
      simp
      by_cases hx0 : x ∈ C0
      · exact ⟨0, hx0⟩
      · by_cases hxD : x ∈ D 0
        · have hxC' : x ∈ iUnion C' := by
            rw [mem_diff] at hx0
            push_neg at hx0
            exact hx0 hxD
          obtain ⟨i, hi⟩ := mem_iUnion.mp hxC'
          exact ⟨i.succ, hi⟩
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          have hi' : i ≠ 0 := by
            intro h
            rw [h] at hi
            tauto
          let j := i.pred hi'
          have hij : i = j.succ := (pred_eq_iff_eq_succ hi').mp rfl
          rw [hij] at hi
          have hxD' : x ∈ ⋃ i, D' i := by
            apply mem_iUnion.mpr ⟨j, _⟩
            apply mem_diff_of_mem hi
            exact fun h ↦ hxD (V_subset_D0 h)
          apply C'_cover_D' at hxD'
          obtain ⟨k, hk⟩ := mem_iUnion.mp hxD'
          exact ⟨k.succ, hk⟩
    have C_disj (i j : Fin (n+1)) (hij : i < j) : Disjoint (C i) (C j) := by
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
  let h := liftCover C (λ i _ ↦ i) h_glue (univ_subset_iff.mp univ_cover_C)
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


lemma to_fin_lifts_along_injective_profinite'
    (X Y S: Profinite.{u}) [hne : Nonempty S] [hS : Finite S]
    (f : X → Y) (f_cont: Continuous f) (f_inj: Function.Injective f)
    (g : X → S) (g_cont : Continuous g) :
    ∃ k : Y → S, (k ∘ f = g) ∧ (Continuous k) := by
  -- let m : Nat be the cardinality of S
  obtain ⟨m, φ, ψ, h1, h2⟩ := Finite.exists_equiv_fin S
  have _ : Nonempty (Fin m) := Nonempty.map φ hne
  -- conclude that m is n+1 for some n
  have m_pos : 0 < m := size_pos'
  let n := m.pred
  have hmn : n.succ = m := Nat.sub_one_add_one_eq_of_pos m_pos
  rw [← hmn] at φ ψ









  sorry
  -- verify that m is positive (since S is nonempty)



/-
  this is the key statement for the inductive proof of injectivity. Given
  a commutative square
    X --> Y
    |     |
    v     v
    S --> T
  where the top map is injective, Y is profinite and S and T are finite discrete
  nonempty, there exists a diagonal map Y --> S making the diagram commute.
-/


lemma key_lifting_lemma (X Y S T : Profinite.{u}) [Nonempty S] [Finite S] [Finite T]
  (f : X → Y) (hf : Continuous f) (f_inj : Function.Injective f)
  (f' : S → T) (hf' : Continuous f') (f'_surj : Function.Surjective f')
  (g : X → S) (g_cont : Continuous g) (g' : Y → T) (hg' : Continuous g')
  (h_comm : g' ∘ f = f' ∘ g) :
  ∃ k : Y → S, (f' ∘ k = g') ∧ (k ∘ f = g) ∧ (Continuous k) := by
  -- TODO: do this on paper first
  /- intuitive proof: for ever t, produce map from fiber Y_t to S_t by extending
    along X_t → Y_t. Then glue these to produce Y → S.
    This should work quite smoothly; produce a function
    T → _, mapping t to the choice of a function Y_t → S_t guaranteed by the above
    then glue.
  -/
  /- option 2:
    S provides disjoint closed subsets Z_s of Y
    need to produce clopens C_s with the additional property that g'(C_S) ⊆ {f'(s)}
    then can simply proceed as above
  -/
  /- option 3: refine clopens C_s to clopens C_{s,t} = C_s ∩ g'⁻¹ {t}
    note that X is contained in the 'compatible' clopens C_{s,t} for which f'(s) = t
    ugly; then need to map compatible C_{s,t} to s, and incompatible C_{s,t} to random preimage
    of t.
  -/
  -- REALLY do this on paper first!!


  sorry


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
