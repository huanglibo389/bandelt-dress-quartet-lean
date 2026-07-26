import QuartetV060.QuartetKernelGeometry
import QuartetDistance.TiedSampleCount
import QuartetDistance.Upper

/-!
# The 24-ordering table on one four-leaf subset

This file identifies the concrete tree kernel on an injectively enumerated
four-leaf subset with a finite `Fin 3` topology table.  Exhaustive evaluation
of the 24 permutations then gives contribution `16` when the two displayed
topologies agree and `-8` when they differ.
-/

namespace QuartetV060

namespace QuartetTopologyCounting

open ActivePathGeometry QuartetKernelGeometry QuartetDistance

noncomputable section

/-- The `i`-th canonical pairing transported along an enumeration of four
distinct taxa. -/
def pairingSplit {X : Type} [DecidableEq X]
    (f : Fin 4 ↪ X) (i : Fin 3) :
    Circular.QuartetSplit X :=
  Circular.mapSplit f (Upper.canonicalTopology i)

/-- Three concrete permutations realizing the three canonical pairings. -/
def topologyPerm : Fin 3 → Circular.Perm4 :=
  ![Equiv.refl (Fin 4), Equiv.swap 1 2, Equiv.swap 2 3]

theorem mapSplit_topologyPerm (i : Fin 3) :
    Circular.mapSplit (topologyPerm i).toEmbedding
      Circular.canonicalCrossing = Upper.canonicalTopology i := by
  fin_cases i <;> decide

theorem isQuartetSplit_pairingSplit
    {X : Type} [DecidableEq X]
    (f : Fin 4 ↪ X) (i : Fin 3) :
    Circular.IsQuartetSplit (Finset.univ.map f) (pairingSplit f i) := by
  refine ⟨(topologyPerm i).toEmbedding.trans f, ?_, ?_⟩
  · have hperm :
        Finset.univ.map (topologyPerm i).toEmbedding =
          (Finset.univ : Finset (Fin 4)) := by
      ext x
      simp
    calc
      Finset.univ.map f =
          (Finset.univ.map (topologyPerm i).toEmbedding).map f := by
            rw [hperm]
      _ = Finset.univ.map ((topologyPerm i).toEmbedding.trans f) := by
            rw [Finset.map_map]
  · unfold pairingSplit Circular.crossing
    rw [← Circular.mapSplit_mapSplit, mapSplit_topologyPerm]

theorem displaysPair_02_13_iff
    {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (T : Tree.PhyloTree X) (f : Fin 4 ↪ X) :
    DisplaysPair T (f 0) (f 2) (f 1) (f 3) ↔
      GraphQuartet.PhyloTree.GraphDisplaysSplit T
        (Finset.univ.map f) (pairingSplit f 0) := by
  constructor
  · intro h
    refine ⟨isQuartetSplit_pairingSplit f 0, {f 0, f 2}, ?_,
      {f 1, f 3}, ?_, ?_, h⟩
    · simp [pairingSplit, Upper.canonicalTopology, Circular.mapSplit,
        Circular.splitOf, Circular.pair]
    · simp [pairingSplit, Upper.canonicalTopology, Circular.mapSplit,
        Circular.splitOf, Circular.pair]
    · intro heq
      have hmem : f 0 ∈ ({f 1, f 3} : Finset X) := by
        rw [← heq]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h01 | h03
      · exact (by decide : (0 : Fin 4) ≠ 1) (f.injective h01)
      · exact (by decide : (0 : Fin 4) ≠ 3) (f.injective h03)
  · rintro ⟨_, A, hA, B, hB, _, hsep⟩
    have hsides :
        A = {f 0, f 2} ∧ B = {f 1, f 3} ∨
        A = {f 1, f 3} ∧ B = {f 0, f 2} := by
      simp [pairingSplit, Upper.canonicalTopology, Circular.mapSplit,
        Circular.splitOf, Circular.pair] at hA hB
      aesop
    rcases hsides with h | h
    · unfold DisplaysPair
      simpa [h.1, h.2] using hsep
    · unfold DisplaysPair
      simpa [h.1, h.2] using
        ((GraphQuartet.edgeSeparates_comm _ _ _ _).mp hsep)

theorem displaysPair_03_12_iff
    {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (T : Tree.PhyloTree X) (f : Fin 4 ↪ X) :
    DisplaysPair T (f 0) (f 3) (f 1) (f 2) ↔
      GraphQuartet.PhyloTree.GraphDisplaysSplit T
        (Finset.univ.map f) (pairingSplit f 2) := by
  constructor
  · intro h
    refine ⟨isQuartetSplit_pairingSplit f 2, {f 0, f 3}, ?_,
      {f 1, f 2}, ?_, ?_, h⟩
    · simp [pairingSplit, Upper.canonicalTopology, Circular.mapSplit,
        Circular.splitOf, Circular.pair]
    · simp [pairingSplit, Upper.canonicalTopology, Circular.mapSplit,
        Circular.splitOf, Circular.pair]
    · intro heq
      have hmem : f 0 ∈ ({f 1, f 2} : Finset X) := by
        rw [← heq]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h01 | h02
      · exact (by decide : (0 : Fin 4) ≠ 1) (f.injective h01)
      · exact (by decide : (0 : Fin 4) ≠ 2) (f.injective h02)
  · rintro ⟨_, A, hA, B, hB, _, hsep⟩
    have hsides :
        A = {f 0, f 3} ∧ B = {f 1, f 2} ∨
        A = {f 1, f 2} ∧ B = {f 0, f 3} := by
      simp [pairingSplit, Upper.canonicalTopology, Circular.mapSplit,
        Circular.splitOf, Circular.pair] at hA hB
      aesop
    rcases hsides with h | h
    · unfold DisplaysPair
      simpa [h.1, h.2] using hsep
    · unfold DisplaysPair
      simpa [h.1, h.2] using
        ((GraphQuartet.edgeSeparates_comm _ _ _ _).mp hsep)

/-- Enumerate a four-leaf subset after a permutation of its four slots. -/
def enumeration {n : ℕ} (q : Upper.Quartet n)
    (σ : Circular.Perm4) : Fin 4 ↪ Fin n :=
  σ.toEmbedding.trans (Upper.quartetEmbedding q)

theorem enumeration_range
    {n : ℕ} (q : Upper.Quartet n) (σ : Circular.Perm4) :
    Finset.univ.map (enumeration q σ) = q.1 := by
  have hperm :
      Finset.univ.map σ.toEmbedding =
        (Finset.univ : Finset (Fin 4)) := by
    ext x
    simp
  calc
    Finset.univ.map (enumeration q σ) =
        (Finset.univ.map σ.toEmbedding).map
          (Upper.quartetEmbedding q) := by
            rw [Finset.map_map]
            rfl
    _ = Finset.univ.map (Upper.quartetEmbedding q) := by
          rw [hperm]
    _ = q.1 := Circular.range_enumerateFour q.1 q.2

/-- Pure finite table for a displayed topology and one ordering. -/
def localKernel (t : Fin 3) (σ : Circular.Perm4) : ℚ :=
  (if Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology 0) =
      Upper.canonicalTopology t then 1 else 0) -
  (if Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology 2) =
      Upper.canonicalTopology t then 1 else 0)

/-- The two distinct topology labels obtained by transporting the two kernel
channels along one four-slot permutation. -/
abbrev DistinctTopologyPair :=
  {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- Decode a transported canonical topology back to its `Fin 3` label. -/
def permutedTopology (σ : Circular.Perm4) (i : Fin 3) : Fin 3 :=
  if Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology i) =
      Upper.canonicalTopology 0 then 0
  else if Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology i) =
      Upper.canonicalTopology 1 then 1
  else 2

theorem mapSplit_permutedTopology
    (σ : Circular.Perm4) (i : Fin 3) :
    Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology i) =
      Upper.canonicalTopology (permutedTopology σ i) := by
  revert σ i
  decide

theorem permutedTopology_ne
    (σ : Circular.Perm4) :
    permutedTopology σ 0 ≠ permutedTopology σ 2 := by
  intro h
  have himage :
      Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology 0) =
        Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology 2) := by
    rw [mapSplit_permutedTopology, mapSplit_permutedTopology, h]
  have hcanonical :
      Upper.canonicalTopology 0 = Upper.canonicalTopology 2 :=
    Circular.mapSplit_injective σ.toEmbedding himage
  exact (by decide : (0 : Fin 3) ≠ 2)
    (Upper.canonicalTopology_injective hcanonical)

def topologyPair (σ : Circular.Perm4) : DistinctTopologyPair :=
  ⟨(permutedTopology σ 0, permutedTopology σ 2),
    permutedTopology_ne σ⟩

/-- Each ordered pair of distinct transported topology labels is realized by
exactly four of the twenty-four slot permutations.  This is a kernel-checked
finite theorem. -/
theorem topologyPair_fiber_card (p : DistinctTopologyPair) :
    Counting.channelCount topologyPair p = 4 := by
  revert p
  decide

/-- The signed local-kernel value attached to a distinct ordered topology
pair. -/
def rawPairScore (t : Fin 3) (p : Fin 3 × Fin 3) : ℚ :=
  (if p.1 = t then 1 else 0) - (if p.2 = t then 1 else 0)

def pairScore (t : Fin 3) (p : DistinctTopologyPair) : ℚ :=
  rawPairScore t p

theorem localKernel_eq_pairScore
    (t : Fin 3) (σ : Circular.Perm4) :
    localKernel t σ = pairScore t (topologyPair σ) := by
  simp only [localKernel, pairScore, topologyPair]
  rw [mapSplit_permutedTopology, mapSplit_permutedTopology]
  simp only [Upper.canonicalTopology_injective.eq_iff]
  rfl

theorem card_topologyPair_fiber (p : DistinctTopologyPair) :
    Fintype.card {σ : Circular.Perm4 // topologyPair σ = p} = 4 := by
  rw [Fintype.card_subtype]
  exact topologyPair_fiber_card p

/-- The six possible ordered pairs of distinct topology labels give the
`16` and `-8` Gram table after their common fiber multiplicity four is
restored. -/
theorem pairScore_product_sum (t₁ t₂ : Fin 3) :
    (∑ p : DistinctTopologyPair,
      (4 : ℚ) * pairScore t₁ p * pairScore t₂ p) =
        if t₁ = t₂ then 16 else -8 := by
  simp only [pairScore]
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 ≠ p.2)
    (by simp)
    (fun p => (4 : ℚ) * rawPairScore t₁ p * rawPairScore t₂ p)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  fin_cases t₁ <;> fin_cases t₂ <;>
    norm_num [rawPairScore, Fin.sum_univ_succ] <;>
    simp <;>
    norm_num

theorem fiber_sum_pairScore_product
    (t₁ t₂ : Fin 3) (p : DistinctTopologyPair) :
    (∑ σ : {σ : Circular.Perm4 // topologyPair σ = p},
      pairScore t₁ (topologyPair σ) *
        pairScore t₂ (topologyPair σ)) =
      (4 : ℚ) * pairScore t₁ p * pairScore t₂ p := by
  have hconst :
      ∀ σ : {σ : Circular.Perm4 // topologyPair σ = p},
        pairScore t₁ (topologyPair σ) *
            pairScore t₂ (topologyPair σ) =
          pairScore t₁ p * pairScore t₂ p := by
    intro σ
    rw [σ.property]
  calc
    (∑ σ : {σ : Circular.Perm4 // topologyPair σ = p},
        pairScore t₁ (topologyPair σ) *
          pairScore t₂ (topologyPair σ)) =
        ∑ _σ : {σ : Circular.Perm4 // topologyPair σ = p},
          pairScore t₁ p * pairScore t₂ p := by
            apply Finset.sum_congr rfl
            intro σ _
            exact hconst σ
    _ = (Fintype.card
          {σ : Circular.Perm4 // topologyPair σ = p} : ℚ) *
        (pairScore t₁ p * pairScore t₂ p) := by simp
    _ = (4 : ℚ) * pairScore t₁ p * pairScore t₂ p := by
      rw [card_topologyPair_fiber]
      ring

theorem localKernel_product_sum (t₁ t₂ : Fin 3) :
    (∑ σ : Circular.Perm4,
      localKernel t₁ σ * localKernel t₂ σ) =
        if t₁ = t₂ then 16 else -8 := by
  simp_rw [localKernel_eq_pairScore]
  rw [← Fintype.sum_fiberwise topologyPair
    (fun σ : Circular.Perm4 =>
      pairScore t₁ (topologyPair σ) *
        pairScore t₂ (topologyPair σ))]
  simp_rw [fiber_sum_pairScore_product]
  exact pairScore_product_sum t₁ t₂

theorem pairingSplit_enumeration
    {n : ℕ} (q : Upper.Quartet n)
    (σ : Circular.Perm4) (i : Fin 3) :
    pairingSplit (enumeration q σ) i =
      Circular.mapSplit (Upper.quartetEmbedding q)
        (Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology i)) := by
  unfold pairingSplit enumeration
  rw [Circular.mapSplit_mapSplit]

theorem displaysPair_enumeration_02_13_iff
    {n : ℕ} (T : Tree.PhyloTree (Fin n))
    (q : Upper.Quartet n) (σ : Circular.Perm4) :
    DisplaysPair T
        (enumeration q σ 0) (enumeration q σ 2)
        (enumeration q σ 1) (enumeration q σ 3) ↔
      Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology 0) =
        Upper.canonicalTopology (Upper.displayedTopology T q) := by
  letI : Nonempty (Fin n) := ⟨Upper.quartetEmbedding q 0⟩
  rw [displaysPair_02_13_iff, enumeration_range]
  rw [GraphQuartet.PhyloTree.graphDisplaysSplit_iff_eq_displayedSplitOn
    T q.1 q.2]
  rw [pairingSplit_enumeration, ← Upper.splitOfTopology_displayedTopology T q]
  unfold Upper.splitOfTopology
  exact (Circular.mapSplit_injective (Upper.quartetEmbedding q)).eq_iff

theorem displaysPair_enumeration_03_12_iff
    {n : ℕ} (T : Tree.PhyloTree (Fin n))
    (q : Upper.Quartet n) (σ : Circular.Perm4) :
    DisplaysPair T
        (enumeration q σ 0) (enumeration q σ 3)
        (enumeration q σ 1) (enumeration q σ 2) ↔
      Circular.mapSplit σ.toEmbedding (Upper.canonicalTopology 2) =
        Upper.canonicalTopology (Upper.displayedTopology T q) := by
  letI : Nonempty (Fin n) := ⟨Upper.quartetEmbedding q 0⟩
  rw [displaysPair_03_12_iff, enumeration_range]
  rw [GraphQuartet.PhyloTree.graphDisplaysSplit_iff_eq_displayedSplitOn
    T q.1 q.2]
  rw [pairingSplit_enumeration, ← Upper.splitOfTopology_displayedTopology T q]
  unfold Upper.splitOfTopology
  exact (Circular.mapSplit_injective (Upper.quartetEmbedding q)).eq_iff

/-- On an injectively enumerated quartet, the concrete tree kernel is exactly
the finite topology table. -/
theorem kernel_enumeration_eq_localKernel
    {n : ℕ} [Nonempty (Fin n)] (T : Tree.PhyloTree (Fin n))
    (q : Upper.Quartet n) (σ : Circular.Perm4) :
    TreeKernel.kernel T
      (enumeration q σ 0) (enumeration q σ 1)
      (enumeration q σ 2) (enumeration q σ 3) =
        localKernel (Upper.displayedTopology T q) σ := by
  classical
  let f := enumeration q σ
  have h02 : f 0 ≠ f 2 := f.injective.ne (by decide)
  have h13 : f 1 ≠ f 3 := f.injective.ne (by decide)
  have h03 : f 0 ≠ f 3 := f.injective.ne (by decide)
  have h12 : f 1 ≠ f 2 := f.injective.ne (by decide)
  rw [kernel_eq_pairingIndicator_sub_pairingIndicator
    T (f 0) (f 1) (f 2) (f 3) h02 h13 h03 h12]
  simp only [displaysPairIndicator]
  rw [if_congr (displaysPair_enumeration_02_13_iff T q σ) rfl rfl]
  rw [if_congr (displaysPair_enumeration_03_12_iff T q σ) rfl rfl]
  rfl

/-- The 24 orderings contribute `16` when the two topology labels agree. -/
theorem localKernel_same_sum (t : Fin 3) :
    (∑ σ : Circular.Perm4, localKernel t σ * localKernel t σ) = 16 := by
  simpa using localKernel_product_sum t t

/-- The 24 orderings contribute `-8` when the two topology labels differ. -/
theorem localKernel_diff_sum (t₁ t₂ : Fin 3) (h : t₁ ≠ t₂) :
    (∑ σ : Circular.Perm4,
      localKernel t₁ σ * localKernel t₂ σ) = -8 := by
  simpa [h] using localKernel_product_sum t₁ t₂

theorem localKernel_same_sum_symm (t : Fin 3) :
    (∑ σ : Circular.Perm4,
      localKernel t σ.symm * localKernel t σ.symm) = 16 := by
  calc
    (∑ σ : Circular.Perm4,
        localKernel t σ.symm * localKernel t σ.symm) =
        ∑ σ : Circular.Perm4,
          localKernel t σ * localKernel t σ := by
            refine Fintype.sum_equiv (Equiv.inv Circular.Perm4)
              (fun σ : Circular.Perm4 =>
                localKernel t σ.symm * localKernel t σ.symm)
              (fun σ : Circular.Perm4 =>
                localKernel t σ * localKernel t σ) ?_
            intro σ
            rfl
    _ = 16 := localKernel_same_sum t

theorem localKernel_diff_sum_symm
    (t₁ t₂ : Fin 3) (h : t₁ ≠ t₂) :
    (∑ σ : Circular.Perm4,
      localKernel t₁ σ.symm * localKernel t₂ σ.symm) = -8 := by
  calc
    (∑ σ : Circular.Perm4,
        localKernel t₁ σ.symm * localKernel t₂ σ.symm) =
        ∑ σ : Circular.Perm4,
          localKernel t₁ σ * localKernel t₂ σ := by
            refine Fintype.sum_equiv (Equiv.inv Circular.Perm4)
              (fun σ : Circular.Perm4 =>
                localKernel t₁ σ.symm * localKernel t₂ σ.symm)
              (fun σ : Circular.Perm4 =>
                localKernel t₁ σ * localKernel t₂ σ) ?_
            intro σ
            rfl
    _ = -8 := localKernel_diff_sum t₁ t₂ h

end

end QuartetTopologyCounting

end QuartetV060
