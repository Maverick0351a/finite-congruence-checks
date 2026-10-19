/- The finite-board composition and transport arguments adapt
openai/math SnakyTwentyOne/Semantics/Game.lean at commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Changes: explicit finite board, fresh-cell budget, immediate victory,
and nonempty legal Breaker response requirements. See UPSTREAM_LICENSE. -/
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21
variable {α : Type*} [DecidableEq α]

/-- A finite-board strategy tree counting actual fresh Maker claims. Victory can
end immediately; a nonwinning turn requires an available legal Breaker reply. -/
inductive FiniteWins (U : Finset α) (win : Finset α → Prop) : ℕ → Finset α → Finset α → Prop
  | done {n M B} : win M → FiniteWins U win n M B
  | finish {n M B} (x : α) (hxU : x ∈ U) (hxM : x ∉ M) (hxB : x ∉ B)
      (won : win (insert x M)) : FiniteWins U win (n + 1) M B
  | move {n M B} (x : α) (hxU : x ∈ U) (hxM : x ∉ M) (hxB : x ∉ B)
      (available : ∃ b ∈ U, b ∉ insert x M ∧ b ∉ B)
      (next : ∀ b ∈ U, b ∉ insert x M → b ∉ B →
        FiniteWins U win n (insert x M) (insert b B)) :
      FiniteWins U win (n + 1) M B

theorem FiniteWins.weaken {U : Finset α} {win : Finset α → Prop} {n M B}
    (h : FiniteWins U win n M B) : ∀ k, FiniteWins U win (n + k) M B := by
  induction h with
  | done hw => intro k; exact .done hw
  | @finish n M B x hxU hxM hxB hw =>
    intro k
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (FiniteWins.finish (n := n + k) x hxU hxM hxB hw)
  | move x hxU hxM hxB ha next ih =>
    intro k
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (FiniteWins.move x hxU hxM hxB ha (fun b hbU hbM hbB => ih b hbU hbM hbB k))

theorem FiniteWins.mono {U : Finset α} {win : Finset α → Prop} {n m M B}
    (h : FiniteWins U win n M B) (hnm : n ≤ m) : FiniteWins U win m M B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact h.weaken k

/-- The budget leaves two fresh cells per remaining Maker turn. It applies to
all larger boards, so Breaker may also play outside the certificate envelope. -/
def FiniteTemplate (win : Finset α → Prop) (n : ℕ) (A H : Finset α) : Prop :=
  ∀ U M B, H ⊆ U → M ⊆ U → B ⊆ U → Disjoint M B → A ⊆ M → Disjoint B H →
    M.card + B.card + 2 * n ≤ U.card → FiniteWins U win n M B

theorem FiniteTemplate.mono {win : Finset α → Prop} {n m A H}
    (h : FiniteTemplate win n A H) (hnm : n ≤ m) : FiniteTemplate win m A H := by
  intro U M B hHU hMU hBU hMB hAM hBH hcard
  exact (h U M B hHU hMU hBU hMB hAM hBH (by omega)).mono hnm

theorem fresh_cell (U M B : Finset α) (h : M.card + B.card < U.card) :
    ∃ x ∈ U, x ∉ M ∧ x ∉ B := by
  obtain ⟨x, hxU, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (lt_of_le_of_lt (Finset.card_union_le M B) h)
  exact ⟨x, hxU, (fun hM => hx (Finset.mem_union_left B hM)),
    (fun hB => hx (Finset.mem_union_right M hB))⟩

theorem finite_immediate (win : Finset α → Prop) (H : Finset α) (pivot : α)
    (hp : pivot ∈ H) (hwin : ∀ M, H ⊆ M → win M) :
    FiniteTemplate win 1 (H.erase pivot) H := by
  intro U M B hHU _ _ _ hAM hBH _
  have hsub : H ⊆ insert pivot M := by
    intro y hy
    by_cases hyp : y = pivot
    · simp [hyp]
    · exact Finset.mem_insert_of_mem (hAM (Finset.mem_erase.mpr ⟨hyp, hy⟩))
  by_cases hpM : pivot ∈ M
  · exact .done (hwin M (by simpa [Finset.insert_eq_of_mem hpM] using hsub))
  · exact .finish pivot (hHU hp) hpM
      (fun hpB => Finset.disjoint_left.mp hBH hpB hp) (hwin _ hsub)

theorem finite_compose {ι : Type*} [Nonempty ι]
    (win : Finset α → Prop) (n : ℕ) (C D : ι → Finset α)
    (hchild : ∀ j, FiniteTemplate win n (C j) (D j))
    (pivot : α) (A H : Finset α) (hpH : pivot ∈ H)
    (hC : ∀ j, C j ⊆ insert pivot A)
    (hD : ∀ j, D j ⊆ H)
    (hcommon : ∀ b, (∀ j, b ∈ D j) → b ∈ insert pivot A) :
    FiniteTemplate win (n + 1) A H := by
  intro U M B hHU hMU hBU hMB hAM hBH hcard
  have hpB : pivot ∉ B := fun hp => Finset.disjoint_left.mp hBH hp hpH
  have hex : ∃ x ∈ U, x ∉ M ∧ x ∉ B ∧ pivot ∈ insert x M := by
    by_cases hpM : pivot ∈ M
    · obtain ⟨x, hxU, hxM, hxB⟩ := fresh_cell U M B (by omega)
      exact ⟨x, hxU, hxM, hxB, Finset.mem_insert_of_mem hpM⟩
    · exact ⟨pivot, hHU hpH, hpM, hpB, Finset.mem_insert_self _ _⟩
  obtain ⟨x, hxU, hxM, hxB, hpx⟩ := hex
  have howned : insert pivot A ⊆ insert x M := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hyp | hyA
    · subst y; exact hpx
    · exact Finset.mem_insert_of_mem (hAM hyA)
  have hMcard : (insert x M).card = M.card + 1 := Finset.card_insert_of_notMem hxM
  apply FiniteWins.move x hxU hxM hxB
  · exact fresh_cell U (insert x M) B (by omega)
  · intro b hbU hbM hbB
    obtain ⟨j, hjC, hjD⟩ := surviving_child C D (insert x M) B H
      (fun j => (hC j).trans howned) hD (fun y hy => howned (hcommon y hy)) hBH b hbM
    refine hchild j U (insert x M) (insert b B) ((hD j).trans hHU)
      (Finset.insert_subset hxU hMU) (Finset.insert_subset hbU hBU) ?_ hjC hjD ?_
    · refine Finset.disjoint_left.mpr ?_
      intro y hyM hyB
      rcases Finset.mem_insert.mp hyB with hyb | hyB
      · subst y; exact hbM hyM
      · rcases Finset.mem_insert.mp hyM with hyx | hyM
        · subst y; exact hxB hyB
        · exact Finset.disjoint_left.mp hMB hyM hyB
    · rw [hMcard, Finset.card_insert_of_notMem hbB]
      omega

theorem FiniteWins.transport {U : Finset α} {win : Finset α → Prop} {n M B}
    (h : FiniteWins U win n M B) (e : α ≃ α)
    (hwin : ∀ X, win X → win (X.image e)) :
    FiniteWins (U.image e) win n (M.image e) (B.image e) := by
  induction h with
  | done hw => exact .done (hwin _ hw)
  | finish x hxU hxM hxB hw =>
    apply FiniteWins.finish (e x) (Finset.mem_image_of_mem e hxU)
    · simpa only [Finset.mem_image, e.injective.eq_iff, exists_eq_right] using hxM
    · simpa only [Finset.mem_image, e.injective.eq_iff, exists_eq_right] using hxB
    · simpa only [Finset.image_insert] using hwin _ hw
  | @move n M B x hxU hxM hxB ha next ih =>
    apply FiniteWins.move (e x) (Finset.mem_image_of_mem e hxU)
    · simpa only [Finset.mem_image, e.injective.eq_iff, exists_eq_right] using hxM
    · simpa only [Finset.mem_image, e.injective.eq_iff, exists_eq_right] using hxB
    · obtain ⟨b, hbU, hbM, hbB⟩ := ha
      refine ⟨e b, Finset.mem_image_of_mem e hbU, ?_, ?_⟩
      · simpa only [← Finset.image_insert, Finset.mem_image, e.injective.eq_iff,
          exists_eq_right] using hbM
      · simpa only [Finset.mem_image, e.injective.eq_iff, exists_eq_right] using hbB
    · intro b hbU hbM hbB
      have hbU' : e.symm b ∈ U := by
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hbU
        simpa [← he] using hy
      have hbM' : e.symm b ∉ insert x M := by
        intro hb
        apply hbM
        simpa [Finset.image_insert] using Finset.mem_image_of_mem e hb
      have hbB' : e.symm b ∉ B := by
        intro hb
        apply hbB
        simpa using Finset.mem_image_of_mem e hb
      simpa [Finset.image_insert] using ih (e.symm b) hbU' hbM' hbB'

theorem FiniteTemplate.transport {win : Finset α → Prop} {n A H}
    (h : FiniteTemplate win n A H) (e : α ≃ α)
    (hwin : ∀ X, win X → win (X.image e)) :
    FiniteTemplate win n (A.image e) (H.image e) := by
  intro U M B hHU hMU hBU hMB hAM hBH hcard
  have hHU' : H ⊆ U.image e.symm := by
    intro z hz
    exact Finset.mem_image.mpr ⟨e z, hHU (Finset.mem_image_of_mem e hz), by simp⟩
  have hMB' : Disjoint (M.image e.symm) (B.image e.symm) := by
    exact (Finset.disjoint_image e.symm.injective).mpr hMB
  have hAM' : A ⊆ M.image e.symm := by
    intro z hz
    exact Finset.mem_image.mpr ⟨e z, hAM (Finset.mem_image_of_mem e hz), by simp⟩
  have hBH' : Disjoint (B.image e.symm) H := by
    refine Finset.disjoint_left.mpr ?_
    intro z hzB hzH
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hzB
    have hxH : x ∈ H.image e := by
      exact Finset.mem_image.mpr ⟨z, hzH, by rw [← he]; simp⟩
    exact Finset.disjoint_left.mp hBH hx hxH
  have hcard' : (M.image e.symm).card + (B.image e.symm).card + 2 * n ≤
      (U.image e.symm).card := by
    simpa only [Finset.card_image_of_injective _ e.symm.injective] using hcard
  have hh := (h (U.image e.symm) (M.image e.symm) (B.image e.symm)
    hHU' (Finset.image_subset_image hMU) (Finset.image_subset_image hBU)
    hMB' hAM' hBH' hcard').transport e hwin
  simpa [Finset.image_image, Function.comp_def] using hh

theorem finite_placed21_template {n : ℕ} {A H : Finset Cell}
    (h : FiniteTemplate HasSnaky n A H) (s : Fin 8) (t : Cell) :
    FiniteTemplate HasSnaky n (placed21 s t A) (placed21 s t H) := by
  have hh := h.transport (placementEquiv (currentCode s) t)
    (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed (currentCode s) t X hx)
  simpa only [placed21, Finset.map_eq_image, Equiv.toEmbedding,
    Function.Embedding.coeFn_mk, coe_placementEquiv] using hh

/-- Empty response sets cannot manufacture a strategy for an impossible target. -/
theorem FiniteWins.false_impossible {U : Finset α} {n M B}
    (h : FiniteWins U (fun _ => False) n M B) : False := by
  induction h with
  | done hw => exact hw
  | finish x hxU hxM hxB hw => exact hw
  | move x hxU hxM hxB ha next ih =>
    obtain ⟨b, hbU, hbM, hbB⟩ := ha
    exact ih b hbU hbM hbB

theorem FiniteWins.zero_iff {U : Finset α} {win : Finset α → Prop} {M B} :
    FiniteWins U win 0 M B ↔ win M := by
  constructor
  · intro h; cases h with | done hw => exact hw
  · exact FiniteWins.done

end FiniteCongruenceChecks.SnakyFinite
