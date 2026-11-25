import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_tail_binning : let Z := fun (m k : ℕ) (γ : Fin m → ℝ) => Finset.univ.filter (fun j => (k:ℝ) ≤ |γ j| ∧ |γ j| < (k+1:ℕ)); ∀ (m H B : ℕ) (γ : Fin m → ℝ) (f : Fin m → ℝ), (∀ i, |γ i| < (B+1:ℕ)) → (∑ i ∈ Finset.univ.filter (fun i => (H:ℝ)≤|γ i|), f i) = ∑ k ∈ Finset.Icc H B, ∑ i ∈ Z m k γ, f i := by
  intro Z m H B γ f hB
  classical
  let T (k : ℕ) := Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j|)
  let S (k : ℕ) := Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧ |γ j| < (k+1 : ℕ))
  let tail (k : ℕ) := ∑ j ∈ T k, f j
  let shell (k : ℕ) := ∑ j ∈ S k, f j
  have hsplit (k : ℕ) : tail k = shell k + tail (k+1) := by
    have hsucc : (k : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    have heq : T k = S k ∪ T (k+1) := by
      ext j
      simp only [T, S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        by_cases ht : |γ j| < ((k+1 : ℕ) : ℝ)
        · exact Or.inl ⟨hj, ht⟩
        · exact Or.inr (le_of_not_gt ht)
      · rintro (⟨hj, _⟩ | hj)
        · exact hj
        · exact hsucc.trans hj
    have hdis : Disjoint (S k) (T (k+1)) := by
      apply Finset.disjoint_left.mpr
      intro j hj ht
      exact (not_lt_of_ge (Finset.mem_filter.mp ht).2) (Finset.mem_filter.mp hj).2.2
    change (∑ j ∈ T k, f j) = (∑ j ∈ S k, f j) + ∑ j ∈ T (k+1), f j
    rw [heq, Finset.sum_union hdis]
  have beyond (k : ℕ) (hk : B < k) : tail k = 0 := by
    have hempty : T k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hreal : ((B+1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show B + 1 ≤ k by omega)
      exact (not_lt_of_ge (hreal.trans (Finset.mem_filter.mp hj).2)) (hB j)
    simp [tail, hempty]
  change tail H = ∑ k ∈ Finset.Icc H B, shell k
  by_cases hHB : H ≤ B
  · calc
      tail H = -tail (B+1) - (-tail H) := by simp [beyond (B+1) (by omega)]
      _ = ∑ k ∈ Finset.Icc H B, ((-tail (k+1)) - (-tail k)) :=
        (Finset.sum_Icc_sub hHB (fun k => -tail k)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        linarith only [hsplit k]
  · have he : Finset.Icc H B = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hHB)
    simp [beyond H (by omega), he]