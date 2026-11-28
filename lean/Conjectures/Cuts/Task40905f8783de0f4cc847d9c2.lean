import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Order.Interval.Finset.Nat

open Finset

private theorem fixed_shifts (X A B : ℕ) :
    (∑ m ∈ Ico X (2*X), if (m-A).Prime ∧ (m-B).Prime then (1:ℝ) else 0) =
    ∑ p ∈ range (2*X), ∑ q ∈ range (2*X),
      if p.Prime ∧ q.Prime ∧ X≤p+A ∧ p+A<2*X ∧ p+A=q+B then (1:ℝ) else 0 := by
  let S := (Ico X (2*X)).filter (fun m => (m-A).Prime ∧ (m-B).Prime)
  let T := ((range (2*X)).product (range (2*X))).filter
    (fun v => v.1.Prime ∧ v.2.Prime ∧ X≤v.1+A ∧ v.1+A<2*X ∧ v.1+A=v.2+B)
  have eq : S.card = T.card := by
    apply card_bij (fun m _ => (m-A,m-B))
    · intro m hm
      obtain ⟨ml,mr⟩ := mem_Ico.mp (mem_filter.mp hm).1
      obtain ⟨pa,pb⟩ := (mem_filter.mp hm).2
      have ha := pa.two_le
      have hb := pb.two_le
      change (m-A,m-B) ∈ T
      simp only [T,mem_filter,product_eq_sprod,mem_product,mem_range]
      exact ⟨⟨by omega,by omega⟩,pa,pb,by omega,by omega,by omega⟩
    · intro m hm n hn eq
      have a := ((mem_filter.mp hm).2.1 : (m-A).Prime).two_le
      have b := ((mem_filter.mp hn).2.1 : (n-A).Prime).two_le
      have h := congrArg Prod.fst eq
      dsimp at h
      omega
    · intro v hv
      rcases v with ⟨p,q⟩
      obtain ⟨_,hp,hq,lo,hi,heq⟩ := mem_filter.mp hv
      have hpa : p+A-A=p := by omega
      have hqb : p+A-B=q := by omega
      refine ⟨p+A,?_,?_⟩
      · exact mem_filter.mpr ⟨mem_Ico.mpr ⟨lo,hi⟩,by simpa only [hpa,hqb] using And.intro hp hq⟩
      · exact Prod.ext hpa hqb
  rw [←sum_product', sum_boole, sum_boole]
  exact congrArg (fun n : ℕ => (n:ℝ)) eq

private theorem indicator_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1:ℝ) else 0)*(if Q then (1:ℝ) else 0) =
      if P ∧ Q then (1:ℝ) else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]

theorem Conjectures.Cuts.Task40905f8783de0f4cc847d9c2 :
    ∀ (X a b c d : ℕ),
      (∑ m ∈ Ico X (2*X),
        ((Icc a b).filter (fun e => (m-2^e).Prime)).card *
        (((Icc c d).filter (fun f => (m-2^f).Prime)).card : ℝ)) =
      ∑ e ∈ Icc a b, ∑ f ∈ Icc c d,
        ∑ p ∈ range (2*X), ∑ q ∈ range (2*X),
          if p.Prime ∧ q.Prime ∧ X≤p+2^e ∧ p+2^e<2*X ∧ p+2^e=q+2^f
          then (1:ℝ) else 0 := by
  intro X a b c d
  simp_rw [←sum_boole, sum_mul, mul_sum, indicator_mul]
  rw [sum_comm]
  conv_lhs => enter [2,e]; rw [sum_comm]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro f _
  exact fixed_shifts X (2^e) (2^f)
