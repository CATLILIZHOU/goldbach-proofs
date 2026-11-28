import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

private theorem summand_factor {n p r v : ℕ}
    (hp : Nat.Prime p) (hr : Nat.Prime r) (hv : Nat.Prime v)
    (hrv : r < v) (hrn : ¬r ∣ n) (hn : n = p + r * v) (hpn : p ∣ n) :
    n = p * (r + 1) ∧ r + 1 ≤ p := by
  have hprod : p ∣ r * v := (Nat.dvd_add_iff_right (dvd_refl p)).mpr (hn ▸ hpn)
  have hpv : p = v := by
    rcases hp.dvd_mul.mp hprod with hpr | hpv
    · have h : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
      exact False.elim (hrn (h ▸ hpn))
    · exact (Nat.prime_dvd_prime_iff_eq hp hv).mp hpv
  constructor
  · rw [hn, hpv]
    ring
  · omega

private theorem prime_le_factor {n p q r : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hn : n = q * (r + 1))
    (hpn : p ∣ n) (hrq : r + 1 ≤ q) : p ≤ q := by
  rcases hp.dvd_mul.mp (hn ▸ hpn) with hpq | hpr
  · exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq).le
  · exact (Nat.le_of_dvd (by omega : 0 < r + 1) hpr).trans hrq

theorem Conjectures.Cuts.Taskb688ff562472faed7f30960a :
    ∀ (x1 x2 x3 x4 x5 x6 x7 : ℕ), Nat.Prime x2 → Nat.Prime x3 → Nat.Prime x4 →
      x3 < x4 → ¬x3 ∣ x1 → x1 = x2 + x3 * x4 → x2 ∣ x1 →
      Nat.Prime x5 → Nat.Prime x6 → Nat.Prime x7 → x6 < x7 → ¬x6 ∣ x1 →
      x1 = x5 + x6 * x7 → x5 ∣ x1 → x2 = x5 := by
  intro n p r v q s w hp hr hv hrv hrn hn hpn hq hs hw hsw hsn hn' hqn
  obtain ⟨factor_p, bound_p⟩ := summand_factor hp hr hv hrv hrn hn hpn
  obtain ⟨factor_q, bound_q⟩ := summand_factor hq hs hw hsw hsn hn' hqn
  exact Nat.le_antisymm (prime_le_factor hp hq factor_q hpn bound_q)
    (prime_le_factor hq hp factor_p hqn bound_p)
