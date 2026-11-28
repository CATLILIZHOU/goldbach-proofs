import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Data.Nat.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- ==== analytic infrastructure block (BMORAnalyticBlock, 136 lemmas) ====


-- ==== BMORRectFactor.lean ====


/-!
# Factoring out the zeros on a compact set

`BMORDiskFactor.exists_entire_cofactor` performs this on a closed disk. The Perron contour needs
the same statement on a **closed rectangle**, so this file generalises the argument to an
arbitrary compact set.
-/

namespace BMORRectFactor
open Complex Filter Set MeromorphicOn
open scoped Topology
noncomputable section

/-- Removing every zero on a compact set, with its exact multiplicity, gives a globally entire
cofactor that does not vanish on the set. -/
theorem exists_entire_cofactor_compact {f : ℂ→ℂ} (df : Differentiable ℂ f)
    (R : Set ℂ) (hR : IsCompact R) {c : ℂ} (fc : f c ≠ 0) :
    ∃ g : ℂ→ℂ, Differentiable ℂ g ∧ (∀ z∈R, g z≠0) ∧
      ∀ z, f z = (∏ᶠ u, (·-u) ^ (divisor f R u)) z * g z := by
  classical
  let d := divisor f R
  let P : ℂ→ℂ := ∏ᶠ u, (·-u) ^ d u
  have hfin := d.finiteSupport hR
  have a : AnalyticOnNhd ℂ f R := fun z _ => df.analyticAt z
  have whole : AnalyticOnNhd ℂ f univ := fun z _ => df.analyticAt z
  have dn : 0 ≤ d := a.divisor_nonneg
  have pa (z : ℂ) : AnalyticAt ℂ P z := Function.FactorizedRational.analyticAt (dn z)
  have noTop (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ := by
    apply whole.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ c) (mem_univ z)
    rw [(df.analyticAt c).meromorphicOrderAt_eq,(df.analyticAt c).analyticOrderAt_eq_zero.mpr fc]
    simp
  let A := P⁻¹ * f
  let g := toMeromorphicNFOn A univ
  have mA : MeromorphicOn A univ := fun z _ => (pa z).meromorphicAt.inv.mul (df.analyticAt z).meromorphicAt
  have nf (z : ℂ) : MeromorphicNFAt g z := meromorphicNFOn_toMeromorphicNFOn A univ (mem_univ z)
  have ord (z : ℂ) : meromorphicOrderAt g z = -(d z : WithTop ℤ) + meromorphicOrderAt f z := by
    change meromorphicOrderAt (toMeromorphicNFOn A univ) z = _
    rw [meromorphicOrderAt_toMeromorphicNFOn mA (mem_univ z),meromorphicOrderAt_mul (pa z).meromorphicAt.inv (df.analyticAt z).meromorphicAt,meromorphicOrderAt_inv,
      show meromorphicOrderAt P z=(d z : WithTop ℤ) from Function.FactorizedRational.meromorphicOrderAt_eq _ hfin]
  have inner (z : ℂ) (hz : z∈R) : meromorphicOrderAt g z=0 := by
    rw [ord]
    change -((divisor f R z : ℤ) : WithTop ℤ) + _ = _
    rw [a.meromorphicOn.divisor_apply hz]
    lift meromorphicOrderAt f z to ℤ using noTop z with b h
    simp
  have ga (z : ℂ) : AnalyticAt ℂ g z := by
    apply (nf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_cases hz : z∈R
    · rw [inner z hz]
    · have dz : d z=0 := by simp [d,hz]
      simpa [ord,dz] using (df.analyticAt z).meromorphicOrderAt_nonneg
  refine ⟨g,fun z => (ga z).differentiableAt, fun z hz => (nf z).meromorphicOrderAt_eq_zero_iff.mp (inner z hz),?_⟩
  intro z
  have pnt : ∀ᶠ w in 𝓝[≠] z, P w ≠0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (pa z).meromorphicAt).mp
      (Function.FactorizedRational.meromorphicOrderAt_ne_top d)
  have he : f =ᶠ[𝓝[≠] z] P*g := by
    filter_upwards [pnt,mA.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)] with w hw he
    change g w=(P w)⁻¹*f w at he
    simp [Pi.mul_apply,he,hw]
  exact tendsto_nhds_unique_of_eventuallyEq ((df z).continuousAt.continuousWithinAt)
    (((pa z).continuousAt.mul (ga z).continuousAt).continuousWithinAt) he

end
end BMORRectFactor

-- ==== BMORRectProd.lean ====


/-!
# The zero factor on a compact set as a finite product

`∏ᶠ u, (· - u)^(divisor f R u) = ∏ a ∈ roots, (· - a)^(mult a)`, the compact-set analogue of
`BMORDiskFactor.factor_prod`.
-/

namespace BMORRectFactor
open Complex Filter Set MeromorphicOn
open scoped Topology BigOperators
noncomputable section

/-- The zero factor of `f` on the compact set `R`. -/
def zeroFactorC (f : ℂ → ℂ) (R : Set ℂ) : ℂ → ℂ := ∏ᶠ u, (·-u) ^ (divisor f R u)

/-- The zeros of `f` on `R`, as a finset. -/
def rootsC (f : ℂ → ℂ) (R : Set ℂ) (hR : IsCompact R) : Finset ℂ :=
  ((divisor f R).finiteSupport hR).toFinset

/-- The multiplicity of a zero. -/
def multC (f : ℂ → ℂ) (R : Set ℂ) (a : ℂ) : ℕ := (divisor f R a).toNat

/-- The zero factor is a finite product over the zeros. -/
theorem factor_prod_compact {f : ℂ → ℂ} (df : Differentiable ℂ f) (R : Set ℂ)
    (hR : IsCompact R) (z : ℂ) :
    zeroFactorC f R z = ∏ a ∈ rootsC f R hR, (z-a)^(multC f R a) := by
  classical
  let d := divisor f R
  have hfin := d.finiteSupport hR
  have aa : AnalyticOnNhd ℂ f R := fun x _ => df.analyticAt x
  have dn : 0 ≤ d := aa.divisor_nonneg
  unfold zeroFactorC
  rw [finprod_eq_prod_of_mulSupport_subset (s := rootsC f R hR)]
  · rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro a _
    change (z-a)^(d a) = (z-a)^(d a).toNat
    rw [← zpow_natCast, Int.toNat_of_nonneg (dn a)]
  · rw [Function.FactorizedRational.mulSupport]
    simp [rootsC]

end
end BMORRectFactor

-- ==== BMORLogDerivFactor.lean ====


/-!
# The logarithmic derivative of `f = P · g`

On the boundary of the rectangle the zero factor `P` does not vanish, so `f'/f = P'/P + g'/g`
holds there pointwise.
-/

namespace BMORRectFactor
open Complex Filter Set MeromorphicOn
open scoped Topology BigOperators
noncomputable section

/-- The zero factor is entire. -/
theorem differentiable_zeroFactorC {f : ℂ → ℂ} (df : Differentiable ℂ f) (R : Set ℂ)
    (hR : IsCompact R) : Differentiable ℂ (zeroFactorC f R) := by
  have aa : AnalyticOnNhd ℂ f R := fun x _ => df.analyticAt x
  have dn : 0 ≤ divisor f R := aa.divisor_nonneg
  intro z
  exact (Function.FactorizedRational.analyticAt (dn z)).differentiableAt

/-- A point outside the compact set is not a zero of the factor. -/
theorem divisor_eq_zero_of_not_mem {f : ℂ → ℂ} {R : Set ℂ} {a : ℂ} (ha : a ∉ R) :
    divisor f R a = 0 := by
  simp [divisor, ha]

/-- The zero factor does not vanish away from the zeros. -/
theorem zeroFactorC_ne_zero {f : ℂ → ℂ} (df : Differentiable ℂ f) {R : Set ℂ}
    (hR : IsCompact R) {z : ℂ} (hz : ∀ a ∈ rootsC f R hR, z ≠ a) :
    zeroFactorC f R z ≠ 0 := by
  rw [factor_prod_compact df R hR z]
  exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (sub_ne_zero.mpr (hz a ha)))

/-- Pointwise logarithmic derivative of a factorisation `f = P·g`. -/
theorem logDeriv_factor {f g : ℂ → ℂ} (df : Differentiable ℂ f) (R : Set ℂ)
    (hR : IsCompact R) (hfg : ∀ z, f z = zeroFactorC f R z * g z)
    (hg : Differentiable ℂ g) {z : ℂ} (hz : zeroFactorC f R z ≠ 0) (hgz : g z ≠ 0) :
    logDeriv f z = logDeriv (zeroFactorC f R) z + logDeriv g z := by
  have hlhs : logDeriv (fun w => zeroFactorC f R w * g w) z = logDeriv f z := by
    congr 1
    exact (funext hfg).symm
  rw [← hlhs]
  exact logDeriv_mul z hz hgz
    (differentiable_zeroFactorC df R hR).differentiableAt hg.differentiableAt

end
end BMORRectFactor

-- ==== BMORSideIntegral.lean ====


/-!
# One-dimensional pieces of the rectangle residue computation

To evaluate `∫_{∂R} 1/(s-a) ds` along the four sides of a rectangle one needs, on each horizontal
side, the antiderivative `log (t - a)` of `t ↦ (t - a)⁻¹`. The antiderivative lives on the slit
plane, so the hypotheses are stated as "the imaginary part never vanishes", which for a horizontal
side at height `y` reduces to `y ≠ a.im`.
-/

namespace BMORProp21

open Complex

/-- Pointwise derivative of `t ↦ log (t - a)` along the real axis. -/
theorem hasDerivAt_log_sub (a : ℂ) (x : ℝ) (hx : ((x:ℂ) - a) ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log ((t:ℂ) - a)) (((x:ℂ) - a)⁻¹) x := by
  have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) - a) (1:ℂ) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const a
  have h2 : HasDerivAt Complex.log (((x:ℂ) - a)⁻¹) ((x:ℂ) - a) :=
    Complex.hasDerivAt_log hx
  simpa only [Function.comp_def, mul_one] using h2.comp x h1

/-- Fundamental theorem of calculus on a horizontal side, for the Perron kernel `1/(s-a)`. -/
theorem integral_inv_sub {a : ℂ} {x₁ x₂ : ℝ}
    (h : ∀ t ∈ Set.uIcc x₁ x₂, ((t:ℂ) - a) ∈ Complex.slitPlane) :
    ∫ t in x₁..x₂, ((t:ℂ) - a)⁻¹
      = Complex.log ((x₂:ℂ) - a) - Complex.log ((x₁:ℂ) - a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact hasDerivAt_log_sub a t (h t ht)
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht
      exact Complex.slitPlane_ne_zero (h t ht)

/-- The horizontal side at height `y` avoids the branch cut whenever `y ≠ a.im`. -/
theorem mem_slitPlane_sub {a : ℂ} {y t : ℝ} (hy : y ≠ a.im) :
    ((t:ℂ) - (a - (y:ℂ)*I)) ∈ Complex.slitPlane := by
  have hz : ((t:ℂ) - (a - (y:ℂ)*I)).im = y - a.im := by simp
  rw [Complex.mem_slitPlane_iff]
  exact Or.inr (by rw [hz]; exact sub_ne_zero.mpr hy)

/-- Integral of the Perron kernel along a horizontal segment that misses the branch cut. -/
theorem integral_inv_sub_horiz {a : ℂ} {x₁ x₂ y : ℝ} (hy : y ≠ a.im) :
    ∫ t in x₁..x₂, (((t:ℂ) + (y:ℂ)*I - a)⁻¹)
      = Complex.log ((x₂:ℂ) + (y:ℂ)*I - a) - Complex.log ((x₁:ℂ) + (y:ℂ)*I - a) := by
  have hmain : ∫ t in x₁..x₂, ((t:ℂ) - (a - (y:ℂ)*I))⁻¹
      = Complex.log ((x₂:ℂ) - (a - (y:ℂ)*I)) - Complex.log ((x₁:ℂ) - (a - (y:ℂ)*I)) := by
    apply integral_inv_sub
    intro t _
    exact mem_slitPlane_sub (a := a) (y := y) (t := t) hy
  have e : ∀ t : ℝ, ((t:ℂ) + (y:ℂ)*I - a) = ((t:ℂ) - (a - (y:ℂ)*I)) := fun t => by ring
  simp only [e]
  exact hmain

end BMORProp21

-- ==== BMORVertical.lean ====


/-!
# The vertical side of the rectangle residue computation — algebraic core

For `c ≠ 0` the vertical side contributes `∫ (c + i u)⁻¹ du`. Unlike the horizontal side, the
principal `Complex.log` is useless here: for `c < 0` the path crosses the branch cut and the
principal logarithm is neither differentiable nor continuous there.

The way out is the elementary identity

`(c + i u)⁻¹ = c/(c^2+u^2) - i·u/(c^2+u^2)`,

which splits the complex integral into two *real* integrals,

`∫ c/(c^2+u^2) du = arctan (u/c)`   and   `∫ u/(c^2+u^2) du = (1/2) log (c^2+u^2)`,

both with everywhere-continuous antiderivatives. This file records the algebraic identity.
-/

namespace BMORProp21

open Complex

/-- Splitting the Perron kernel on a vertical side into its real and imaginary parts. -/
theorem vertical_kernel_split {c u : ℝ} (hc : c ≠ 0) :
    (((c:ℂ) + (u:ℂ)*I)⁻¹) = ((c/(c^2+u^2) : ℝ) : ℂ) - I * ((u/(c^2+u^2) : ℝ) : ℂ) := by
  have h0 : (c^2 + u^2 : ℝ) ≠ 0 := by positivity
  have hne : ((c:ℂ) + (u:ℂ)*I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at hre
    exact hc hre
  refine inv_eq_of_mul_eq_one_left ?_
  push_cast
  have hden : ((c:ℂ)^2 + (u:ℂ)^2) ≠ 0 := by
    have he : ((c:ℂ)^2 + (u:ℂ)^2) = ((c^2+u^2 : ℝ) : ℂ) := by push_cast; ring
    rw [he]
    exact_mod_cast h0
  field_simp [hden]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  calc ((c:ℂ) - (u:ℂ) * Complex.I) * ((c:ℂ) + (u:ℂ) * Complex.I)
      = ((c:ℂ))^2 - ((u:ℂ))^2 * Complex.I^2 := by ring
    _ = ((c:ℂ))^2 - ((u:ℂ))^2 * (-1) := by rw [hI]
    _ = ((c:ℂ))^2 + ((u:ℂ))^2 := by ring

end BMORProp21

-- ==== BMORVerticalReal.lean ====


/-!
# The vertical side of the rectangle residue computation

For `c ≠ 0` the vertical side contributes `∫ (c + i u)⁻¹ du`. The principal `Complex.log` is
useless here: for `c < 0` the path crosses the branch cut. Instead we split

`(c + i u)⁻¹ = c/(c^2+u^2) - i·u/(c^2+u^2)`

into two real integrals whose antiderivatives are everywhere continuous:
`arctan (u/c)` and `½ log (c^2+u^2)`. No branch bookkeeping is needed.
-/

namespace BMORProp21

open Complex

/-- `c/(c^2+u^2)` is the derivative of `u ↦ arctan (u/c)`. -/
theorem hasDerivAt_arctan_div {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan (t/c)) (c/(c^2+u^2)) u := by
  have hinner : HasDerivAt (fun t : ℝ => t/c) (1/c) u := by
    simpa using (hasDerivAt_id u).div_const c
  have houter : HasDerivAt Real.arctan (1/(1+((u/c))^2)) (u/c) := Real.hasDerivAt_arctan (u/c)
  have hcomp : HasDerivAt (Real.arctan ∘ fun t : ℝ => t/c) (1/(1+((u/c))^2) * (1/c)) u :=
    houter.comp u hinner
  simp only [Function.comp_def] at hcomp
  have hval : (1/(1+((u/c))^2) * (1/c)) = c/(c^2+u^2) := by
    field_simp
  simpa only [hval] using hcomp

/-- `u/(c^2+u^2)` is the derivative of `u ↦ ½ log (c^2+u^2)`. -/
theorem hasDerivAt_half_log {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (fun t : ℝ => (1/2)*Real.log (c^2+t^2)) (u/(c^2+u^2)) u := by
  have hpos : (0:ℝ) < c^2+u^2 := by positivity
  have hinner : HasDerivAt (fun t : ℝ => c^2+t^2) (2*u) u := by
    simpa using (hasDerivAt_pow 2 u).const_add (c^2)
  have houter : HasDerivAt Real.log ((c^2+u^2)⁻¹) (c^2+u^2) := Real.hasDerivAt_log hpos.ne'
  have hcomp : HasDerivAt (Real.log ∘ fun t : ℝ => c^2+t^2) ((c^2+u^2)⁻¹ * (2*u)) u :=
    houter.comp u hinner
  simp only [Function.comp_def] at hcomp
  have hval : ((c^2+u^2)⁻¹ * (2*u)) = 2*(u/(c^2+u^2)) := by field_simp
  rw [hval] at hcomp
  have := hcomp.const_mul (1/2)
  convert this using 1
  ring

/-- The real integral of `c/(c^2+u^2)`. -/
theorem integral_arctan_div {c : ℝ} (hc : c ≠ 0) {u₁ u₂ : ℝ} :
    ∫ u in u₁..u₂, (c/(c^2+u^2))
      = Real.arctan (u₂/c) - Real.arctan (u₁/c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _
    exact hasDerivAt_arctan_div hc u
  · have hne : ∀ x : ℝ, c^2 + x^2 ≠ 0 := fun x => by positivity
    exact (continuous_const.div (by fun_prop) hne).intervalIntegrable _ _

/-- The real integral of `u/(c^2+u^2)`. -/
theorem integral_half_log {c : ℝ} (hc : c ≠ 0) {u₁ u₂ : ℝ} :
    ∫ u in u₁..u₂, (u/(c^2+u^2))
      = (1/2)*Real.log (c^2+u₂^2) - (1/2)*Real.log (c^2+u₁^2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _
    exact hasDerivAt_half_log hc u
  · have hne : ∀ x : ℝ, c^2 + x^2 ≠ 0 := fun x => by positivity
    exact (continuous_id.div (by fun_prop) hne).intervalIntegrable _ _

end BMORProp21

-- ==== BMORVerticalClosed.lean ====


/-!
# Closed form of the vertical side of the Perron rectangle

Combining the algebraic split `(c + i u)⁻¹ = c/(c²+u²) - i·u/(c²+u²)` with the two real
antiderivatives gives the closed form

`∫_{u₁}^{u₂} (c + i u)⁻¹ du = [arctan (u/c) - (i/2) log (c²+u²)]_{u₁}^{u₂}`,

valid for either sign of `c` and with no branch bookkeeping.
-/

namespace BMORProp21

open Complex

/-- The vertical side integral in closed form. -/
theorem integral_inv_vertical {c : ℝ} (hc : c ≠ 0) {u₁ u₂ : ℝ} :
    ∫ u in u₁..u₂, (((c:ℂ) + (u:ℂ)*I)⁻¹)
      = ((Real.arctan (u₂/c) : ℂ) - (I/2)*((Real.log (c^2+u₂^2) : ℝ) : ℂ))
        - ((Real.arctan (u₁/c) : ℂ) - (I/2)*((Real.log (c^2+u₁^2) : ℝ) : ℂ)) := by
  have hpt : ∀ u : ℝ, (((c:ℂ) + (u:ℂ)*I)⁻¹)
      = ((c/(c^2+u^2) : ℝ) : ℂ) - I * ((u/(c^2+u^2) : ℝ) : ℂ) :=
    fun u => vertical_kernel_split hc
  have hden : Continuous fun u : ℝ => c^2 + u^2 := continuous_const.add (continuous_id.pow 2)
  have hpos : ∀ x : ℝ, c^2 + x^2 ≠ 0 := fun x => by positivity
  have h1 : Continuous fun u : ℝ => ((c/(c^2+u^2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.div hden hpos)
  have h2 : Continuous fun u : ℝ => (I:ℂ) * ((u/(c^2+u^2) : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.div hden hpos))
  simp only [hpt]
  rw [intervalIntegral.integral_sub (h1.intervalIntegrable u₁ u₂) (h2.intervalIntegrable u₁ u₂)]
  rw [intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_ofReal]
  rw [integral_arctan_div hc, integral_half_log hc]
  push_cast
  ring

end BMORProp21

-- ==== BMORTranslate.lean ====


/-!
# Translating the Perron rectangle to the origin

The four side computations are all statements about `s - a`. Translating the rectangle by `a`
reduces every one of them to the case `a = 0`, which removes the dependence on `a` from the
branch bookkeeping. This file records the two translation identities.
-/

namespace BMORProp21

open Complex

/-- Horizontal side: translating the rectangle by `a`. -/
theorem horizontal_translate {a : ℂ} {x₁ x₂ y : ℝ} :
    ∫ x in x₁..x₂, (((x:ℂ) + (y:ℂ)*I - a)⁻¹)
      = ∫ u in (x₁ - a.re)..(x₂ - a.re),
          (((u:ℂ) + ((y - a.im):ℝ)*I)⁻¹) := by
  have key := intervalIntegral.integral_comp_add_right (a := x₁) (b := x₂) (d := -a.re)
    (f := fun u : ℝ => (((u:ℂ) + ((y - a.im):ℝ)*I)⁻¹))
  have hshift : ∀ x : ℝ, (((x + (-a.re):ℝ):ℂ) + ((y + (-a.im):ℝ):ℂ)*I)
      = ((x:ℂ) + (y:ℂ)*I - a) := by
    intro x
    apply Complex.ext <;> simp <;> ring
  simpa only [hshift, sub_eq_add_neg] using key

/-- Vertical side: translating the rectangle by `a`. -/
theorem vertical_translate {a : ℂ} {y₁ y₂ x : ℝ} :
    ∫ y in y₁..y₂, (((x:ℂ) + (y:ℂ)*I - a)⁻¹)
      = ∫ v in (y₁ - a.im)..(y₂ - a.im),
          ((((x - a.re):ℝ):ℂ) + (v:ℂ)*I)⁻¹ := by
  have key := intervalIntegral.integral_comp_add_right (a := y₁) (b := y₂) (d := -a.im)
    (f := fun v : ℝ => ((((x - a.re):ℝ):ℂ) + (v:ℂ)*I)⁻¹)
  have hshift : ∀ y : ℝ, (((x + (-a.re):ℝ):ℂ) + ((y + (-a.im):ℝ):ℂ)*I)
      = ((x:ℂ) + (y:ℂ)*I - a) := by
    intro y
    apply Complex.ext <;> simp <;> ring
  simpa only [hshift, sub_eq_add_neg] using key

end BMORProp21

-- ==== BMORArg.lean ====


/-!
# The argument of a point in a quadrant

For the residue computation on the Perron rectangle one needs `Complex.arg` of the four corners
after translating to the origin. Each corner has `re ≠ 0` and `im ≠ 0`, so it lies in the interior
of a quadrant. This file proves the three non-right-quadrant cases:

* `u > 0`          : `arg (u + v·i) = arctan (v/u)`;
* `u < 0`, `v > 0` : `arg (u + v·i) = arctan (v/u) + π`;
* `u < 0`, `v < 0` : `arg (u + v·i) = arctan (v/u) - π`.
-/

namespace BMORProp21

open Complex

/-- Packaging step: if `cos θ = u/r` and `sin θ = v/r` then `u + v·i = r·(cos θ + sin θ·i)`. -/
theorem repr_of {u v r θ : ℝ} (hr : 0 < r)
    (hcos : Real.cos θ = u/r) (hsin : Real.sin θ = v/r) :
    ((u:ℂ) + (v:ℂ)*I) = (r:ℂ) * (Real.cos θ + Real.sin θ * I) := by
  have hrne : r ≠ 0 := hr.ne'
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero, hcos]
    field_simp
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, hsin]
    field_simp
    ring

/-- The elementary identity `1 + (v/u)² = (u²+v²)/u²`, proved by avoiding inverses. -/
theorem one_add_sq_div {u v : ℝ} (hu : u ≠ 0) :
    (1 + (v/u)^2) = (u^2+v^2)/u^2 := by
  rw [div_pow, show (1:ℝ) = u^2/u^2 from by field_simp, ← add_div]

/-- Right half-plane: the modulus form. -/
theorem repr_pos {u v : ℝ} (hu : 0 < u) :
    ((u:ℂ) + (v:ℂ)*I) = ((Real.sqrt (u^2+v^2):ℝ):ℂ) *
      (Real.cos (Real.arctan (v/u)) + Real.sin (Real.arctan (v/u)) * I) := by
  have hr : (0:ℝ) < Real.sqrt (u^2+v^2) := Real.sqrt_pos.mpr (by positivity)
  have h1 := one_add_sq_div (v := v) hu.ne'
  refine repr_of hr ?_ ?_
  · rw [Real.cos_arctan, h1, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (le_of_lt hu),
      one_div, inv_div]
  · rw [Real.sin_arctan, h1, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (le_of_lt hu)]
    field_simp

/-- The principal argument in the right half-plane. -/
theorem arg_pos {u v : ℝ} (hu : 0 < u) :
    Complex.arg ((u:ℂ) + (v:ℂ)*I) = Real.arctan (v/u) := by
  have hr : (0:ℝ) < Real.sqrt (u^2+v^2) := Real.sqrt_pos.mpr (by positivity)
  have hlo : -(Real.pi) < Real.arctan (v/u) := by
    have := Real.neg_pi_div_two_lt_arctan (v/u); linarith [Real.pi_pos]
  have hhi : Real.arctan (v/u) ≤ Real.pi := by
    have := Real.arctan_lt_pi_div_two (v/u); linarith [Real.pi_pos]
  have h := Complex.arg_mul_cos_add_sin_mul_I (r := Real.sqrt (u^2+v^2))
    (θ := Real.arctan (v/u)) hr ⟨hlo, hhi⟩
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  rwa [← repr_pos hu] at h

/-- Left half-plane: cosine and sine of the unshifted arctangent. -/
theorem cos_sin_of_neg {u v : ℝ} (hu : u < 0) :
    Real.cos (Real.arctan (v/u)) = (-u) / Real.sqrt (u^2+v^2) ∧
      Real.sin (Real.arctan (v/u)) = (-v) / Real.sqrt (u^2+v^2) := by
  have hu0 : u ≠ 0 := hu.ne
  have h1 := one_add_sq_div (v := v) hu0
  have hsq : Real.sqrt (u^2) = -u := by
    rw [Real.sqrt_sq_eq_abs, abs_of_neg hu]
  have hsqpos : (0:ℝ) < Real.sqrt (u^2+v^2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg v, (show (0:ℝ) < u^2 by nlinarith [hu])])
  constructor
  · rw [Real.cos_arctan, h1, Real.sqrt_div' _ (by positivity), hsq, one_div, inv_div]
  · rw [Real.sin_arctan, h1, Real.sqrt_div' _ (by positivity), hsq]
    field_simp

/-- Upper-left quadrant. -/
theorem repr_neg_pos {u v : ℝ} (hu : u < 0) (hv : 0 < v) :
    ((u:ℂ) + (v:ℂ)*I) = ((Real.sqrt (u^2+v^2):ℝ):ℂ) *
      (Real.cos (Real.arctan (v/u) + Real.pi) + Real.sin (Real.arctan (v/u) + Real.pi) * I) := by
  obtain ⟨hc, hs⟩ := cos_sin_of_neg (v := v) hu
  have hr : (0:ℝ) < Real.sqrt (u^2+v^2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg v, (show (0:ℝ) < u^2 by nlinarith [hu])])
  refine repr_of hr ?_ ?_
  · rw [Real.cos_add_pi, hc]; ring
  · rw [Real.sin_add_pi, hs]; ring

/-- Lower-left quadrant. -/
theorem repr_neg_neg {u v : ℝ} (hu : u < 0) (hv : v < 0) :
    ((u:ℂ) + (v:ℂ)*I) = ((Real.sqrt (u^2+v^2):ℝ):ℂ) *
      (Real.cos (Real.arctan (v/u) - Real.pi) + Real.sin (Real.arctan (v/u) - Real.pi) * I) := by
  obtain ⟨hc, hs⟩ := cos_sin_of_neg (v := v) hu
  have hr : (0:ℝ) < Real.sqrt (u^2+v^2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg v, (show (0:ℝ) < u^2 by nlinarith [hu])])
  refine repr_of hr ?_ ?_
  · rw [Real.cos_sub_pi, hc]; ring
  · rw [Real.sin_sub_pi, hs]; ring

/-- The principal argument in the upper-left quadrant. -/
theorem arg_neg_pos {u v : ℝ} (hu : u < 0) (hv : 0 < v) :
    Complex.arg ((u:ℂ) + (v:ℂ)*I) = Real.arctan (v/u) + Real.pi := by
  have hr : (0:ℝ) < Real.sqrt (u^2+v^2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg v, (show (0:ℝ) < u^2 by nlinarith [hu])])
  have hneg : v/u < 0 := div_neg_of_pos_of_neg hv hu
  have harc : Real.arctan (v/u) < 0 := by
    have h := Real.arctan_lt_arctan_iff.mpr hneg
    simpa using h
  have hlo : -(Real.pi) < Real.arctan (v/u) + Real.pi := by
    have := Real.neg_pi_div_two_lt_arctan (v/u); linarith [Real.pi_pos]
  have hhi : Real.arctan (v/u) + Real.pi ≤ Real.pi := by linarith
  have h := Complex.arg_mul_cos_add_sin_mul_I (r := Real.sqrt (u^2+v^2))
    (θ := Real.arctan (v/u) + Real.pi) hr ⟨hlo, hhi⟩
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  rwa [← repr_neg_pos hu hv] at h

/-- The principal argument in the lower-left quadrant. -/
theorem arg_neg_neg {u v : ℝ} (hu : u < 0) (hv : v < 0) :
    Complex.arg ((u:ℂ) + (v:ℂ)*I) = Real.arctan (v/u) - Real.pi := by
  have hr : (0:ℝ) < Real.sqrt (u^2+v^2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg v, (show (0:ℝ) < u^2 by nlinarith [hu])])
  have hpos : 0 < v/u := div_pos_of_neg_of_neg hv hu
  have harc : 0 < Real.arctan (v/u) := by
    have h := Real.arctan_lt_arctan_iff.mpr hpos
    simpa using h
  have hlo : -(Real.pi) < Real.arctan (v/u) - Real.pi := by
    have := Real.arctan_lt_pi_div_two (v/u); linarith [Real.pi_pos]
  have hhi : Real.arctan (v/u) - Real.pi ≤ Real.pi := by
    have := Real.arctan_lt_pi_div_two (v/u); linarith [Real.pi_pos]
  have h := Complex.arg_mul_cos_add_sin_mul_I (r := Real.sqrt (u^2+v^2))
    (θ := Real.arctan (v/u) - Real.pi) hr ⟨hlo, hhi⟩
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  rwa [← repr_neg_neg hu hv] at h

end BMORProp21

-- ==== BMORBoundary.lean ====


/-!
# The Perron rectangle integral equals `2πi` — real part
-/

namespace BMORProp21

open Complex

/-- The real part of `log (U + V·i)` in terms of `log (U² + V²)`. -/
theorem log_re_of_real_add {U V : ℝ} :
    (Complex.log ((U:ℂ) + (V:ℂ)*I)).re = (1/2) * Real.log (U^2 + V^2) := by
  rw [Complex.log_re, Complex.norm_def, Complex.normSq_add_mul_I]
  rw [Real.log_sqrt (show (0:ℝ) ≤ U^2 + V^2 by positivity)]
  ring

/-- The constant `(i/2).im` is `1/2`. -/
theorem im_I_half : ((I * (1/2) : ℂ)).im = (1/2 : ℝ) := by
  norm_num [Complex.mul_im]

/-- Horizontal side of the rectangle. -/
noncomputable def sideH (U₁ U₂ V : ℝ) : ℂ :=
  ∫ x in U₁..U₂, ((x:ℂ) + (V:ℂ)*I)⁻¹

/-- Vertical side of the rectangle. -/
noncomputable def sideV (U V₁ V₂ : ℝ) : ℂ :=
  ∫ y in V₁..V₂, ((U:ℂ) + (y:ℂ)*I)⁻¹

end BMORProp21

-- ==== BMORSideVParts.lean ====


/-!
# Real and imaginary parts of the vertical side

The closed form `∫ (c + i u)⁻¹ du = [arctan (u/c) - (i/2) log (c²+u²)]` is split into its real
and imaginary parts once and for all, so that later assemblies only see real numbers and the
fiddly `(i/2)` coefficient never enters the goal.
-/

namespace BMORProp21

open Complex

/-- Real part of the vertical side. -/
theorem sideV_re {c u₁ u₂ : ℝ} (hc : c ≠ 0) :
    (∫ u in u₁..u₂, ((c:ℂ) + (u:ℂ)*I)⁻¹).re
      = Real.arctan (u₂/c) - Real.arctan (u₁/c) := by
  have h2 : ((2:ℂ)).im = 0 := by norm_num
  rw [integral_inv_vertical (c := c) hc]
  simp only [h2, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_ofNat, zero_mul, mul_zero, one_mul, mul_one,
    sub_zero, zero_sub, add_zero, neg_zero, Complex.ofReal_sub]
  ring

/-- Imaginary part of the vertical side. -/
theorem sideV_im {c u₁ u₂ : ℝ} (hc : c ≠ 0) :
    (∫ u in u₁..u₂, ((c:ℂ) + (u:ℂ)*I)⁻¹).im
      = (1/2) * (Real.log (c^2+u₁^2) - Real.log (c^2+u₂^2)) := by
  rw [integral_inv_vertical (c := c) hc]
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_ofNat,
    zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, add_zero, neg_zero,
    Complex.ofReal_sub]
  norm_num
  ring

end BMORProp21

-- ==== BMORSideParts.lean ====


/-!
# Real part of the Perron rectangle boundary

With both sides split into real and imaginary parts, the vanishing of the real part of the
boundary integral is a bookkeeping identity on logarithms.
-/

namespace BMORProp21

open Complex

/-- Real part of the horizontal side. -/
theorem sideH_re {U₁ U₂ V : ℝ} (hV : V ≠ 0) :
    (∫ x in U₁..U₂, ((x:ℂ) + (V:ℂ)*I)⁻¹).re
      = (1/2) * (Real.log (U₂^2+V^2) - Real.log (U₁^2+V^2)) := by
  have h := integral_inv_sub_horiz (a := 0) (x₁ := U₁) (x₂ := U₂) (y := V) (by simpa using hV)
  rw [show (∫ x in U₁..U₂, ((x:ℂ) + (V:ℂ)*I)⁻¹)
      = Complex.log ((U₂:ℂ) + (V:ℂ)*I) - Complex.log ((U₁:ℂ) + (V:ℂ)*I) from by
    simpa only [sub_zero] using h]
  simp only [Complex.sub_re]
  rw [log_re_of_real_add (U := U₂) (V := V), log_re_of_real_add (U := U₁) (V := V)]
  ring

/-- The real part of the boundary integral vanishes. -/
theorem boundary_re_zero {U₁ U₂ V₁ V₂ : ℝ} (h1 : U₁ < 0) (h2 : 0 < U₂)
    (h3 : V₁ < 0) (h4 : 0 < V₂) :
    ((∫ x in U₁..U₂, ((x:ℂ) + (V₁:ℂ)*I)⁻¹) - (∫ x in U₁..U₂, ((x:ℂ) + (V₂:ℂ)*I)⁻¹)
      + I*(∫ y in V₁..V₂, ((U₂:ℂ) + (y:ℂ)*I)⁻¹)
      - I*(∫ y in V₁..V₂, ((U₁:ℂ) + (y:ℂ)*I)⁻¹)).re = 0 := by
  have hv1 : (V₁:ℝ) ≠ 0 := ne_of_lt h3
  have hv2 : (V₂:ℝ) ≠ 0 := ne_of_gt h4
  have hu1 : (U₁:ℝ) ≠ 0 := ne_of_lt h1
  have hu2 : (U₂:ℝ) ≠ 0 := ne_of_gt h2
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, zero_mul, one_mul, mul_zero, sub_zero, zero_sub, add_zero]
  rw [sideH_re (U₁ := U₁) (U₂ := U₂) (V := V₁) hv1,
      sideH_re (U₁ := U₁) (U₂ := U₂) (V := V₂) hv2,
      sideV_im (c := U₂) (u₁ := V₁) (u₂ := V₂) hu2,
      sideV_im (c := U₁) (u₁ := V₁) (u₂ := V₂) hu1]
  ring

end BMORProp21

-- ==== BMORSideIm.lean ====


/-!
# Imaginary part of the Perron rectangle boundary equals `2π`

With both sides split and the three quadrant formulas for `Complex.arg` available, the imaginary
part of the boundary integral is a bookkeeping identity on arctangents plus the two `±π` branch
shifts, and equals `2π`.
-/

namespace BMORProp21

open Complex

/-- Imaginary part of the horizontal side. -/
theorem sideH_im {U₁ U₂ V : ℝ} (hV : V ≠ 0) :
    (∫ x in U₁..U₂, ((x:ℂ) + (V:ℂ)*I)⁻¹).im
      = Complex.arg ((U₂:ℂ) + (V:ℂ)*I) - Complex.arg ((U₁:ℂ) + (V:ℂ)*I) := by
  have h := integral_inv_sub_horiz (a := 0) (x₁ := U₁) (x₂ := U₂) (y := V) (by simpa using hV)
  rw [show (∫ x in U₁..U₂, ((x:ℂ) + (V:ℂ)*I)⁻¹)
      = Complex.log ((U₂:ℂ) + (V:ℂ)*I) - Complex.log ((U₁:ℂ) + (V:ℂ)*I) from by
    simpa only [sub_zero] using h]
  simp only [Complex.sub_im, Complex.log_im]

/-- The imaginary part of the boundary integral is `2π`. -/
theorem boundary_im_eq {U₁ U₂ V₁ V₂ : ℝ} (h1 : U₁ < 0) (h2 : 0 < U₂)
    (h3 : V₁ < 0) (h4 : 0 < V₂) :
    ((∫ x in U₁..U₂, ((x:ℂ) + (V₁:ℂ)*I)⁻¹) - (∫ x in U₁..U₂, ((x:ℂ) + (V₂:ℂ)*I)⁻¹)
      + I*(∫ y in V₁..V₂, ((U₂:ℂ) + (y:ℂ)*I)⁻¹)
      - I*(∫ y in V₁..V₂, ((U₁:ℂ) + (y:ℂ)*I)⁻¹)).im = 2 * Real.pi := by
  have hv1 : (V₁:ℝ) ≠ 0 := ne_of_lt h3
  have hv2 : (V₂:ℝ) ≠ 0 := ne_of_gt h4
  have hu1 : (U₁:ℝ) ≠ 0 := ne_of_lt h1
  have hu2 : (U₂:ℝ) ≠ 0 := ne_of_gt h2
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, mul_one,
    sub_zero, zero_sub, add_zero]
  rw [sideH_im (U₁ := U₁) (U₂ := U₂) (V := V₁) hv1,
      sideH_im (U₁ := U₁) (U₂ := U₂) (V := V₂) hv2,
      sideV_re (c := U₂) (u₁ := V₁) (u₂ := V₂) hu2,
      sideV_re (c := U₁) (u₁ := V₁) (u₂ := V₂) hu1]
  rw [arg_pos (u := U₂) (v := V₁) h2, arg_pos (u := U₂) (v := V₂) h2,
      arg_neg_neg (u := U₁) (v := V₁) h1 h3, arg_neg_pos (u := U₁) (v := V₂) h1 h4]
  ring


/-- The boundary integral of `1/(s - 0)` around the rectangle equals `2πi`. -/
theorem rectangle_residue {U₁ U₂ V₁ V₂ : ℝ} (h1 : U₁ < 0) (h2 : 0 < U₂)
    (h3 : V₁ < 0) (h4 : 0 < V₂) :
    (∫ x in U₁..U₂, ((x:ℂ) + (V₁:ℂ)*I)⁻¹) - (∫ x in U₁..U₂, ((x:ℂ) + (V₂:ℂ)*I)⁻¹)
      + I*(∫ y in V₁..V₂, ((U₂:ℂ) + (y:ℂ)*I)⁻¹)
      - I*(∫ y in V₁..V₂, ((U₁:ℂ) + (y:ℂ)*I)⁻¹) = 2 * (Real.pi : ℂ) * I := by
  apply Complex.ext
  · rw [boundary_re_zero h1 h2 h3 h4]
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  · rw [boundary_im_eq h1 h2 h3 h4]
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
end BMORProp21

-- ==== BMORResidueAt.lean ====


/-!
# The rectangle residue at an arbitrary pole, and the vanishing of entire boundary integrals

Two building blocks for the cross-zero identity:

* `rectangle_residue_at`: `∫_{∂R} (s - a)⁻¹ ds = 2πi` for `a` strictly inside the rectangle
  (translation of `rectangle_residue`);
* `boundary_entire_zero`: `∫_{∂R} g = 0` for entire `g` (Mathlib's Cauchy–Goursat for rectangles).
-/

namespace BMORProp21

open Complex

/-- The boundary integral of `(s - a)⁻¹` is `2πi` when `a` is strictly inside the rectangle. -/
theorem rectangle_residue_at {a : ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hx1 : x₁ < a.re) (hx2 : a.re < x₂) (hy1 : y₁ < a.im) (hy2 : a.im < y₂) :
    (∫ x in x₁..x₂, (((x:ℂ) + (y₁:ℂ)*I) - a)⁻¹)
      - (∫ x in x₁..x₂, (((x:ℂ) + (y₂:ℂ)*I) - a)⁻¹)
      + I*(∫ y in y₁..y₂, (((x₂:ℂ) + (y:ℂ)*I) - a)⁻¹)
      - I*(∫ y in y₁..y₂, (((x₁:ℂ) + (y:ℂ)*I) - a)⁻¹) = 2 * (Real.pi : ℂ) * I := by
  rw [horizontal_translate (a := a) (x₁ := x₁) (x₂ := x₂) (y := y₁),
      horizontal_translate (a := a) (x₁ := x₁) (x₂ := x₂) (y := y₂),
      vertical_translate (a := a) (y₁ := y₁) (y₂ := y₂) (x := x₂),
      vertical_translate (a := a) (y₁ := y₁) (y₂ := y₂) (x := x₁)]
  exact rectangle_residue (by linarith) (by linarith) (by linarith) (by linarith)

/-- The boundary integral of an entire function vanishes. -/
theorem boundary_entire_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g) {x₁ x₂ y₁ y₂ : ℝ} :
    (∫ x in x₁..x₂, g ((x:ℂ) + (y₁:ℂ)*I)) - (∫ x in x₁..x₂, g ((x:ℂ) + (y₂:ℂ)*I))
      + I*(∫ y in y₁..y₂, g ((x₂:ℂ) + (y:ℂ)*I))
      - I*(∫ y in y₁..y₂, g ((x₁:ℂ) + (y:ℂ)*I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    (fun z _ => (hg.differentiableAt).differentiableWithinAt)
  simpa using h

end BMORProp21

-- ==== BMORWeighted.lean ====


/-!
# Weighted residue on a rectangle — algebraic core

`∫_{∂R} g(s)/(s-a) ds = 2πi·g(a)` for an entire `g` and a pole `a` strictly inside the rectangle.
The proof avoids constructing the removable singularity by hand: Mathlib's `dslope g a` is already
entire, and `g(s)/(s-a) = dslope g a s + g(a)/(s-a)`.
-/

namespace BMORProp21

open Complex Filter Set
open scoped Topology

/-- `dslope g a z = (g z - g a)/(z - a)` away from `a`. -/
theorem dslope_eq {g : ℂ → ℂ} {a z : ℂ} (hz : z ≠ a) :
    dslope g a z = (z - a)⁻¹ * (g z - g a) := by
  rw [dslope_of_ne g hz, slope_def_field]
  ring

/-- `dslope g a` is entire when `g` is. -/
theorem differentiable_dslope {g : ℂ → ℂ} (hg : Differentiable ℂ g) (a : ℂ) :
    Differentiable ℂ (dslope g a) := by
  have h : DifferentiableOn ℂ (dslope g a) univ :=
    (Complex.differentiableOn_dslope (f := g) (c := a) (s := univ) (by simp)).mpr
      (fun z _ => (hg.differentiableAt).differentiableWithinAt)
  exact differentiableOn_univ.mp h

/-- Pointwise splitting of `g(s)/(s-a)` into an entire part and a simple pole. -/
theorem div_sub_split {g : ℂ → ℂ} {a z : ℂ} (hz : z ≠ a) :
    g z * (z - a)⁻¹ = dslope g a z + g a * (z - a)⁻¹ := by
  rw [dslope_eq hz]
  field_simp
  ring

end BMORProp21

-- ==== BMORWeightedResidue.lean ====


/-!
# Weighted residue on a rectangle

`∫_{∂R} g(s)/(s-a) ds = 2πi·g(a)` for an entire `g` and a pole `a` strictly inside the rectangle.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- Continuity of a horizontal parametrisation. -/
theorem cont_h (y : ℝ) : Continuous fun x : ℝ => ((x:ℂ) + (y:ℂ)*I) :=
  Complex.continuous_ofReal.add continuous_const

/-- Continuity of a vertical parametrisation. -/
theorem cont_v (x : ℝ) : Continuous fun y : ℝ => ((x:ℂ) + (y:ℂ)*I) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- The weighted residue on a rectangle. -/
theorem boundary_weighted_residue {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a : ℂ}
    {x₁ x₂ y₁ y₂ : ℝ} (hx1 : x₁ < a.re) (hx2 : a.re < x₂)
    (hy1 : y₁ < a.im) (hy2 : a.im < y₂) :
    (∫ x in x₁..x₂, g ((x:ℂ) + (y₁:ℂ)*I) * (((x:ℂ) + (y₁:ℂ)*I) - a)⁻¹)
      - (∫ x in x₁..x₂, g ((x:ℂ) + (y₂:ℂ)*I) * (((x:ℂ) + (y₂:ℂ)*I) - a)⁻¹)
      + I*(∫ y in y₁..y₂, g ((x₂:ℂ) + (y:ℂ)*I) * (((x₂:ℂ) + (y:ℂ)*I) - a)⁻¹)
      - I*(∫ y in y₁..y₂, g ((x₁:ℂ) + (y:ℂ)*I) * (((x₁:ℂ) + (y:ℂ)*I) - a)⁻¹)
    = 2 * (Real.pi : ℂ) * I * g a := by
  have hds : Differentiable ℂ (dslope g a) := differentiable_dslope hg a
  have hneH1 : ∀ x : ℝ, ((x:ℂ) + (y₁:ℂ)*I) ≠ a := by
    intro x h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hneH2 : ∀ x : ℝ, ((x:ℂ) + (y₂:ℂ)*I) ≠ a := by
    intro x h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hneV2 : ∀ y : ℝ, ((x₂:ℂ) + (y:ℂ)*I) ≠ a := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hneV1 : ∀ y : ℝ, ((x₁:ℂ) + (y:ℂ)*I) ≠ a := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  -- integrability of the four entire parts
  have iD1 : IntervalIntegrable (fun x : ℝ => dslope g a ((x:ℂ) + (y₁:ℂ)*I)) volume x₁ x₂ :=
    (hds.continuous.comp (cont_h y₁)).intervalIntegrable _ _
  have iD2 : IntervalIntegrable (fun x : ℝ => dslope g a ((x:ℂ) + (y₂:ℂ)*I)) volume x₁ x₂ :=
    (hds.continuous.comp (cont_h y₂)).intervalIntegrable _ _
  have iD3 : IntervalIntegrable (fun y : ℝ => dslope g a ((x₂:ℂ) + (y:ℂ)*I)) volume y₁ y₂ :=
    (hds.continuous.comp (cont_v x₂)).intervalIntegrable _ _
  have iD4 : IntervalIntegrable (fun y : ℝ => dslope g a ((x₁:ℂ) + (y:ℂ)*I)) volume y₁ y₂ :=
    (hds.continuous.comp (cont_v x₁)).intervalIntegrable _ _
  -- integrability of the four pole parts
  have iV1 : IntervalIntegrable (fun x : ℝ => g a * (((x:ℂ) + (y₁:ℂ)*I) - a)⁻¹) volume x₁ x₂ := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.mul continuousOn_const
      (ContinuousOn.inv₀ ((cont_h y₁).continuousOn.sub continuousOn_const)
        (fun x _ => sub_ne_zero.mpr (hneH1 x)))
  have iV2 : IntervalIntegrable (fun x : ℝ => g a * (((x:ℂ) + (y₂:ℂ)*I) - a)⁻¹) volume x₁ x₂ := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.mul continuousOn_const
      (ContinuousOn.inv₀ ((cont_h y₂).continuousOn.sub continuousOn_const)
        (fun x _ => sub_ne_zero.mpr (hneH2 x)))
  have iV3 : IntervalIntegrable (fun y : ℝ => g a * (((x₂:ℂ) + (y:ℂ)*I) - a)⁻¹) volume y₁ y₂ := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.mul continuousOn_const
      (ContinuousOn.inv₀ ((cont_v x₂).continuousOn.sub continuousOn_const)
        (fun y _ => sub_ne_zero.mpr (hneV2 y)))
  have iV4 : IntervalIntegrable (fun y : ℝ => g a * (((x₁:ℂ) + (y:ℂ)*I) - a)⁻¹) volume y₁ y₂ := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.mul continuousOn_const
      (ContinuousOn.inv₀ ((cont_v x₁).continuousOn.sub continuousOn_const)
        (fun y _ => sub_ne_zero.mpr (hneV1 y)))
  have hH1 : ∫ x in x₁..x₂, g ((x:ℂ) + (y₁:ℂ)*I) * (((x:ℂ) + (y₁:ℂ)*I) - a)⁻¹
      = (∫ x in x₁..x₂, dslope g a ((x:ℂ) + (y₁:ℂ)*I))
        + g a * (∫ x in x₁..x₂, (((x:ℂ) + (y₁:ℂ)*I) - a)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add iD1 iV1]
    apply intervalIntegral.integral_congr
    intro x _
    exact div_sub_split (hneH1 x)
  have hH2 : ∫ x in x₁..x₂, g ((x:ℂ) + (y₂:ℂ)*I) * (((x:ℂ) + (y₂:ℂ)*I) - a)⁻¹
      = (∫ x in x₁..x₂, dslope g a ((x:ℂ) + (y₂:ℂ)*I))
        + g a * (∫ x in x₁..x₂, (((x:ℂ) + (y₂:ℂ)*I) - a)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add iD2 iV2]
    apply intervalIntegral.integral_congr
    intro x _
    exact div_sub_split (hneH2 x)
  have hV2 : ∫ y in y₁..y₂, g ((x₂:ℂ) + (y:ℂ)*I) * (((x₂:ℂ) + (y:ℂ)*I) - a)⁻¹
      = (∫ y in y₁..y₂, dslope g a ((x₂:ℂ) + (y:ℂ)*I))
        + g a * (∫ y in y₁..y₂, (((x₂:ℂ) + (y:ℂ)*I) - a)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add iD3 iV3]
    apply intervalIntegral.integral_congr
    intro y _
    exact div_sub_split (hneV2 y)
  have hV1 : ∫ y in y₁..y₂, g ((x₁:ℂ) + (y:ℂ)*I) * (((x₁:ℂ) + (y:ℂ)*I) - a)⁻¹
      = (∫ y in y₁..y₂, dslope g a ((x₁:ℂ) + (y:ℂ)*I))
        + g a * (∫ y in y₁..y₂, (((x₁:ℂ) + (y:ℂ)*I) - a)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add iD4 iV4]
    apply intervalIntegral.integral_congr
    intro y _
    exact div_sub_split (hneV1 y)
  rw [hH1, hH2, hV2, hV1]
  have hz := boundary_entire_zero hds (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂)
  have hr := rectangle_residue_at (a := a) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂)
    hx1 hx2 hy1 hy2
  linear_combination hz + g a * hr

end BMORProp21

-- ==== BMORCpowResidue.lean ====


/-!
# The Perron residue with the `x^s` weight

`∫_{∂R} x^s/(s-ρ) ds = 2πi·x^ρ` for `x ≠ 0` and `ρ` strictly inside the rectangle. This is the
statement that turns each zero `ρ` of `L` into a contribution `m_ρ·x^ρ`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- `s ↦ x^s` is entire for `x ≠ 0`. -/
theorem differentiable_cpow_const {x : ℂ} (hx : x ≠ 0) :
    Differentiable ℂ (fun s : ℂ => x ^ s) := by
  have h : (fun s : ℂ => x ^ s) = (fun s : ℂ => Complex.exp (Complex.log x * s)) := by
    funext s
    exact cpow_def_of_ne_zero hx s
  rw [h]
  have hlin : Differentiable ℂ (fun s : ℂ => Complex.log x * s) :=
    (differentiable_const (c := Complex.log x)).mul differentiable_id
  exact Complex.differentiable_exp.comp hlin

/-- The weighted residue at a zero `ρ`. -/
theorem boundary_cpow_residue {x : ℂ} (hx : x ≠ 0) {ρ : ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (h1 : x₁ < ρ.re) (h2 : ρ.re < x₂) (h3 : y₁ < ρ.im) (h4 : ρ.im < y₂) :
    (∫ t in x₁..x₂, x ^ ((t:ℂ) + (y₁:ℂ)*I) * (((t:ℂ) + (y₁:ℂ)*I) - ρ)⁻¹)
      - (∫ t in x₁..x₂, x ^ ((t:ℂ) + (y₂:ℂ)*I) * (((t:ℂ) + (y₂:ℂ)*I) - ρ)⁻¹)
      + I*(∫ t in y₁..y₂, x ^ ((x₂:ℂ) + (t:ℂ)*I) * (((x₂:ℂ) + (t:ℂ)*I) - ρ)⁻¹)
      - I*(∫ t in y₁..y₂, x ^ ((x₁:ℂ) + (t:ℂ)*I) * (((x₁:ℂ) + (t:ℂ)*I) - ρ)⁻¹)
    = 2 * (Real.pi : ℂ) * I * x ^ ρ :=
  boundary_weighted_residue (differentiable_cpow_const hx) h1 h2 h3 h4

end BMORProp21

-- ==== BMORLogDerivProd.lean ====


/-!
# Logarithmic derivative of a finite product of powers

`(∏_{ρ ∈ σ} (· - ρ)^{m ρ})' / (∏ ...) = Σ_{ρ ∈ σ} m ρ / (s - ρ)`.

This turns the principal part `P'/P` of `L'/L` into a finite sum of simple poles, which is what
the weighted residue formula is applied to.
-/

namespace BMORProp21

open Complex

/-- The logarithmic derivative of `z ↦ z - ρ`. -/
theorem logDeriv_sub_const (s ρ : ℂ) : logDeriv (fun z : ℂ => z - ρ) s = (s - ρ)⁻¹ := by
  simp [logDeriv_apply, sub_eq_add_neg]

/-- The logarithmic derivative of a finite product of powers. -/
theorem logDeriv_prod_pow {σ : Finset ℂ} {m : ℂ → ℕ} {s : ℂ}
    (hs : ∀ ρ ∈ σ, s ≠ ρ) :
    logDeriv (fun z : ℂ => ∏ ρ ∈ σ, (z - ρ)^(m ρ)) s
      = ∑ ρ ∈ σ, (m ρ : ℂ) / (s - ρ) := by
  have hfun : (fun z : ℂ => ∏ ρ ∈ σ, (z - ρ)^(m ρ))
      = (∏ ρ ∈ σ, fun z : ℂ => (z - ρ)^(m ρ)) := by
    funext z
    rw [Finset.prod_apply]
  rw [hfun, logDeriv_prod]
  · refine Finset.sum_congr rfl ?_
    intro ρ hρ
    rw [logDeriv_fun_pow (f := fun z : ℂ => z - ρ) (n := m ρ) (differentiableAt_id.sub_const ρ), logDeriv_sub_const]
    field_simp
  · intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (hs ρ hρ))
  · intro ρ hρ
    fun_prop

end BMORProp21

-- ==== BMORSumInterchange.lean ====


/-!
# Interchanging a finite sum with a segment integral

`∫_a^b Σ_i c_i * f_i(t) dt = Σ_i c_i * ∫_a^b f_i(t) dt`. Used to move the sum over the zeros of
`L` outside the Perron integral.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- A finite sum of interval-integrable functions is interval-integrable. -/
theorem intervalIntegrable_finset_sum {ι : Type*} (σ : Finset ι) (g : ι → ℝ → ℂ)
    (h : ∀ i ∈ σ, IntervalIntegrable (g i) volume x₁ x₂) :
    IntervalIntegrable (fun t => ∑ i ∈ σ, g i t) volume x₁ x₂ := by
  classical
  induction σ using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous fun _ : ℝ => (0:ℂ)).intervalIntegrable x₁ x₂
  | insert a s ha ih =>
      have h1 := h a (Finset.mem_insert_self a s)
      have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have heq : (fun t => ∑ i ∈ insert a s, g i t) = (fun t => g a t + ∑ i ∈ s, g i t) := by
        funext t
        rw [Finset.sum_insert ha]
      rw [heq]
      exact h1.add h2

/-- A finite sum of constant multiples can be integrated termwise. -/
theorem integral_finset_sum_gen {ι : Type*} (σ : Finset ι) (c : ι → ℂ) (f : ι → ℝ → ℂ)
    (h : ∀ i ∈ σ, IntervalIntegrable (fun t => f i t) volume x₁ x₂) :
    ∫ t in x₁..x₂, ∑ i ∈ σ, c i * f i t = ∑ i ∈ σ, c i * ∫ t in x₁..x₂, f i t := by
  classical
  induction σ using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : IntervalIntegrable (fun t => c a * f a t) volume x₁ x₂ :=
        (h a (Finset.mem_insert_self a s)).const_mul (c a)
      have h2 : IntervalIntegrable (fun t => ∑ i ∈ s, c i * f i t) volume x₁ x₂ :=
        intervalIntegrable_finset_sum s (fun i => fun t => c i * f i t)
          (fun i hi => (h i (Finset.mem_insert_of_mem hi)).const_mul (c i))
      have heq : (fun t => ∑ i ∈ insert a s, c i * f i t)
          = (fun t => c a * f a t + ∑ i ∈ s, c i * f i t) := by
        funext t
        rw [Finset.sum_insert ha]
      rw [heq, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

end BMORProp21

-- ==== BMORBnd.lean ====


/-!
# The rectangle boundary functional

Bundling the four side integrals into a single functional `bnd` makes the linearity of the
boundary integral explicit, so that the residue computation becomes ordinary algebra.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- The horizontal leg of the boundary at height `y`. -/
noncomputable def segH (F : ℂ → ℂ) (y : ℝ) (x₁ x₂ : ℝ) : ℂ :=
  ∫ x in x₁..x₂, F ((x:ℂ) + (y:ℂ)*I)

/-- The vertical leg of the boundary at abscissa `x`. -/
noncomputable def segV (F : ℂ → ℂ) (x : ℝ) (y₁ y₂ : ℝ) : ℂ :=
  ∫ y in y₁..y₂, F ((x:ℂ) + (y:ℂ)*I)

/-- The boundary integral of `F` around the rectangle with corners `(x₁,y₁)`, `(x₂,y₂)`. -/
noncomputable def bnd (F : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : ℂ :=
  segH F y₁ x₁ x₂ - segH F y₂ x₁ x₂ + I*segV F x₂ y₁ y₂ - I*segV F x₁ y₁ y₂

theorem segH_add {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G) :
    segH (fun z => F z + G z) y x₁ x₂ = segH F y x₁ x₂ + segH G y x₁ x₂ := by
  unfold segH
  rw [intervalIntegral.integral_add (f := fun x : ℝ => F ((x:ℂ) + (y:ℂ)*I))
    (g := fun x : ℝ => G ((x:ℂ) + (y:ℂ)*I))
    ((hF.comp (cont_h y)).intervalIntegrable _ _)
    ((hG.comp (cont_h y)).intervalIntegrable _ _)]

theorem segV_add {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G) :
    segV (fun z => F z + G z) x y₁ y₂ = segV F x y₁ y₂ + segV G x y₁ y₂ := by
  unfold segV
  rw [intervalIntegral.integral_add (f := fun y : ℝ => F ((x:ℂ) + (y:ℂ)*I))
    (g := fun y : ℝ => G ((x:ℂ) + (y:ℂ)*I))
    ((hF.comp (cont_v x)).intervalIntegrable _ _)
    ((hG.comp (cont_v x)).intervalIntegrable _ _)]

theorem segH_const_mul (c : ℂ) {F : ℂ → ℂ} (hF : Continuous F) :
    segH (fun z => c * F z) y x₁ x₂ = c * segH F y x₁ x₂ := by
  unfold segH
  rw [intervalIntegral.integral_const_mul]

theorem segV_const_mul (c : ℂ) {F : ℂ → ℂ} (hF : Continuous F) :
    segV (fun z => c * F z) x y₁ y₂ = c * segV F x y₁ y₂ := by
  unfold segV
  rw [intervalIntegral.integral_const_mul]

/-- Entire functions have zero boundary integral. -/
theorem bnd_entire_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    bnd g x₁ x₂ y₁ y₂ = 0 := by
  unfold bnd segH segV
  exact boundary_entire_zero hg

/-- Additivity of the boundary functional. -/
theorem bnd_add {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G) :
    bnd (fun z => F z + G z) x₁ x₂ y₁ y₂
      = bnd F x₁ x₂ y₁ y₂ + bnd G x₁ x₂ y₁ y₂ := by
  unfold bnd
  rw [segH_add hF hG, segH_add hF hG, segV_add hF hG, segV_add hF hG]
  ring

/-- Homogeneity of the boundary functional. -/
theorem bnd_const_mul (c : ℂ) {F : ℂ → ℂ} (hF : Continuous F) :
    bnd (fun z => c * F z) x₁ x₂ y₁ y₂ = c * bnd F x₁ x₂ y₁ y₂ := by
  unfold bnd
  rw [segH_const_mul c hF, segH_const_mul c hF, segV_const_mul c hF, segV_const_mul c hF]
  ring

end BMORProp21

-- ==== BMORBndSum.lean ====


/-!
# The boundary functional applied to `x^s` times a simple pole, and its additivity over sums
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- The boundary functional kills the zero function. -/
theorem bnd_zero : bnd (fun _ => (0:ℂ)) x₁ x₂ y₁ y₂ = 0 := by
  unfold bnd segH segV
  simp

/-- A finite sum of continuous functions is continuous. -/
theorem continuous_finset_sum_c {ι : Type*} (σ : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ σ, Continuous (F i)) :
    Continuous (fun z => ∑ i ∈ σ, F i z) := by
  classical
  induction σ using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
      have h1 : Continuous (F a) := hF a (Finset.mem_insert_self a s)
      have h2 : Continuous (fun z => ∑ i ∈ s, F i z) :=
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      have hsum : (fun z => ∑ i ∈ insert a s, F i z) = (fun z => F a z + ∑ i ∈ s, F i z) := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hsum]
      exact h1.add h2

/-- The boundary functional is additive over a finite sum. -/
theorem bnd_finset_sum {ι : Type*} (σ : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ σ, Continuous (F i)) :
    bnd (fun z => ∑ i ∈ σ, F i z) x₁ x₂ y₁ y₂ = ∑ i ∈ σ, bnd (F i) x₁ x₂ y₁ y₂ := by
  classical
  induction σ using Finset.induction_on with
  | empty =>
      have h0 : (fun z => ∑ i ∈ (∅ : Finset ι), F i z) = (fun _ => (0:ℂ)) := by
        funext z
        simp
      rw [h0]
      simp only [Finset.sum_empty]
      exact bnd_zero
  | insert a s ha ih =>
      have h1 : Continuous (F a) := hF a (Finset.mem_insert_self a s)
      have h2 : Continuous (fun z => ∑ i ∈ s, F i z) :=
        continuous_finset_sum_c s F (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      have hsum : (fun z => ∑ i ∈ insert a s, F i z) = (fun z => F a z + ∑ i ∈ s, F i z) := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hsum, bnd_add h1 h2, ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)),
        Finset.sum_insert ha]

/-- The weighted residue in `bnd` form. -/
theorem bnd_cpow_residue {x : ℂ} (hx : x ≠ 0) {ρ : ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (h1 : x₁ < ρ.re) (h2 : ρ.re < x₂) (h3 : y₁ < ρ.im) (h4 : ρ.im < y₂) :
    bnd (fun s => x ^ s * (s - ρ)⁻¹) x₁ x₂ y₁ y₂ = 2 * (Real.pi : ℂ) * I * x ^ ρ := by
  unfold bnd segH segV
  exact boundary_cpow_residue hx h1 h2 h3 h4

end BMORProp21

-- ==== BMORPoles2.lean ====


/-!
# The principal part of `L'/L` integrated against `x^s`

General form: for a continuous parametrisation `φ` staying away from all the poles, the finite sum
over the poles can be moved outside the integral.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- Continuity of `t ↦ x^s` along a continuous parametrisation. -/
theorem continuous_cpow_comp {x : ℂ} (hx : x ≠ 0) {φ : ℝ → ℂ} (hφ : Continuous φ) :
    Continuous fun t => x ^ (φ t) := by
  have h : (fun t => x ^ (φ t)) = (fun t => Complex.exp (Complex.log x * φ t)) := by
    funext t
    exact cpow_def_of_ne_zero hx _
  rw [h]
  exact Complex.continuous_exp.comp (continuous_const.mul hφ)

/-- Integrability of a single pole term along a parametrised segment. -/
theorem integrable_along {x : ℂ} (hx : x ≠ 0) {φ : ℝ → ℂ} (hφ : Continuous φ)
    {ρ : ℂ} (hne : ∀ t : ℝ, φ t ≠ ρ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ => x ^ (φ t) * (φ t - ρ)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul (continuous_cpow_comp hx hφ).continuousOn
  apply ContinuousOn.inv₀ (hφ.sub continuous_const).continuousOn
  intro t _
  exact sub_ne_zero.mpr (hne t)

/-- Sum interchange along a parametrised segment. -/
theorem exchange_gen {x : ℂ} (hx : x ≠ 0) {σ : Finset ℂ} {m : ℂ → ℕ} {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hne : ∀ ρ ∈ σ, ∀ t : ℝ, φ t ≠ ρ) {a b : ℝ} :
    ∫ t in a..b, ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ (φ t) * (φ t - ρ)⁻¹)
      = ∑ ρ ∈ σ, (m ρ : ℂ) * ∫ t in a..b, (x ^ (φ t) * (φ t - ρ)⁻¹) :=
  integral_finset_sum_gen (x₁ := a) (x₂ := b) σ (fun ρ => (m ρ : ℂ))
    (fun ρ t => x ^ (φ t) * (φ t - ρ)⁻¹)
    (fun ρ hρ => integrable_along hx hφ (fun t => hne ρ hρ t))

end BMORProp21

-- ==== BMORPoleSum.lean ====


/-!
# The principal part of `L'/L` integrated against `x^s`

`bnd (fun s => Σ_ρ m_ρ * (x^s * (s-ρ)⁻¹)) = 2πi * Σ_ρ m_ρ * x^ρ`
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

set_option maxHeartbeats 800000 in
/-- Sum interchange on the four sides of the rectangle. -/
theorem bnd_sum_poles {x : ℂ} (hx : x ≠ 0) {σ : Finset ℂ} {m : ℂ → ℕ}
    {x₁ x₂ y₁ y₂ : ℝ}
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    bnd (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹)) x₁ x₂ y₁ y₂
      = (2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * x ^ ρ := by
  have hne1 : ∀ ρ ∈ σ, ∀ t : ℝ, ((t:ℂ) + (y₁:ℂ)*I) ≠ ρ := by
    intro ρ hρ t h
    have him : y₁ = ρ.im := by simpa using congrArg Complex.im h
    linarith [(hin ρ hρ).2.2.1]
  have hne2 : ∀ ρ ∈ σ, ∀ t : ℝ, ((t:ℂ) + (y₂:ℂ)*I) ≠ ρ := by
    intro ρ hρ t h
    have him : y₂ = ρ.im := by simpa using congrArg Complex.im h
    linarith [(hin ρ hρ).2.2.2]
  have hne3 : ∀ ρ ∈ σ, ∀ t : ℝ, ((x₂:ℂ) + (t:ℂ)*I) ≠ ρ := by
    intro ρ hρ t h
    have hre : x₂ = ρ.re := by simpa using congrArg Complex.re h
    linarith [(hin ρ hρ).2.1]
  have hne4 : ∀ ρ ∈ σ, ∀ t : ℝ, ((x₁:ℂ) + (t:ℂ)*I) ≠ ρ := by
    intro ρ hρ t h
    have hre : x₁ = ρ.re := by simpa using congrArg Complex.re h
    linarith [(hin ρ hρ).1]
  have e1 : segH (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹)) y₁ x₁ x₂
      = ∑ ρ ∈ σ, (m ρ : ℂ) * segH (fun s => x ^ s * (s - ρ)⁻¹) y₁ x₁ x₂ := by
    unfold segH
    rw [exchange_gen hx (cont_h y₁) hne1]
  have e2 : segH (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹)) y₂ x₁ x₂
      = ∑ ρ ∈ σ, (m ρ : ℂ) * segH (fun s => x ^ s * (s - ρ)⁻¹) y₂ x₁ x₂ := by
    unfold segH
    rw [exchange_gen hx (cont_h y₂) hne2]
  have e3 : segV (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹)) x₂ y₁ y₂
      = ∑ ρ ∈ σ, (m ρ : ℂ) * segV (fun s => x ^ s * (s - ρ)⁻¹) x₂ y₁ y₂ := by
    unfold segV
    rw [exchange_gen hx (cont_v x₂) hne3]
  have e4 : segV (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹)) x₁ y₁ y₂
      = ∑ ρ ∈ σ, (m ρ : ℂ) * segV (fun s => x ^ s * (s - ρ)⁻¹) x₁ y₁ y₂ := by
    unfold segV
    rw [exchange_gen hx (cont_v x₁) hne4]
  have hbnd : bnd (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹)) x₁ x₂ y₁ y₂
      = ∑ ρ ∈ σ, (m ρ : ℂ) * bnd (fun s => x ^ s * (s - ρ)⁻¹) x₁ x₂ y₁ y₂ := by
    unfold bnd
    rw [e1, e2, e3, e4]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  rw [hbnd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [bnd_cpow_residue hx (hin ρ hρ).1 (hin ρ hρ).2.1 (hin ρ hρ).2.2.1 (hin ρ hρ).2.2.2]
  ring

end BMORProp21

-- ==== BMORBndLocal.lean ====


/-!
# The boundary functional on functions holomorphic only near the rectangle

`bnd F = 0` whenever `F` is complex differentiable on the closed rectangle. This is the local
version of `bnd_entire_zero`, needed for `g'/g` when `g` has zeros outside the rectangle.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- `bnd` vanishes on functions differentiable on the closed rectangle. -/
theorem bnd_diffOn_zero {F : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hF : DifferentiableOn ℂ F (Set.Icc x₁ x₂ ×ℂ Set.Icc y₁ y₂)) :
    bnd F x₁ x₂ y₁ y₂ = 0 := by
  have h' : DifferentiableOn ℂ F
      (Set.uIcc ((x₁:ℂ) + (y₁:ℂ)*I).re ((x₂:ℂ) + (y₂:ℂ)*I).re
        ×ℂ Set.uIcc ((x₁:ℂ) + (y₁:ℂ)*I).im ((x₂:ℂ) + (y₂:ℂ)*I).im) := by
    simpa [Set.uIcc_of_le hx, Set.uIcc_of_le hy] using hF
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((x₁:ℂ) + (y₁:ℂ)*I) ((x₂:ℂ) + (y₂:ℂ)*I) h'
  unfold bnd segH segV
  simpa using h

end BMORProp21

-- ==== BMORBndAddOn.lean ====


/-!
# Additivity of `bnd` for functions only continuous on the rectangle
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- The closed rectangle as a set of complex numbers. -/
def rectSet (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := Set.uIcc x₁ x₂ ×ℂ Set.uIcc y₁ y₂

/-- Integrability of a horizontal leg for functions continuous on the rectangle. -/
theorem intH_of_continuousOn {F : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hF : ContinuousOn F (rectSet x₁ x₂ y₁ y₂)) (y : ℝ) (hy : y ∈ Set.uIcc y₁ y₂) :
    IntervalIntegrable (fun t : ℝ => F ((t:ℂ) + (y:ℂ)*I)) volume x₁ x₂ := by
  apply ContinuousOn.intervalIntegrable
  exact hF.comp (cont_h y).continuousOn (fun t ht => by
    have hr : ((t:ℂ) + (y:ℂ)*I).re ∈ Set.uIcc x₁ x₂ := by simpa using ht
    have him : ((t:ℂ) + (y:ℂ)*I).im ∈ Set.uIcc y₁ y₂ := by simpa using hy
    exact ⟨hr, him⟩)

/-- Integrability of a vertical leg for functions continuous on the rectangle. -/
theorem intV_of_continuousOn {F : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hF : ContinuousOn F (rectSet x₁ x₂ y₁ y₂)) (x : ℝ) (hx : x ∈ Set.uIcc x₁ x₂) :
    IntervalIntegrable (fun t : ℝ => F ((x:ℂ) + (t:ℂ)*I)) volume y₁ y₂ := by
  apply ContinuousOn.intervalIntegrable
  exact hF.comp (cont_v x).continuousOn (fun t ht => by
    have hr : ((x:ℂ) + (t:ℂ)*I).re ∈ Set.uIcc x₁ x₂ := by simpa using hx
    have him : ((x:ℂ) + (t:ℂ)*I).im ∈ Set.uIcc y₁ y₂ := by simpa using ht
    exact ⟨hr, him⟩)

/-- Additivity of `bnd` for functions continuous on the rectangle. -/
theorem bnd_addOn {F G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hF : ContinuousOn F (rectSet x₁ x₂ y₁ y₂))
    (hG : ContinuousOn G (rectSet x₁ x₂ y₁ y₂)) :
    bnd (fun z => F z + G z) x₁ x₂ y₁ y₂
      = bnd F x₁ x₂ y₁ y₂ + bnd G x₁ x₂ y₁ y₂ := by
  unfold bnd segH segV
  rw [intervalIntegral.integral_add
    (intH_of_continuousOn hF y₁ (Set.left_mem_uIcc))
    (intH_of_continuousOn hG y₁ (Set.left_mem_uIcc)),
    intervalIntegral.integral_add
    (intH_of_continuousOn hF y₂ (Set.right_mem_uIcc))
    (intH_of_continuousOn hG y₂ (Set.right_mem_uIcc)),
    intervalIntegral.integral_add
    (intV_of_continuousOn hF x₂ (Set.right_mem_uIcc))
    (intV_of_continuousOn hG x₂ (Set.right_mem_uIcc)),
    intervalIntegral.integral_add
    (intV_of_continuousOn hF x₁ (Set.left_mem_uIcc))
    (intV_of_continuousOn hG x₁ (Set.left_mem_uIcc))]
  ring

end BMORProp21

-- ==== BMORBndCongr.lean ====


/-!
# Congruence of the boundary functional
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- `bnd` respects pointwise equality on the four legs of the boundary. -/
theorem bnd_congr4 {F G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (h1 : ∀ t ∈ Set.uIcc x₁ x₂, F ((t:ℂ) + (y₁:ℂ)*I) = G ((t:ℂ) + (y₁:ℂ)*I))
    (h2 : ∀ t ∈ Set.uIcc x₁ x₂, F ((t:ℂ) + (y₂:ℂ)*I) = G ((t:ℂ) + (y₂:ℂ)*I))
    (h3 : ∀ t ∈ Set.uIcc y₁ y₂, F ((x₂:ℂ) + (t:ℂ)*I) = G ((x₂:ℂ) + (t:ℂ)*I))
    (h4 : ∀ t ∈ Set.uIcc y₁ y₂, F ((x₁:ℂ) + (t:ℂ)*I) = G ((x₁:ℂ) + (t:ℂ)*I)) :
    bnd F x₁ x₂ y₁ y₂ = bnd G x₁ x₂ y₁ y₂ := by
  unfold bnd segH segV
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2,
    intervalIntegral.integral_congr h3, intervalIntegral.integral_congr h4]

/-- `bnd` respects pointwise equality on the rectangle. -/
theorem bnd_congr {F G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (h : ∀ z ∈ rectSet x₁ x₂ y₁ y₂, F z = G z) :
    bnd F x₁ x₂ y₁ y₂ = bnd G x₁ x₂ y₁ y₂ := by
  refine bnd_congr4 (fun t ht => h _ ⟨by simpa using ht, by simpa using Set.left_mem_uIcc⟩)
    (fun t ht => h _ ⟨by simpa using ht, by simpa using Set.right_mem_uIcc⟩)
    (fun t ht => h _ ⟨by simpa using Set.right_mem_uIcc, by simpa using ht⟩)
    (fun t ht => h _ ⟨by simpa using Set.left_mem_uIcc, by simpa using ht⟩)

end BMORProp21

-- ==== BMORCrossZero.lean ====


/-!
# The zero-factor part of the cross-zero identity

`bnd (fun s => x^s · (P'/P)(s)) = 2πi · Σ_ρ m_ρ · x^ρ`
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- On the boundary the logarithmic derivative of the zero factor is the sum of simple poles. -/
theorem logDeriv_zeroFactorC_on {f : ℂ → ℂ} (df : Differentiable ℂ f) (R : Set ℂ)
    (hR : IsCompact R) {z : ℂ} (hz : ∀ a ∈ BMORRectFactor.rootsC f R hR, z ≠ a) :
    logDeriv (BMORRectFactor.zeroFactorC f R) z
      = ∑ a ∈ BMORRectFactor.rootsC f R hR,
          (BMORRectFactor.multC f R a : ℂ) / (z - a) := by
  have hfun : BMORRectFactor.zeroFactorC f R
      = (fun w : ℂ => ∏ a ∈ BMORRectFactor.rootsC f R hR,
          (w - a) ^ (BMORRectFactor.multC f R a)) := by
    funext w
    exact BMORRectFactor.factor_prod_compact df R hR w
  have hlhs : logDeriv (fun w : ℂ => ∏ a ∈ BMORRectFactor.rootsC f R hR,
      (w - a) ^ (BMORRectFactor.multC f R a)) z
      = logDeriv (BMORRectFactor.zeroFactorC f R) z := by
    congr 1
    exact hfun.symm
  rw [← hlhs]
  exact logDeriv_prod_pow hz


/-- The zero-factor part of the cross-zero identity. -/
theorem bnd_logDeriv_zeroFactorC {f : ℂ → ℂ} (df : Differentiable ℂ f) (R : Set ℂ)
    (hR : IsCompact R) {x : ℂ} (hx : x ≠ 0) {x₁ x₂ y₁ y₂ : ℝ}
    (hin : ∀ ρ ∈ BMORRectFactor.rootsC f R hR,
      x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    bnd (fun s => x ^ s * logDeriv (BMORRectFactor.zeroFactorC f R) s) x₁ x₂ y₁ y₂
      = (2 * (Real.pi : ℂ) * I) *
          ∑ ρ ∈ BMORRectFactor.rootsC f R hR,
            (BMORRectFactor.multC f R ρ : ℂ) * x ^ ρ := by
  set σ := BMORRectFactor.rootsC f R hR with hσ
  have key : ∀ z : ℂ, (∀ a ∈ σ, z ≠ a) →
      x ^ z * logDeriv (BMORRectFactor.zeroFactorC f R) z
        = ∑ a ∈ σ, (BMORRectFactor.multC f R a : ℂ) * (x ^ z * (z - a)⁻¹) := by
    intro z hz
    rw [logDeriv_zeroFactorC_on df R hR hz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hne1 : ∀ a ∈ σ, ∀ t : ℝ, ((t:ℂ) + (y₁:ℂ)*I) ≠ a := by
    intro a ha t h
    have him : y₁ = a.im := by simpa using congrArg Complex.im h
    linarith [(hin a ha).2.2.1]
  have hne2 : ∀ a ∈ σ, ∀ t : ℝ, ((t:ℂ) + (y₂:ℂ)*I) ≠ a := by
    intro a ha t h
    have him : y₂ = a.im := by simpa using congrArg Complex.im h
    linarith [(hin a ha).2.2.2]
  have hne3 : ∀ a ∈ σ, ∀ t : ℝ, ((x₂:ℂ) + (t:ℂ)*I) ≠ a := by
    intro a ha t h
    have hre : x₂ = a.re := by simpa using congrArg Complex.re h
    linarith [(hin a ha).2.1]
  have hne4 : ∀ a ∈ σ, ∀ t : ℝ, ((x₁:ℂ) + (t:ℂ)*I) ≠ a := by
    intro a ha t h
    have hre : x₁ = a.re := by simpa using congrArg Complex.re h
    linarith [(hin a ha).1]
  have hcongr : bnd (fun s => x ^ s * logDeriv (BMORRectFactor.zeroFactorC f R) s) x₁ x₂ y₁ y₂
      = bnd (fun s => ∑ a ∈ σ, (BMORRectFactor.multC f R a : ℂ) * (x ^ s * (s - a)⁻¹))
          x₁ x₂ y₁ y₂ :=
    bnd_congr4 (G := fun s => ∑ a ∈ σ, (BMORRectFactor.multC f R a : ℂ) * (x ^ s * (s - a)⁻¹))
      (fun t _ => key _ (fun a ha => hne1 a ha t))
      (fun t _ => key _ (fun a ha => hne2 a ha t))
      (fun t _ => key _ (fun a ha => hne3 a ha t))
      (fun t _ => key _ (fun a ha => hne4 a ha t))
  rw [hcongr]
  exact bnd_sum_poles hx hin
end BMORProp21

-- ==== BMORCoFactor.lean ====


/-!
# The cofactor part of the cross-zero identity

`bnd (fun s => x^s · (g'/g)(s)) = 0` whenever `g` is entire and does not vanish on the rectangle.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- `g'/g` is holomorphic where `g` does not vanish. -/
theorem differentiableOn_logDeriv {g : ℂ → ℂ} (hg : Differentiable ℂ g) {R : Set ℂ}
    (hne : ∀ z ∈ R, g z ≠ 0) : DifferentiableOn ℂ (logDeriv g) R := by
  intro z hz
  have h : DifferentiableAt ℂ (fun w => deriv g w / g w) z :=
    (hg.deriv.differentiableAt).div hg.differentiableAt (hne z hz)
  exact h.differentiableWithinAt

/-- The cofactor part of the cross-zero identity. -/
theorem bnd_cpow_logDeriv_cofactor {g : ℂ → ℂ} (hg : Differentiable ℂ g) {x : ℂ} (hx : x ≠ 0)
    {x₁ x₂ y₁ y₂ : ℝ} (hle_x : x₁ ≤ x₂) (hle_y : y₁ ≤ y₂)
    (hne : ∀ z ∈ rectSet x₁ x₂ y₁ y₂, g z ≠ 0) :
    bnd (fun s => x ^ s * logDeriv g s) x₁ x₂ y₁ y₂ = 0 := by
  apply bnd_diffOn_zero hle_x hle_y
  have hR : (Set.Icc x₁ x₂ ×ℂ Set.Icc y₁ y₂) = rectSet x₁ x₂ y₁ y₂ := by
    simp [rectSet, Set.uIcc_of_le hle_x, Set.uIcc_of_le hle_y]
  rw [hR]
  exact (differentiable_cpow_const hx).differentiableOn.mul (differentiableOn_logDeriv hg hne)

end BMORProp21

-- ==== BMORBndAdd4.lean ====


/-!
# Additivity of `bnd` with continuity only on the four legs
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- `bnd` is additive as soon as both functions are continuous on each leg. -/
theorem bnd_add4 {F G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hF1 : ContinuousOn (fun t : ℝ => F ((t:ℂ) + (y₁:ℂ)*I)) (Set.uIcc x₁ x₂))
    (hF2 : ContinuousOn (fun t : ℝ => F ((t:ℂ) + (y₂:ℂ)*I)) (Set.uIcc x₁ x₂))
    (hF3 : ContinuousOn (fun t : ℝ => F ((x₂:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂))
    (hF4 : ContinuousOn (fun t : ℝ => F ((x₁:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂))
    (hG1 : ContinuousOn (fun t : ℝ => G ((t:ℂ) + (y₁:ℂ)*I)) (Set.uIcc x₁ x₂))
    (hG2 : ContinuousOn (fun t : ℝ => G ((t:ℂ) + (y₂:ℂ)*I)) (Set.uIcc x₁ x₂))
    (hG3 : ContinuousOn (fun t : ℝ => G ((x₂:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂))
    (hG4 : ContinuousOn (fun t : ℝ => G ((x₁:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂)) :
    bnd (fun z => F z + G z) x₁ x₂ y₁ y₂
      = bnd F x₁ x₂ y₁ y₂ + bnd G x₁ x₂ y₁ y₂ := by
  unfold bnd segH segV
  rw [intervalIntegral.integral_add hF1.intervalIntegrable hG1.intervalIntegrable,
    intervalIntegral.integral_add hF2.intervalIntegrable hG2.intervalIntegrable,
    intervalIntegral.integral_add hF3.intervalIntegrable hG3.intervalIntegrable,
    intervalIntegral.integral_add hF4.intervalIntegrable hG4.intervalIntegrable]
  ring

end BMORProp21

-- ==== BMORContinuity.lean ====


/-!
# Continuity on a leg of the two pieces of `x^s · L'/L`
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- A finite sum of continuous functions of a real variable is continuous. -/
theorem continuous_finset_sum_r {ι : Type*} (σ : Finset ι) (g : ι → ℝ → ℂ)
    (h : ∀ i ∈ σ, Continuous (g i)) :
    Continuous (fun t => ∑ i ∈ σ, g i t) := by
  classical
  induction σ using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
      have h1 := h a (Finset.mem_insert_self a s)
      have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have heq : (fun t => ∑ i ∈ insert a s, g i t)
          = (fun t => g a t + ∑ i ∈ s, g i t) := by
        funext t
        rw [Finset.sum_insert ha]
      rw [heq]
      exact h1.add h2

/-- The principal part is continuous on a leg that avoids the poles. -/
theorem continuousOn_cpow_logDerivP {f : ℂ → ℂ} (df : Differentiable ℂ f) (R : Set ℂ)
    (hR : IsCompact R) {x : ℂ} (hx : x ≠ 0) {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hne : ∀ ρ ∈ BMORRectFactor.rootsC f R hR, ∀ t : ℝ, φ t ≠ ρ) {a b : ℝ} :
    ContinuousOn (fun t => x ^ (φ t) * logDeriv (BMORRectFactor.zeroFactorC f R) (φ t))
      (Set.uIcc a b) := by
  have hcongr : ∀ t : ℝ, x ^ (φ t) * logDeriv (BMORRectFactor.zeroFactorC f R) (φ t)
      = ∑ ρ ∈ BMORRectFactor.rootsC f R hR,
          (BMORRectFactor.multC f R ρ : ℂ) * (x ^ (φ t) * (φ t - ρ)⁻¹) := by
    intro t
    rw [logDeriv_zeroFactorC_on df R hR (fun ρ hρ => hne ρ hρ t), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  have hcont : Continuous (fun t => ∑ ρ ∈ BMORRectFactor.rootsC f R hR,
      (BMORRectFactor.multC f R ρ : ℂ) * (x ^ (φ t) * (φ t - ρ)⁻¹)) := by
    apply continuous_finset_sum_r
    intro ρ hρ
    exact continuous_const.mul ((continuous_cpow_comp hx hφ).mul
      (Continuous.inv₀ (hφ.sub continuous_const) (fun t => sub_ne_zero.mpr (hne ρ hρ t))))
  exact hcont.continuousOn.congr (fun t _ => hcongr t)

/-- The cofactor part is continuous on a leg inside the zero-free region. -/
theorem continuousOn_cpow_logDeriv_cofactor {g : ℂ → ℂ} (hg : Differentiable ℂ g) {x : ℂ}
    (hx : x ≠ 0) {φ : ℝ → ℂ} (hφ : Continuous φ) {R : Set ℂ}
    (hR : ∀ t ∈ Set.uIcc a b, φ t ∈ R) (hne : ∀ z ∈ R, g z ≠ 0) :
    ContinuousOn (fun t => x ^ (φ t) * logDeriv g (φ t)) (Set.uIcc a b) := by
  apply ContinuousOn.mul (continuous_cpow_comp hx hφ).continuousOn
  exact (differentiableOn_logDeriv hg hne).continuousOn.comp hφ.continuousOn hR

end BMORProp21

-- ==== BMORBndSet.lean ====


/-!
# The boundary of the rectangle as a single set

Bundling the four legs into one set keeps the hypothesis count of the boundary lemmas at two,
which matters because Lean's statement elaboration degrades sharply past roughly a dozen
hypotheses.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- The boundary of the rectangle, as a single set. -/
def bndSet (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  {z | (z.im = y₁ ∧ z.re ∈ Set.uIcc x₁ x₂) ∨ (z.im = y₂ ∧ z.re ∈ Set.uIcc x₁ x₂)
    ∨ (z.re = x₂ ∧ z.im ∈ Set.uIcc y₁ y₂) ∨ (z.re = x₁ ∧ z.im ∈ Set.uIcc y₁ y₂)}

theorem mem_bndSet_H1 {x₁ x₂ y₁ y₂ t : ℝ} (ht : t ∈ Set.uIcc x₁ x₂) :
    ((t:ℂ) + (y₁:ℂ)*I) ∈ bndSet x₁ x₂ y₁ y₂ := by
  have him : ((t:ℂ) + (y₁:ℂ)*I).im = y₁ := by simp
  have hre : ((t:ℂ) + (y₁:ℂ)*I).re ∈ Set.uIcc x₁ x₂ := by simpa using ht
  simp only [bndSet, Set.mem_setOf_eq]
  tauto

theorem mem_bndSet_H2 {x₁ x₂ y₁ y₂ t : ℝ} (ht : t ∈ Set.uIcc x₁ x₂) :
    ((t:ℂ) + (y₂:ℂ)*I) ∈ bndSet x₁ x₂ y₁ y₂ := by
  have him : ((t:ℂ) + (y₂:ℂ)*I).im = y₂ := by simp
  have hre : ((t:ℂ) + (y₂:ℂ)*I).re ∈ Set.uIcc x₁ x₂ := by simpa using ht
  simp only [bndSet, Set.mem_setOf_eq]
  tauto

theorem mem_bndSet_V2 {x₁ x₂ y₁ y₂ t : ℝ} (ht : t ∈ Set.uIcc y₁ y₂) :
    ((x₂:ℂ) + (t:ℂ)*I) ∈ bndSet x₁ x₂ y₁ y₂ := by
  have hre : ((x₂:ℂ) + (t:ℂ)*I).re = x₂ := by simp
  have him : ((x₂:ℂ) + (t:ℂ)*I).im ∈ Set.uIcc y₁ y₂ := by simpa using ht
  simp only [bndSet, Set.mem_setOf_eq]
  tauto

theorem mem_bndSet_V1 {x₁ x₂ y₁ y₂ t : ℝ} (ht : t ∈ Set.uIcc y₁ y₂) :
    ((x₁:ℂ) + (t:ℂ)*I) ∈ bndSet x₁ x₂ y₁ y₂ := by
  have hre : ((x₁:ℂ) + (t:ℂ)*I).re = x₁ := by simp
  have him : ((x₁:ℂ) + (t:ℂ)*I).im ∈ Set.uIcc y₁ y₂ := by simpa using ht
  simp only [bndSet, Set.mem_setOf_eq]
  tauto

/-- Congruence of `bnd` from agreement on the boundary set. -/
theorem bnd_congr_bnd {F G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (h : ∀ z ∈ bndSet x₁ x₂ y₁ y₂, F z = G z) :
    bnd F x₁ x₂ y₁ y₂ = bnd G x₁ x₂ y₁ y₂ :=
  bnd_congr4 (fun t ht => h _ (mem_bndSet_H1 ht)) (fun t ht => h _ (mem_bndSet_H2 ht))
    (fun t ht => h _ (mem_bndSet_V2 ht)) (fun t ht => h _ (mem_bndSet_V1 ht))

/-- Additivity of `bnd` from continuity on the boundary set. -/
theorem bnd_add_bnd {F G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hF : ContinuousOn F (bndSet x₁ x₂ y₁ y₂)) (hG : ContinuousOn G (bndSet x₁ x₂ y₁ y₂)) :
    bnd (fun z => F z + G z) x₁ x₂ y₁ y₂
      = bnd F x₁ x₂ y₁ y₂ + bnd G x₁ x₂ y₁ y₂ :=
  bnd_add4
    (hF.comp (cont_h y₁).continuousOn (fun t ht => mem_bndSet_H1 ht))
    (hF.comp (cont_h y₂).continuousOn (fun t ht => mem_bndSet_H2 ht))
    (hF.comp (cont_v x₂).continuousOn (fun t ht => mem_bndSet_V2 ht))
    (hF.comp (cont_v x₁).continuousOn (fun t ht => mem_bndSet_V1 ht))
    (hG.comp (cont_h y₁).continuousOn (fun t ht => mem_bndSet_H1 ht))
    (hG.comp (cont_h y₂).continuousOn (fun t ht => mem_bndSet_H2 ht))
    (hG.comp (cont_v x₂).continuousOn (fun t ht => mem_bndSet_V2 ht))
    (hG.comp (cont_v x₁).continuousOn (fun t ht => mem_bndSet_V1 ht))

end BMORProp21

-- ==== BMORCrossZeroClean.lean ====


/-!
# The cross-zero identity, stated without proof-carrying data

`rootsC`/`multC` carry a proof argument (`IsCompact R`) inside a `Finset`, which makes any
statement mentioning them explode in `whnf`. These versions take the finset of zeros `σ` and the
multiplicity function `m` explicitly, together with the factorisation identity.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- On the boundary the logarithmic derivative of the zero factor is a sum of simple poles. -/
theorem logDeriv_zeroFactorC_eq {f : ℂ → ℂ} (R : Set ℂ) {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    {z : ℂ} (hz : ∀ a ∈ σ, z ≠ a) :
    logDeriv (BMORRectFactor.zeroFactorC f R) z = ∑ a ∈ σ, (m a : ℂ) / (z - a) := by
  have hfun : BMORRectFactor.zeroFactorC f R = (fun w : ℂ => ∏ a ∈ σ, (w-a)^(m a)) :=
    funext hP
  have hlhs : logDeriv (fun w : ℂ => ∏ a ∈ σ, (w-a)^(m a)) z
      = logDeriv (BMORRectFactor.zeroFactorC f R) z := by
    congr 1
    exact hfun.symm
  rw [← hlhs]
  exact logDeriv_prod_pow hz

/-- The zero-factor part of the cross-zero identity. -/
theorem bnd_cpow_logDeriv_zeroFactorC_eq {f : ℂ → ℂ} {x : ℂ} (hx : x ≠ 0)
    {R : Set ℂ} {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    {x₁ x₂ y₁ y₂ : ℝ}
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    bnd (fun s => x ^ s * logDeriv (BMORRectFactor.zeroFactorC f R) s) x₁ x₂ y₁ y₂
      = (2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * x ^ ρ := by
  have key : ∀ z : ℂ, (∀ a ∈ σ, z ≠ a) →
      x ^ z * logDeriv (BMORRectFactor.zeroFactorC f R) z
        = ∑ a ∈ σ, (m a : ℂ) * (x ^ z * (z - a)⁻¹) := by
    intro z hz
    rw [logDeriv_zeroFactorC_eq R hP hz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hne1 : ∀ a ∈ σ, ∀ t : ℝ, ((t:ℂ) + (y₁:ℂ)*I) ≠ a := by
    intro a ha t h
    have him : y₁ = a.im := by simpa using congrArg Complex.im h
    linarith [(hin a ha).2.2.1]
  have hne2 : ∀ a ∈ σ, ∀ t : ℝ, ((t:ℂ) + (y₂:ℂ)*I) ≠ a := by
    intro a ha t h
    have him : y₂ = a.im := by simpa using congrArg Complex.im h
    linarith [(hin a ha).2.2.2]
  have hne3 : ∀ a ∈ σ, ∀ t : ℝ, ((x₂:ℂ) + (t:ℂ)*I) ≠ a := by
    intro a ha t h
    have hre : x₂ = a.re := by simpa using congrArg Complex.re h
    linarith [(hin a ha).2.1]
  have hne4 : ∀ a ∈ σ, ∀ t : ℝ, ((x₁:ℂ) + (t:ℂ)*I) ≠ a := by
    intro a ha t h
    have hre : x₁ = a.re := by simpa using congrArg Complex.re h
    linarith [(hin a ha).1]
  have hcongr : bnd (fun s => x ^ s * logDeriv (BMORRectFactor.zeroFactorC f R) s)
        x₁ x₂ y₁ y₂
      = bnd (fun s => ∑ a ∈ σ, (m a : ℂ) * (x ^ s * (s - a)⁻¹)) x₁ x₂ y₁ y₂ :=
    bnd_congr4 (G := fun s => ∑ a ∈ σ, (m a : ℂ) * (x ^ s * (s - a)⁻¹))
      (fun t _ => key _ (fun a ha => hne1 a ha t))
      (fun t _ => key _ (fun a ha => hne2 a ha t))
      (fun t _ => key _ (fun a ha => hne3 a ha t))
      (fun t _ => key _ (fun a ha => hne4 a ha t))
  rw [hcongr]
  exact bnd_sum_poles hx hin


/-- The principal part is continuous on a leg that avoids the poles (clean form). -/
theorem continuousOn_cpow_logDerivP_eq {f : ℂ → ℂ} {R : Set ℂ} {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    {x : ℂ} (hx : x ≠ 0) {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hne : ∀ a ∈ σ, ∀ t : ℝ, φ t ≠ a) {a b : ℝ} :
    ContinuousOn (fun t => x ^ (φ t) * logDeriv (BMORRectFactor.zeroFactorC f R) (φ t))
      (Set.uIcc a b) := by
  have hcongr : ∀ t : ℝ, x ^ (φ t) * logDeriv (BMORRectFactor.zeroFactorC f R) (φ t)
      = ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ (φ t) * (φ t - ρ)⁻¹) := by
    intro t
    rw [logDeriv_zeroFactorC_eq R hP (fun ρ hρ => hne ρ hρ t), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  have hcont : Continuous (fun t => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ (φ t) * (φ t - ρ)⁻¹)) := by
    apply continuous_finset_sum_r
    intro ρ hρ
    exact continuous_const.mul ((continuous_cpow_comp hx hφ).mul
      (Continuous.inv₀ (hφ.sub continuous_const) (fun t => sub_ne_zero.mpr (hne ρ hρ t))))
  exact hcont.continuousOn.congr (fun t _ => hcongr t)
end BMORProp21

-- ==== BMORCrossZeroK.lean ====


/-!
# Cross-zero lemmas with the weight `x^s` abstracted into a function parameter

`x ^ s` for `x s : ℂ` triggers a `HPow ℂ ℂ ℂ` instance search that loops in `whnf` in large
contexts. Keeping the weight as an opaque `K : ℂ → ℂ` with `hK : ∀ s, K s = Complex.cpow x s`
avoids the problem entirely.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- `bnd_sum_poles` with an abstract weight. -/
theorem bnd_sum_poles_K {x : ℂ} (hx : x ≠ 0) {σ : Finset ℂ} {m : ℂ → ℕ} {K : ℂ → ℂ}
    (hK : ∀ s : ℂ, K s = x ^ s)
    {x₁ x₂ y₁ y₂ : ℝ}
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    bnd (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (K s * (s - ρ)⁻¹)) x₁ x₂ y₁ y₂
      = (2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * K ρ := by
  have hcongr : bnd (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (K s * (s - ρ)⁻¹)) x₁ x₂ y₁ y₂
      = bnd (fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹)) x₁ x₂ y₁ y₂ := by
    refine bnd_congr4 (G := fun s => ∑ ρ ∈ σ, (m ρ : ℂ) * (x ^ s * (s - ρ)⁻¹))
      ?_ ?_ ?_ ?_
    all_goals
      intro t _
      simp only [hK]
  rw [hcongr, bnd_sum_poles hx hin]
  congr 1
  exact Finset.sum_congr rfl (fun ρ _ => by simp only [hK])

/-- `bnd_cpow_logDeriv_zeroFactorC_eq` with an abstract weight. -/
theorem bnd_cpow_logDeriv_zeroFactorC_eq_K {f : ℂ → ℂ} {x : ℂ} (hx : x ≠ 0)
    {R : Set ℂ} {σ : Finset ℂ} {m : ℂ → ℕ} {K : ℂ → ℂ}
    (hK : ∀ s : ℂ, K s = x ^ s)
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    {x₁ x₂ y₁ y₂ : ℝ}
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    bnd (fun s => K s * logDeriv (BMORRectFactor.zeroFactorC f R) s) x₁ x₂ y₁ y₂
      = (2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * K ρ := by
  have hcongr : bnd (fun s => K s * logDeriv (BMORRectFactor.zeroFactorC f R) s)
        x₁ x₂ y₁ y₂
      = bnd (fun s => x ^ s * logDeriv (BMORRectFactor.zeroFactorC f R) s) x₁ x₂ y₁ y₂ := by
    refine bnd_congr4
      (G := fun s => x ^ s * logDeriv (BMORRectFactor.zeroFactorC f R) s) ?_ ?_ ?_ ?_
    all_goals
      intro t _
      simp only [hK]
  rw [hcongr, bnd_cpow_logDeriv_zeroFactorC_eq hx hP hin]
  congr 1
  exact Finset.sum_congr rfl (fun ρ _ => by simp only [hK])


/-- `bnd_cpow_logDeriv_cofactor` with an abstract weight. -/
theorem bnd_cpow_logDeriv_cofactor_K {g : ℂ → ℂ} (hg : Differentiable ℂ g) {x : ℂ} (hx : x ≠ 0)
    {K : ℂ → ℂ} (hK : ∀ s : ℂ, K s = x ^ s)
    {x₁ x₂ y₁ y₂ : ℝ} (hle_x : x₁ ≤ x₂) (hle_y : y₁ ≤ y₂)
    (hne : ∀ z ∈ rectSet x₁ x₂ y₁ y₂, g z ≠ 0) :
    bnd (fun s => K s * logDeriv g s) x₁ x₂ y₁ y₂ = 0 := by
  have hcongr : bnd (fun s => K s * logDeriv g s) x₁ x₂ y₁ y₂
      = bnd (fun s => x ^ s * logDeriv g s) x₁ x₂ y₁ y₂ := by
    refine bnd_congr4 (G := fun s => x ^ s * logDeriv g s) ?_ ?_ ?_ ?_
    all_goals
      intro t _
      simp only [hK]
  rw [hcongr]
  exact bnd_cpow_logDeriv_cofactor hg hx hle_x hle_y hne
end BMORProp21

-- ==== BMORCrossZeroBnd.lean ====


/-!
# The cross-zero identity, with the boundary packaged as one set
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- Points of the boundary are not zeros of the zero factor. -/
theorem bndSet_ne_roots {f : ℂ → ℂ} {R : Set ℂ} {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    {x₁ x₂ y₁ y₂ : ℝ} (hR : R = rectSet x₁ x₂ y₁ y₂)
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    ∀ z ∈ bndSet x₁ x₂ y₁ y₂, ∀ a ∈ σ, z ≠ a := by
  intro z hz a ha h
  subst hR
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have him : a.im = y₁ := by rw [← h, h1]
    linarith [(hin a ha).2.2.1]
  · have him : a.im = y₂ := by rw [← h, h1]
    linarith [(hin a ha).2.2.2]
  · have hre : a.re = x₂ := by rw [← h, h1]
    linarith [(hin a ha).2.1]
  · have hre : a.re = x₁ := by rw [← h, h1]
    linarith [(hin a ha).1]


/-- Continuity of the principal part on the boundary. -/
theorem continuousOn_K_logDerivP {f : ℂ → ℂ} (df : Differentiable ℂ f) {R : Set ℂ}
    (hR : IsCompact R) {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    {x₁ x₂ y₁ y₂ : ℝ} (hrect : R = rectSet x₁ x₂ y₁ y₂)
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂)
    {K : ℂ → ℂ} (hKc : Continuous K) :
    ContinuousOn (fun s => K s * logDeriv (BMORRectFactor.zeroFactorC f R) s)
      (bndSet x₁ x₂ y₁ y₂) := by
  have hPdiff : Differentiable ℂ (BMORRectFactor.zeroFactorC f R) :=
    BMORRectFactor.differentiable_zeroFactorC df R hR
  intro z hz
  have hzne := bndSet_ne_roots hP hrect hin z hz
  have hPne : BMORRectFactor.zeroFactorC f R z ≠ 0 := by
    rw [hP z]
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (sub_ne_zero.mpr (hzne a ha)))
  have hdiff : DifferentiableAt ℂ (logDeriv (BMORRectFactor.zeroFactorC f R)) z :=
    (hPdiff.deriv.differentiableAt).div hPdiff.differentiableAt hPne
  exact (hKc.continuousAt.mul hdiff.continuousAt).continuousWithinAt
end BMORProp21

-- ==== BMORCrossZeroMain.lean ====


/-!
# The cross-zero identity

`bnd (fun s => K s · (f'/f)(s)) = 2πi · Σ_ρ m_ρ · K ρ` for `K s = x^s`, `f` entire, `f = P·g` with
`P` the zero factor and `g` zero-free on the rectangle.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- The cross-zero identity. -/
theorem cross_zero {f g : ℂ → ℂ} (df : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {x : ℂ} (hx : x ≠ 0) {K : ℂ → ℂ} (hK : ∀ s : ℂ, K s = x ^ s)
    {R : Set ℂ} (hR : IsCompact R) {x₁ x₂ y₁ y₂ : ℝ} (hrect : R = rectSet x₁ x₂ y₁ y₂)
    {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    (hfg : ∀ z, f z = BMORRectFactor.zeroFactorC f R z * g z)
    (hgne : ∀ z ∈ rectSet x₁ x₂ y₁ y₂, g z ≠ 0)
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂)
    (hle_x : x₁ ≤ x₂) (hle_y : y₁ ≤ y₂) :
    bnd (fun s => K s * logDeriv f s) x₁ x₂ y₁ y₂
      = (2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * K ρ := by
  have hKc : Continuous K := by
    have h : K = fun s => x ^ s := funext hK
    rw [h]
    exact (differentiable_cpow_const hx).continuous
  have hPne : ∀ z ∈ bndSet x₁ x₂ y₁ y₂, BMORRectFactor.zeroFactorC f R z ≠ 0 := by
    intro z hz
    have hzne := bndSet_ne_roots hP hrect hin z hz
    rw [hP z]
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (sub_ne_zero.mpr (hzne a ha)))
  have hlog : ∀ z ∈ bndSet x₁ x₂ y₁ y₂,
      K z * logDeriv f z
        = K z * logDeriv (BMORRectFactor.zeroFactorC f R) z + K z * logDeriv g z := by
    intro z hz
    have hbnd : z ∈ rectSet x₁ x₂ y₁ y₂ := by
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : z.im ∈ Set.uIcc y₁ y₂ := by rw [h1]; exact Set.left_mem_uIcc
        exact ⟨h2, h2'⟩
      · have h2' : z.im ∈ Set.uIcc y₁ y₂ := by rw [h1]; exact Set.right_mem_uIcc
        exact ⟨h2, h2'⟩
      · have h2' : z.re ∈ Set.uIcc x₁ x₂ := by rw [h1]; exact Set.right_mem_uIcc
        exact ⟨h2', h2⟩
      · have h2' : z.re ∈ Set.uIcc x₁ x₂ := by rw [h1]; exact Set.left_mem_uIcc
        exact ⟨h2', h2⟩
    have h1 := hPne z hz
    have h2 : g z ≠ 0 := hgne z hbnd
    rw [BMORRectFactor.logDeriv_factor df R hR hfg hg h1 h2]
    ring
  have hPc : ContinuousOn (fun s => K s * logDeriv (BMORRectFactor.zeroFactorC f R) s)
      (bndSet x₁ x₂ y₁ y₂) :=
    continuousOn_K_logDerivP df hR hP hrect hin hKc
  have hGc : ContinuousOn (fun s => K s * logDeriv g s) (bndSet x₁ x₂ y₁ y₂) := by
    intro z hz
    have hbnd : z ∈ rectSet x₁ x₂ y₁ y₂ := by
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : z.im ∈ Set.uIcc y₁ y₂ := by rw [h1]; exact Set.left_mem_uIcc
        exact ⟨h2, h2'⟩
      · have h2' : z.im ∈ Set.uIcc y₁ y₂ := by rw [h1]; exact Set.right_mem_uIcc
        exact ⟨h2, h2'⟩
      · have h2' : z.re ∈ Set.uIcc x₁ x₂ := by rw [h1]; exact Set.right_mem_uIcc
        exact ⟨h2', h2⟩
      · have h2' : z.re ∈ Set.uIcc x₁ x₂ := by rw [h1]; exact Set.left_mem_uIcc
        exact ⟨h2', h2⟩
    have hgd : DifferentiableAt ℂ (logDeriv g) z :=
      (hg.deriv.differentiableAt).div hg.differentiableAt (hgne z hbnd)
    exact (hKc.continuousAt.mul hgd.continuousAt).continuousWithinAt
  rw [bnd_congr_bnd (G := fun s => K s * logDeriv (BMORRectFactor.zeroFactorC f R) s
    + K s * logDeriv g s) hlog]
  rw [bnd_add_bnd hPc hGc]
  rw [bnd_cpow_logDeriv_zeroFactorC_eq_K hx hK hP hin,
    bnd_cpow_logDeriv_cofactor_K hg hx hK hle_x hle_y hgne, add_zero]

end BMORProp21

-- ==== BMORVerticalEst.lean ====


/-!
# The modulus of `x^s` on a vertical line

`‖x^(c+it)‖ = x^c` for `x > 0`. This is the basic estimate behind every far-contour bound in the
explicit formula.
-/

namespace BMORProp21

open Complex

/-- On the vertical line `Re s = c`, the weight `x^s` has modulus `x^c`. -/
theorem norm_cpow_vertical {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ = Real.exp (c * Real.log x) := by
  have hx0 : (x : ℂ) ≠ 0 := by
    simpa using hx.ne'
  have hlog : Complex.log ((x:ℂ)) = (Real.log x : ℂ) := by
    apply Complex.ext
    · rw [Complex.log_re]
      simp [Real.norm_eq_abs, abs_of_pos hx]
    · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg (le_of_lt hx)]
      simp
  rw [cpow_def_of_ne_zero hx0, Complex.norm_exp, hlog]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  congr 1
  ring

end BMORProp21

-- ==== BMORVerticalBound.lean ====


/-!
# Bounding a vertical leg of the contour

`‖∫_{a}^{b} x^{c+it} F(c+it) dt‖ ≤ x^c · ∫_{a}^{b} ‖F(c+it)‖ dt`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- The vertical leg is controlled by `x^c` times the length-weighted norm of `F`. -/
theorem norm_integral_cpow_vertical_le {x : ℝ} (hx : 0 < x) {c : ℝ} {F : ℂ → ℂ}
    {a b : ℝ} (hab : a ≤ b) :
    ‖∫ t in a..b, (x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * F ((c:ℂ) + (t:ℂ)*I)‖
      ≤ Real.exp (c * Real.log x) * ∫ t in a..b, ‖F ((c:ℂ) + (t:ℂ)*I)‖ := by
  calc ‖∫ t in a..b, (x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * F ((c:ℂ) + (t:ℂ)*I)‖
      ≤ ∫ t in a..b, ‖(x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * F ((c:ℂ) + (t:ℂ)*I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, Real.exp (c * Real.log x) * ‖F ((c:ℂ) + (t:ℂ)*I)‖ := by
        apply intervalIntegral.integral_congr
        intro t _
        show ‖(x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * F ((c:ℂ) + (t:ℂ)*I)‖
          = Real.exp (c * Real.log x) * ‖F ((c:ℂ) + (t:ℂ)*I)‖
        rw [norm_mul, norm_cpow_vertical hx]
    _ = Real.exp (c * Real.log x) * ∫ t in a..b, ‖F ((c:ℂ) + (t:ℂ)*I)‖ := by
        rw [intervalIntegral.integral_const_mul]

end BMORProp21

-- ==== BMORHorizBound.lean ====


/-!
# Bounding a horizontal leg of the contour

`‖∫_{x₁}^{x₂} x^{t+iy} F(t+iy) dt‖ ≤ x^{x₂} · ∫_{x₁}^{x₂} ‖F(t+iy)‖ dt` for `x > 1`, `x₁ ≤ x₂`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- The horizontal leg is controlled by `x^{x₂}` times the norm integral. -/
theorem norm_segH_cpow_le {x : ℝ} (hx : 1 < x) {G : ℂ → ℂ} {y x₁ x₂ : ℝ} (h12 : x₁ ≤ x₂)
    (hGc : Continuous fun t : ℝ => G ((t:ℂ) + (y:ℂ)*I)) :
    ‖∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖
      ≤ Real.exp (x₂ * Real.log x) * ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y:ℂ)*I)‖ := by
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  have hlog : 0 ≤ Real.log x := le_of_lt (Real.log_pos hx)
  have hnorm : Continuous fun t : ℝ => ‖G ((t:ℂ) + (y:ℂ)*I)‖ :=
    (continuous_norm : Continuous fun z : ℂ => ‖z‖).comp hGc
  calc ‖∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖
      ≤ ∫ t in x₁..x₂, ‖(x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm h12
    _ = ∫ t in x₁..x₂, Real.exp (t * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖ := by
        apply intervalIntegral.integral_congr
        intro t _
        show ‖(x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖
          = Real.exp (t * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖
        rw [norm_mul, norm_cpow_vertical hx0]
    _ ≤ ∫ t in x₁..x₂, Real.exp (x₂ * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖ := by
        apply intervalIntegral.integral_mono_on h12
        · exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul hnorm |>.intervalIntegrable _ _
        · exact (continuous_const.mul hnorm).intervalIntegrable _ _
        · intro t ht
          have ht2 : t ≤ x₂ := (Set.mem_Icc.mp ht).2
          have hle : t * Real.log x ≤ x₂ * Real.log x := by nlinarith
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (norm_nonneg _)
    _ = Real.exp (x₂ * Real.log x) * ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y:ℂ)*I)‖ := by
        rw [intervalIntegral.integral_const_mul]

end BMORProp21

-- ==== BMORBndBound2.lean ====


/-!
# The far-contour estimate: algebraic core and the full boundary bound
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- Pure complex arithmetic bound behind the boundary estimate. -/
theorem norm_sub_add_I_le {F1 F2 G1 G2 : ℂ} :
    ‖(F1 - F2) + I*G2 - I*G1‖ ≤ ‖F1‖ + ‖F2‖ + ‖G2‖ + ‖G1‖ := by
  have h1 : ‖(F1 - F2) + I*G2 - I*G1‖ ≤ ‖(F1 - F2) + I*G2‖ + ‖I*G1‖ := norm_sub_le _ _
  have h2 : ‖(F1 - F2) + I*G2‖ ≤ ‖F1 - F2‖ + ‖I*G2‖ := norm_add_le _ _
  have h3 : ‖F1 - F2‖ ≤ ‖F1‖ + ‖F2‖ := norm_sub_le _ _
  have h4 : ‖I*G2‖ = ‖G2‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h5 : ‖I*G1‖ = ‖G1‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  linarith [h1, h2, h3, h4, h5]

/-- The full boundary estimate for `x^s·G`. -/
theorem norm_bnd_cpow_le {x : ℝ} (hx : 1 < x) {G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hH1 : Continuous fun t : ℝ => G ((t:ℂ) + (y₁:ℂ)*I))
    (hH2 : Continuous fun t : ℝ => G ((t:ℂ) + (y₂:ℂ)*I))
    (hV1 : Continuous fun t : ℝ => G ((x₁:ℂ) + (t:ℂ)*I))
    (hV2 : Continuous fun t : ℝ => G ((x₂:ℂ) + (t:ℂ)*I))
    (hle : Real.exp (x₁ * Real.log x) ≤ Real.exp (x₂ * Real.log x)) :
    ‖bnd (fun s => (x:ℂ) ^ s * G s) x₁ x₂ y₁ y₂‖
      ≤ Real.exp (x₂ * Real.log x) *
          ((∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
            + (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖)) := by
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  have ha : 0 ≤ ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hx12 (fun t _ => norm_nonneg _)
  have hb : 0 ≤ ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hx12 (fun t _ => norm_nonneg _)
  have hc : 0 ≤ ∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hy12 (fun t _ => norm_nonneg _)
  have hd : 0 ≤ ∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hy12 (fun t _ => norm_nonneg _)
  have t1 : ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖ :=
    norm_segH_cpow_le (x := x) (G := G) (y := y₁) hx hx12 hH1
  have t2 : ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖ :=
    norm_segH_cpow_le (x := x) (G := G) (y := y₂) hx hx12 hH2
  have t3 : ‖(∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * ∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖ :=
    norm_integral_cpow_vertical_le (x := x) hx0 (c := x₂) (F := G) hy12
  have t4 : ‖(∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₁ * Real.log x) * ∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖ :=
    norm_integral_cpow_vertical_le (x := x) hx0 (c := x₁) (F := G) hy12
  have h4' : ‖(∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * ∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖ :=
    le_trans t4 (mul_le_mul_of_nonneg_right hle hd)
  have hkey := norm_sub_add_I_le
    (F1 := ∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))
    (F2 := ∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))
    (G2 := ∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))
    (G1 := ∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))
  unfold bnd segH segV
  have step1 : ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))
        - (∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))
        + I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))
        - I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖) := by
    linarith [hkey, t1, t2, t3, h4']
  calc ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))
        - (∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))
        + I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))
        - I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖) := step1
    _ = Real.exp (x₂ * Real.log x) *
          ((∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
            + (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖)) := by ring

end BMORProp21

-- ==== BMORBndBoundOn.lean ====


/-!
# The far-contour estimate with continuity only on the leg

Same bounds as `norm_segH_cpow_le` / `norm_integral_cpow_vertical_le` / `norm_bnd_cpow_le`, but
requiring continuity only on the segment. This is what `L'/L` satisfies: it is continuous on the
contour but not globally.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- Horizontal leg, continuity on the segment only. -/
theorem norm_segH_cpow_le_on {x : ℝ} (hx : 1 < x) {G : ℂ → ℂ} {y x₁ x₂ : ℝ} (h12 : x₁ ≤ x₂)
    (hGc : ContinuousOn (fun t : ℝ => G ((t:ℂ) + (y:ℂ)*I)) (Set.uIcc x₁ x₂)) :
    ‖∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y:ℂ)*I)‖) := by
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  have hlog : 0 ≤ Real.log x := le_of_lt (Real.log_pos hx)
  have hnorm : ContinuousOn (fun t : ℝ => ‖G ((t:ℂ) + (y:ℂ)*I)‖) (Set.uIcc x₁ x₂) :=
    (continuous_norm : Continuous fun z : ℂ => ‖z‖).comp_continuousOn hGc
  calc ‖∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖
      ≤ ∫ t in x₁..x₂, ‖(x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm h12
    _ = ∫ t in x₁..x₂, Real.exp (t * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖ := by
        apply intervalIntegral.integral_congr
        intro t _
        show ‖(x:ℂ) ^ ((t:ℂ) + (y:ℂ)*I) * G ((t:ℂ) + (y:ℂ)*I)‖
          = Real.exp (t * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖
        rw [norm_mul, norm_cpow_vertical hx0]
    _ ≤ ∫ t in x₁..x₂, Real.exp (x₂ * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖ := by
        apply intervalIntegral.integral_mono_on h12
        · have hc1 : ContinuousOn (fun t : ℝ => Real.exp (t * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖)
              (Set.uIcc x₁ x₂) :=
            (Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn.mul hnorm
          exact hc1.intervalIntegrable
        · have hc2 : ContinuousOn (fun t : ℝ => Real.exp (x₂ * Real.log x) * ‖G ((t:ℂ) + (y:ℂ)*I)‖)
              (Set.uIcc x₁ x₂) :=
            continuousOn_const.mul hnorm
          exact hc2.intervalIntegrable
        · intro t ht
          have ht2 : t ≤ x₂ := (Set.mem_Icc.mp ht).2
          have hle : t * Real.log x ≤ x₂ * Real.log x := by nlinarith
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (norm_nonneg _)
    _ = Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y:ℂ)*I)‖) := by
        rw [intervalIntegral.integral_const_mul]

/-- Vertical leg, continuity on the segment only. -/
theorem norm_segV_cpow_le_on {x : ℝ} (hx : 0 < x) {G : ℂ → ℂ} {c y₁ y₂ : ℝ} (h12 : y₁ ≤ y₂)
    (hGc : ContinuousOn (fun t : ℝ => G ((c:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂)) :
    ‖∫ t in y₁..y₂, (x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * G ((c:ℂ) + (t:ℂ)*I)‖
      ≤ Real.exp (c * Real.log x) * (∫ t in y₁..y₂, ‖G ((c:ℂ) + (t:ℂ)*I)‖) := by
  calc ‖∫ t in y₁..y₂, (x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * G ((c:ℂ) + (t:ℂ)*I)‖
      ≤ ∫ t in y₁..y₂, ‖(x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * G ((c:ℂ) + (t:ℂ)*I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm h12
    _ = ∫ t in y₁..y₂, Real.exp (c * Real.log x) * ‖G ((c:ℂ) + (t:ℂ)*I)‖ := by
        apply intervalIntegral.integral_congr
        intro t _
        show ‖(x:ℂ) ^ ((c:ℂ) + (t:ℂ)*I) * G ((c:ℂ) + (t:ℂ)*I)‖
          = Real.exp (c * Real.log x) * ‖G ((c:ℂ) + (t:ℂ)*I)‖
        rw [norm_mul, norm_cpow_vertical hx]
    _ = Real.exp (c * Real.log x) * (∫ t in y₁..y₂, ‖G ((c:ℂ) + (t:ℂ)*I)‖) := by
        rw [intervalIntegral.integral_const_mul]

end BMORProp21

-- ==== BMORIntegralConst.lean ====


/-!
# A segment integral bounded by length times a uniform bound

`F ≤ C` pointwise ⇒ `∫_a^b F ≤ (b-a)·C`. This turns a uniform bound on `‖g'/g‖` on the contour
into the corresponding contribution to the error term.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- A uniform pointwise bound gives a length-times-bound integral estimate. -/
theorem integral_le_of_le_const {F : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hF : Continuous F) (h : ∀ t, F t ≤ C) :
    ∫ t in a..b, F t ≤ (b - a) * C := by
  have hconst : (∫ t in a..b, C) = (b - a) * C := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [← hconst]
  exact intervalIntegral.integral_mono_on hab (hF.intervalIntegrable _ _)
    intervalIntegrable_const (fun t _ => h t)

end BMORProp21

-- ==== BMORLogDerivBound.lean ====


/-!
# Bounding `‖f'/f‖` by the zeros

With `f = P·g` (`P` the zero factor, `g` zero-free on the rectangle),
`‖f'/f(z)‖ ≤ Σ_ρ m_ρ·‖(z-ρ)⁻¹‖ + ‖g'/g(z)‖`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- The logarithmic derivative of `f` is bounded by the pole terms plus the cofactor term. -/
theorem norm_logDeriv_factor_le {f g : ℂ → ℂ} (df : Differentiable ℂ f) (R : Set ℂ)
    (hR : IsCompact R) {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    (hfg : ∀ z, f z = BMORRectFactor.zeroFactorC f R z * g z) (hg : Differentiable ℂ g)
    {z : ℂ} (hz : ∀ a ∈ σ, z ≠ a) (hgz : g z ≠ 0) :
    ‖logDeriv f z‖ ≤ (∑ a ∈ σ, (m a : ℝ) * ‖(z - a)⁻¹‖) + ‖logDeriv g z‖ := by
  have hPne : BMORRectFactor.zeroFactorC f R z ≠ 0 := by
    rw [hP z]
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (sub_ne_zero.mpr (hz a ha)))
  rw [BMORRectFactor.logDeriv_factor df R hR hfg hg hPne hgz,
    logDeriv_zeroFactorC_eq R hP hz]
  calc ‖(∑ a ∈ σ, (m a : ℂ) / (z - a)) + logDeriv g z‖
      ≤ ‖∑ a ∈ σ, (m a : ℂ) / (z - a)‖ + ‖logDeriv g z‖ := norm_add_le _ _
    _ ≤ (∑ a ∈ σ, ‖(m a : ℂ) / (z - a)‖) + ‖logDeriv g z‖ := by
        have h := norm_sum_le σ (fun a => (m a : ℂ) / (z - a))
        linarith
    _ = (∑ a ∈ σ, (m a : ℝ) * ‖(z - a)⁻¹‖) + ‖logDeriv g z‖ := by
        have hs : (∑ a ∈ σ, ‖(m a : ℂ) / (z - a)‖)
            = ∑ a ∈ σ, (m a : ℝ) * ‖(z - a)⁻¹‖ := by
          apply Finset.sum_congr rfl
          intro a _
          rw [norm_div, Complex.norm_natCast, norm_inv, div_eq_mul_inv]
        rw [hs]

end BMORProp21

-- ==== BMORDistBound.lean ====


/-!
# The distance bound for the pole terms

If `δ ≤ ‖φ t - ρ‖` on the segment, then `∫ ‖(φ t - ρ)⁻¹‖ ≤ (b - a)·δ⁻¹`.
This is the elementary estimate that turns each zero into a `1/dist` contribution.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- Pointwise: a lower bound on the distance gives a bound on the inverse. -/
theorem norm_inv_sub_le {ρ z : ℂ} {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ ‖z - ρ‖) :
    ‖(z - ρ)⁻¹‖ ≤ δ⁻¹ := by
  rw [norm_inv]
  exact (inv_le_inv₀ (show (0:ℝ) < ‖z - ρ‖ by linarith) hδ).mpr h

/-- The integral of `‖(φ t - ρ)⁻¹‖` is at most `length/δ`. -/
theorem integral_norm_inv_sub_le {ρ : ℂ} {φ : ℝ → ℂ} {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hφc : Continuous φ) (h : ∀ t, δ ≤ ‖φ t - ρ‖) :
    ∫ t in a..b, ‖(φ t - ρ)⁻¹‖ ≤ (b - a) * δ⁻¹ := by
  have hne : ∀ t, φ t - ρ ≠ 0 := by
    intro t h0
    have : ‖φ t - ρ‖ = 0 := by rw [h0]; simp
    linarith [h t]
  have hint : IntervalIntegrable (fun t : ℝ => ‖(φ t - ρ)⁻¹‖) volume a b := by
    apply Continuous.intervalIntegrable
    exact (hφc.sub continuous_const).inv₀ hne |>.norm
  have hconst : (∫ t in a..b, (δ⁻¹ : ℝ)) = (b - a) * δ⁻¹ := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
  intro t _
  exact norm_inv_sub_le hδ (h t)

end BMORProp21

-- ==== BMORPoleIntegral.lean ====


/-!
# The pole sum integrated along a segment

`∫ Σ_ρ m_ρ·‖(φ t - ρ)⁻¹‖ ≤ Σ_ρ m_ρ·((b-a)·δ_ρ⁻¹)`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators


/-- Real-valued finite sum of interval-integrable functions. -/
theorem intervalIntegrable_finset_sum_real {ι : Type*} (σ : Finset ι) (g : ι → ℝ → ℝ)
    {a b : ℝ} (h : ∀ i ∈ σ, IntervalIntegrable (g i) volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ σ, g i t) volume a b := by
  classical
  induction σ using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable a b
  | insert a0 s ha ih =>
      have h1 := h a0 (Finset.mem_insert_self a0 s)
      have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have heq : (fun t => ∑ i ∈ insert a0 s, g i t) = (fun t => g a0 t + ∑ i ∈ s, g i t) := by
        funext t
        rw [Finset.sum_insert ha]
      rw [heq]
      exact h1.add h2
/-- Real-valued finite sum interchange. -/
theorem integral_finset_sum_gen_real {ι : Type*} (σ : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    {a b : ℝ} (h : ∀ i ∈ σ, IntervalIntegrable (fun t => f i t) volume a b) :
    ∫ t in a..b, ∑ i ∈ σ, c i * f i t = ∑ i ∈ σ, c i * ∫ t in a..b, f i t := by
  classical
  induction σ using Finset.induction_on with
  | empty => simp
  | insert a0 s ha ih =>
      have h1 : IntervalIntegrable (fun t => c a0 * f a0 t) volume a b :=
        (h a0 (Finset.mem_insert_self a0 s)).const_mul (c a0)
      have h2 : IntervalIntegrable (fun t => ∑ i ∈ s, c i * f i t) volume a b :=
        intervalIntegrable_finset_sum_real s (fun i => fun t => c i * f i t)
          (fun i hi => (h i (Finset.mem_insert_of_mem hi)).const_mul (c i))
      have heq : (fun t => ∑ i ∈ insert a0 s, c i * f i t)
          = (fun t => c a0 * f a0 t + ∑ i ∈ s, c i * f i t) := by
        funext t
        rw [Finset.sum_insert ha]
      rw [heq, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

/-- The integrated pole sum is bounded by the distance contributions. -/
theorem integral_pole_sum_le {σ : Finset ℂ} {m : ℂ → ℕ} {φ : ℝ → ℂ} {δ : ℂ → ℝ}
    (hφc : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    (hδ : ∀ ρ ∈ σ, 0 < δ ρ) (hdist : ∀ ρ ∈ σ, ∀ t, δ ρ ≤ ‖φ t - ρ‖) :
    ∫ t in a..b, (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖)
      ≤ ∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹) := by
  rw [integral_finset_sum_gen_real σ (fun ρ => (m ρ : ℝ)) (fun ρ t => ‖(φ t - ρ)⁻¹‖) ?_]
  · apply Finset.sum_le_sum
    intro ρ hρ
    exact mul_le_mul_of_nonneg_left
      (integral_norm_inv_sub_le (hδ ρ hρ) hab hφc (hdist ρ hρ)) (Nat.cast_nonneg _)
  · intro ρ hρ
    have hne : ∀ t, φ t - ρ ≠ 0 := by
      intro t h0
      have : ‖φ t - ρ‖ = 0 := by rw [h0]; simp
      linarith [hdist ρ hρ t, hδ ρ hρ]
    exact ((hφc.sub continuous_const).inv₀ hne).norm.intervalIntegrable _ _

end BMORProp21

-- ==== BMORLogDerivIntegral.lean ====


/-!
# The integrated `f'/f` bound

`∫ ‖f'/f(φ t)‖ ≤ Σ_ρ m_ρ·((b-a)·δ_ρ⁻¹) + ∫ ‖g'/g(φ t)‖`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators


/-- Real-valued finite sum of continuous functions. -/
theorem continuous_finset_sum_real {ι : Type*} (σ : Finset ι) (g : ι → ℝ → ℝ)
    (h : ∀ i ∈ σ, Continuous (g i)) :
    Continuous (fun t => ∑ i ∈ σ, g i t) := by
  classical
  induction σ using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a0 s ha ih =>
      have h1 := h a0 (Finset.mem_insert_self a0 s)
      have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have heq : (fun t => ∑ i ∈ insert a0 s, g i t) = (fun t => g a0 t + ∑ i ∈ s, g i t) := by
        funext t
        rw [Finset.sum_insert ha]
      rw [heq]
      exact h1.add h2
/-- The integrated logarithmic derivative is bounded by the pole contributions. -/
theorem integral_norm_logDeriv_le {f g : ℂ → ℂ} (df : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {R : Set ℂ} (hR : IsCompact R) {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    (hfg : ∀ z, f z = BMORRectFactor.zeroFactorC f R z * g z)
    (hne : ∀ z ∈ R, f z ≠ 0)
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hmaps : ∀ t, φ t ∈ R)
    (hφne : ∀ ρ ∈ σ, ∀ t, φ t ≠ ρ)
    {a b : ℝ} (hab : a ≤ b) {δ : ℂ → ℝ}
    (hδ : ∀ ρ ∈ σ, 0 < δ ρ) (hdist : ∀ ρ ∈ σ, ∀ t, δ ρ ≤ ‖φ t - ρ‖) :
    ∫ t in a..b, ‖logDeriv f (φ t)‖
      ≤ (∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹)) + ∫ t in a..b, ‖logDeriv g (φ t)‖ := by
  have hgz : ∀ t, g (φ t) ≠ 0 := by
    intro t h0
    have h1 : f (φ t) = 0 := by
      rw [hfg, h0, mul_zero]
    exact hne _ (hmaps t) h1
  have hpt : ∀ t, ‖logDeriv f (φ t)‖
      ≤ (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) + ‖logDeriv g (φ t)‖ :=
    fun t => norm_logDeriv_factor_le df R hR hP hfg hg (fun ρ hρ => hφne ρ hρ t) (hgz t)
  have hcontP : Continuous fun t => ∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖ := by
    apply continuous_finset_sum_real
    intro ρ hρ
    have hne' : ∀ t, φ t - ρ ≠ 0 := by
      intro t h0
      have : ‖φ t - ρ‖ = 0 := by rw [h0]; simp
      linarith [hdist ρ hρ t, hδ ρ hρ]
    exact continuous_const.mul ((hφc.sub continuous_const).inv₀ hne').norm
  have hcontG : Continuous fun t => ‖logDeriv g (φ t)‖ := by
    have hne' : ∀ t, g (φ t) ≠ 0 := hgz
    have hdv : Differentiable ℂ (deriv g) := hg.deriv
    exact ((hdv.continuous.comp hφc).div (hg.continuous.comp hφc) hne').norm
  have hcontF : Continuous fun t => ‖logDeriv f (φ t)‖ := by
    have hne' : ∀ t, f (φ t) ≠ 0 := fun t => hne _ (hmaps t)
    have hdv : Differentiable ℂ (deriv f) := df.deriv
    exact ((hdv.continuous.comp hφc).div (df.continuous.comp hφc) hne').norm
  have iF : IntervalIntegrable (fun t => ‖logDeriv f (φ t)‖) volume a b :=
    hcontF.intervalIntegrable _ _
  have iG : IntervalIntegrable
      (fun t => (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) + ‖logDeriv g (φ t)‖) volume a b :=
    (hcontP.add hcontG).intervalIntegrable _ _
  have iS : IntervalIntegrable (fun t => ∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) volume a b :=
    hcontP.intervalIntegrable _ _
  have iN : IntervalIntegrable (fun t => ‖logDeriv g (φ t)‖) volume a b :=
    hcontG.intervalIntegrable _ _
  calc ∫ t in a..b, ‖logDeriv f (φ t)‖
      ≤ ∫ t in a..b, ((∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) + ‖logDeriv g (φ t)‖) :=
        intervalIntegral.integral_mono_on hab iF iG (fun t _ => hpt t)
    _ = (∫ t in a..b, (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖))
          + ∫ t in a..b, ‖logDeriv g (φ t)‖ :=
        intervalIntegral.integral_add iS iN
    _ ≤ (∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹))
          + ∫ t in a..b, ‖logDeriv g (φ t)‖ := by
        have hp : ∫ t in a..b, (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖)
            ≤ ∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹) :=
          integral_pole_sum_le hφc hab hδ hdist
        linarith

end BMORProp21

-- ==== BMORDistOn.lean ====


/-!
# The pole sum on a segment, with all hypotheses on the segment

`∫_a^b Σ_ρ m_ρ·‖(φ t - ρ)⁻¹‖ ≤ Σ_ρ m_ρ·((b-a)·δ_ρ⁻¹)` where `δ_ρ ≤ ‖φ t - ρ‖` only for
`t ∈ uIcc a b`. This is what the contour legs actually satisfy.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- Segment version of the distance integral bound. -/
theorem integral_norm_inv_sub_le_on {ρ : ℂ} {φ : ℝ → ℂ} {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hφc : Continuous φ) (h : ∀ t ∈ Set.uIcc a b, δ ≤ ‖φ t - ρ‖) :
    ∫ t in a..b, ‖(φ t - ρ)⁻¹‖ ≤ (b - a) * δ⁻¹ := by
  have hne : ∀ t ∈ Set.uIcc a b, φ t - ρ ≠ 0 := by
    intro t ht h0
    have h0' : ‖φ t - ρ‖ = 0 := by rw [h0]; simp
    linarith [h t ht]
  have hcont : ContinuousOn (fun t : ℝ => ‖(φ t - ρ)⁻¹‖) (Set.uIcc a b) :=
    (((hφc.sub continuous_const).continuousOn).inv₀ hne).norm
  have hconst : (∫ t in a..b, (δ⁻¹ : ℝ)) = (b - a) * δ⁻¹ := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [← hconst]
  exact intervalIntegral.integral_mono_on hab hcont.intervalIntegrable
    intervalIntegrable_const (fun t ht => norm_inv_sub_le hδ (h t (by rw [Set.uIcc_of_le hab]; exact ht)))

/-- Segment version of the integrated pole sum bound. -/
theorem integral_pole_sum_le_on {σ : Finset ℂ} {m : ℂ → ℕ} {φ : ℝ → ℂ} {δ : ℂ → ℝ}
    (hφc : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    (hδ : ∀ ρ ∈ σ, 0 < δ ρ) (hdist : ∀ ρ ∈ σ, ∀ t ∈ Set.uIcc a b, δ ρ ≤ ‖φ t - ρ‖) :
    ∫ t in a..b, (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖)
      ≤ ∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹) := by
  rw [integral_finset_sum_gen_real σ (fun ρ => (m ρ : ℝ)) (fun ρ t => ‖(φ t - ρ)⁻¹‖) ?_]
  · apply Finset.sum_le_sum
    intro ρ hρ
    exact mul_le_mul_of_nonneg_left
      (integral_norm_inv_sub_le_on (hδ ρ hρ) hab hφc (hdist ρ hρ)) (Nat.cast_nonneg _)
  · intro ρ hρ
    have hne : ∀ t ∈ Set.uIcc a b, φ t - ρ ≠ 0 := by
      intro t ht h0
      have h0' : ‖φ t - ρ‖ = 0 := by rw [h0]; simp
      linarith [hdist ρ hρ t ht, hδ ρ hρ]
    exact ((((hφc.sub continuous_const).continuousOn).inv₀ hne).norm).intervalIntegrable

end BMORProp21

-- ==== BMORBndFinal.lean ====


/-!
# The far-contour estimate for `x^s · (f'/f)`

`‖bnd (x^s·f'/f)‖ ≤ x^{x₂} · (sum of the four norm integrals of `f'/f`)`, requiring only that `f`
does not vanish on the rectangle.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- `f'/f` is continuous at any point where `f` does not vanish. -/
theorem continuousAt_logDeriv {f : ℂ → ℂ} (df : Differentiable ℂ f) {z : ℂ} (hz : f z ≠ 0) :
    ContinuousAt (logDeriv f) z :=
  ((df.deriv.differentiableAt).div df.differentiableAt hz).continuousAt

/-- The full boundary estimate with continuity only on the legs. -/
theorem norm_bnd_cpow_le_on {x : ℝ} (hx : 1 < x) {G : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hH1 : ContinuousOn (fun t : ℝ => G ((t:ℂ) + (y₁:ℂ)*I)) (Set.uIcc x₁ x₂))
    (hH2 : ContinuousOn (fun t : ℝ => G ((t:ℂ) + (y₂:ℂ)*I)) (Set.uIcc x₁ x₂))
    (hV1 : ContinuousOn (fun t : ℝ => G ((x₁:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂))
    (hV2 : ContinuousOn (fun t : ℝ => G ((x₂:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂))
    (hle : Real.exp (x₁ * Real.log x) ≤ Real.exp (x₂ * Real.log x)) :
    ‖bnd (fun s => (x:ℂ) ^ s * G s) x₁ x₂ y₁ y₂‖
      ≤ Real.exp (x₂ * Real.log x) *
          ((∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
            + (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖)) := by
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  have ha : 0 ≤ ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hx12 (fun t _ => norm_nonneg _)
  have hb : 0 ≤ ∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hx12 (fun t _ => norm_nonneg _)
  have hc : 0 ≤ ∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hy12 (fun t _ => norm_nonneg _)
  have hd : 0 ≤ ∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖ :=
    intervalIntegral.integral_nonneg hy12 (fun t _ => norm_nonneg _)
  have t1 : ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖) :=
    norm_segH_cpow_le_on (x := x) (G := G) (y := y₁) hx hx12 hH1
  have t2 : ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖) :=
    norm_segH_cpow_le_on (x := x) (G := G) (y := y₂) hx hx12 hH2
  have t3 : ‖(∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖) :=
    norm_segV_cpow_le_on (x := x) hx0 (c := x₂) (G := G) hy12 hV2
  have t4 : ‖(∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₁ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖) :=
    norm_segV_cpow_le_on (x := x) hx0 (c := x₁) (G := G) hy12 hV1
  have h4' : ‖(∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖) :=
    le_trans t4 (mul_le_mul_of_nonneg_right hle hd)
  have hkey := norm_sub_add_I_le
    (F1 := ∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))
    (F2 := ∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))
    (G2 := ∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))
    (G1 := ∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))
  unfold bnd segH segV
  have step1 : ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))
        - (∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))
        + I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))
        - I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖) := by
    linarith [hkey, t1, t2, t3, h4']
  calc ‖(∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * G ((t:ℂ) + (y₁:ℂ)*I))
        - (∫ t in x₁..x₂, (x:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * G ((t:ℂ) + (y₂:ℂ)*I))
        + I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₂:ℂ) + (t:ℂ)*I) * G ((x₂:ℂ) + (t:ℂ)*I))
        - I * (∫ t in y₁..y₂, (x:ℂ) ^ ((x₁:ℂ) + (t:ℂ)*I) * G ((x₁:ℂ) + (t:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
        + Real.exp (x₂ * Real.log x) * (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖) := step1
    _ = Real.exp (x₂ * Real.log x) *
          ((∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₁:ℂ)*I)‖)
            + (∫ t in x₁..x₂, ‖G ((t:ℂ) + (y₂:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₂:ℂ) + (t:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖G ((x₁:ℂ) + (t:ℂ)*I)‖)) := by ring


/-- The far-contour estimate for `x^s · (f'/f)`. -/
theorem norm_bnd_cpow_logDeriv_le {f : ℂ → ℂ} (df : Differentiable ℂ f)
    {x : ℝ} (hx : 1 < x) {x₁ x₂ y₁ y₂ : ℝ} (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hne : ∀ z ∈ rectSet x₁ x₂ y₁ y₂, f z ≠ 0)
    (hle : Real.exp (x₁ * Real.log x) ≤ Real.exp (x₂ * Real.log x)) :
    ‖bnd (fun s => (x:ℂ) ^ s * logDeriv f s) x₁ x₂ y₁ y₂‖
      ≤ Real.exp (x₂ * Real.log x) *
          ((∫ t in x₁..x₂, ‖logDeriv f ((t:ℂ) + (y₁:ℂ)*I)‖)
            + (∫ t in x₁..x₂, ‖logDeriv f ((t:ℂ) + (y₂:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖logDeriv f ((x₂:ℂ) + (t:ℂ)*I)‖)
            + (∫ t in y₁..y₂, ‖logDeriv f ((x₁:ℂ) + (t:ℂ)*I)‖)) := by
  apply norm_bnd_cpow_le_on (G := fun z => logDeriv f z) hx hx12 hy12 _ _ _ _ hle
  · intro t ht
    exact (continuousAt_logDeriv df (hne _ ⟨by simpa using ht, by simpa using Set.left_mem_uIcc⟩)).comp_continuousWithinAt
      (cont_h y₁).continuousAt.continuousWithinAt
  · intro t ht
    exact (continuousAt_logDeriv df (hne _ ⟨by simpa using ht, by simpa using Set.right_mem_uIcc⟩)).comp_continuousWithinAt
      (cont_h y₂).continuousAt.continuousWithinAt
  · intro t ht
    exact (continuousAt_logDeriv df (hne _ ⟨by simpa using Set.left_mem_uIcc, by simpa using ht⟩)).comp_continuousWithinAt
      (cont_v x₁).continuousAt.continuousWithinAt
  · intro t ht
    exact (continuousAt_logDeriv df (hne _ ⟨by simpa using Set.right_mem_uIcc, by simpa using ht⟩)).comp_continuousWithinAt
      (cont_v x₂).continuousAt.continuousWithinAt
end BMORProp21

-- ==== BMORLogDerivIntegralOn2.lean ====


/-!
# The integrated `f'/f` bound, all hypotheses on the segment
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- Segment version of the integrated logarithmic derivative bound. -/
theorem integral_norm_logDeriv_le_on {f g : ℂ → ℂ} (df : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {R : Set ℂ} (hR : IsCompact R) {σ : Finset ℂ} {m : ℂ → ℕ}
    (hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a))
    (hfg : ∀ z, f z = BMORRectFactor.zeroFactorC f R z * g z)
    (hne : ∀ z ∈ R, f z ≠ 0)
    {φ : ℝ → ℂ} (hφc : Continuous φ) {a b : ℝ}
    (hmaps : ∀ t ∈ Set.uIcc a b, φ t ∈ R)
    (hφne : ∀ ρ ∈ σ, ∀ t ∈ Set.uIcc a b, φ t ≠ ρ)
    (hab : a ≤ b) {δ : ℂ → ℝ}
    (hδ : ∀ ρ ∈ σ, 0 < δ ρ)
    (hdist : ∀ ρ ∈ σ, ∀ t ∈ Set.uIcc a b, δ ρ ≤ ‖φ t - ρ‖) :
    ∫ t in a..b, ‖logDeriv f (φ t)‖
      ≤ (∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹))
        + ∫ t in a..b, ‖logDeriv g (φ t)‖ := by
  have hmem : a ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact Set.left_mem_Icc.mpr hab
  have hgz : ∀ t ∈ Set.uIcc a b, g (φ t) ≠ 0 := by
    intro t ht h0
    have h1 : f (φ t) = 0 := by rw [hfg, h0, mul_zero]
    exact hne _ (hmaps t ht) h1
  have hpt : ∀ t ∈ Set.uIcc a b, ‖logDeriv f (φ t)‖
      ≤ (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) + ‖logDeriv g (φ t)‖ :=
    fun t ht => norm_logDeriv_factor_le df R hR hP hfg hg (fun ρ hρ => hφne ρ hρ t ht) (hgz t ht)
  have hcontF : ContinuousOn (fun t => ‖logDeriv f (φ t)‖) (Set.uIcc a b) := by
    intro t ht
    exact ((continuousAt_logDeriv df (hne _ (hmaps t ht))).comp_continuousWithinAt
      hφc.continuousAt.continuousWithinAt).norm
  have hcontG : ContinuousOn (fun t => ‖logDeriv g (φ t)‖) (Set.uIcc a b) := by
    intro t ht
    exact ((continuousAt_logDeriv hg (hgz t ht)).comp_continuousWithinAt
      hφc.continuousAt.continuousWithinAt).norm
  have hterm : ∀ ρ ∈ σ, IntervalIntegrable
      (fun t => (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) volume a b := by
    intro ρ hρ
    have hne' : ∀ t ∈ Set.uIcc a b, φ t - ρ ≠ 0 :=
      fun t ht => sub_ne_zero.mpr (hφne ρ hρ t ht)
    have hc : ContinuousOn (fun t => (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) (Set.uIcc a b) :=
      continuousOn_const.mul (((hφc.sub continuous_const).continuousOn).inv₀ hne').norm
    exact hc.intervalIntegrable
  have iS : IntervalIntegrable (fun t => ∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) volume a b :=
    intervalIntegrable_finset_sum_real σ (fun ρ t => (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) hterm
  have iN : IntervalIntegrable (fun t => ‖logDeriv g (φ t)‖) volume a b :=
    hcontG.intervalIntegrable
  have iF : IntervalIntegrable (fun t => ‖logDeriv f (φ t)‖) volume a b :=
    hcontF.intervalIntegrable
  have iG : IntervalIntegrable
      (fun t => (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) + ‖logDeriv g (φ t)‖) volume a b :=
    iS.add iN
  calc ∫ t in a..b, ‖logDeriv f (φ t)‖
      ≤ ∫ t in a..b, ((∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖) + ‖logDeriv g (φ t)‖) :=
        intervalIntegral.integral_mono_on hab iF iG (fun t ht => hpt t (by rw [Set.uIcc_of_le hab]; exact ht))
    _ = (∫ t in a..b, (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖))
          + ∫ t in a..b, ‖logDeriv g (φ t)‖ :=
        intervalIntegral.integral_add iS iN
    _ ≤ (∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹))
          + ∫ t in a..b, ‖logDeriv g (φ t)‖ := by
        have hp : ∫ t in a..b, (∑ ρ ∈ σ, (m ρ : ℝ) * ‖(φ t - ρ)⁻¹‖)
            ≤ ∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (δ ρ)⁻¹) :=
          integral_pole_sum_le_on hφc hab hδ hdist
        linarith

end BMORProp21

-- ==== BMORContourData.lean ====


/-!
# Packaging the contour data

The final contour estimate needs the same six facts about `(f, g, R, σ, m, δ, C_g)` at every leg.
Bundling them into a structure keeps the hypothesis count of the theorem within what Lean's
elaborator can handle (see the notes on the "size wall").
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- Segment version of the uniform-bound integral estimate. -/
theorem integral_le_of_le_const_on {F : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.uIcc a b)) (h : ∀ t ∈ Set.uIcc a b, F t ≤ C) :
    ∫ t in a..b, F t ≤ (b - a) * C := by
  have hconst : (∫ t in a..b, C) = (b - a) * C := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [← hconst]
  exact intervalIntegral.integral_mono_on hab hF.intervalIntegrable
    intervalIntegrable_const
    (fun t ht => h t (by rw [Set.uIcc_of_le hab]; exact ht))

/-- The data needed for the contour estimate. -/
structure ContourData (f g : ℂ → ℂ) (R : Set ℂ) (σ : Finset ℂ) (m : ℂ → ℕ) where
  /-- `P` is the zero factor as a finite product. -/
  hP : ∀ z, BMORRectFactor.zeroFactorC f R z = ∏ a ∈ σ, (z-a)^(m a)
  /-- `f` factors as `P·g`. -/
  hfg : ∀ z, f z = BMORRectFactor.zeroFactorC f R z * g z
  /-- `f` does not vanish on `R`. -/
  hne : ∀ z ∈ R, f z ≠ 0
  /-- Distance from each zero to `R`. -/
  delta : ℂ → ℝ
  hδ : ∀ ρ ∈ σ, 0 < delta ρ
  hdist : ∀ ρ ∈ σ, ∀ z ∈ R, delta ρ ≤ ‖z - ρ‖
  /-- Uniform bound on `g'/g` on `R`. -/
  Cg : ℝ
  hCg : ∀ z ∈ R, ‖logDeriv g z‖ ≤ Cg

end BMORProp21

-- ==== BMORLegBound.lean ====


/-!
# One leg of the contour estimate
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- The `f'/f` integral along one leg is bounded by the pole contributions plus `length·C_g`. -/
theorem leg_bound {f g : ℂ → ℂ} (df : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {R : Set ℂ} (hR : IsCompact R) {σ : Finset ℂ} {m : ℂ → ℕ}
    (D : ContourData f g R σ m) {φ : ℝ → ℂ} (hφc : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    (hmaps : ∀ t ∈ Set.uIcc a b, φ t ∈ R) :
    ∫ t in a..b, ‖logDeriv f (φ t)‖
      ≤ (∑ ρ ∈ σ, (m ρ : ℝ) * ((b - a) * (D.delta ρ)⁻¹)) + (b - a) * D.Cg := by
  have hφne : ∀ ρ ∈ σ, ∀ t ∈ Set.uIcc a b, φ t ≠ ρ := by
    intro ρ hρ t ht h0
    have hd := D.hdist ρ hρ (φ t) (hmaps t ht)
    rw [h0, sub_self, norm_zero] at hd
    linarith [D.hδ ρ hρ]
  have hgz : ∀ t ∈ Set.uIcc a b, g (φ t) ≠ 0 := by
    intro t ht h0
    have h1 : f (φ t) = 0 := by rw [D.hfg, h0, mul_zero]
    exact D.hne _ (hmaps t ht) h1
  have h1 := integral_norm_logDeriv_le_on df hg hR D.hP D.hfg D.hne hφc hmaps hφne hab D.hδ
    (fun ρ hρ t ht => D.hdist ρ hρ (φ t) (hmaps t ht))
  have hcontG : ContinuousOn (fun t => ‖logDeriv g (φ t)‖) (Set.uIcc a b) :=
    fun t ht => ((continuousAt_logDeriv hg (hgz t ht)).comp_continuousWithinAt
      hφc.continuousAt.continuousWithinAt).norm
  have h2 : ∫ t in a..b, ‖logDeriv g (φ t)‖ ≤ (b - a) * D.Cg :=
    integral_le_of_le_const_on hab hcontG (fun t ht => D.hCg _ (hmaps t ht))
  linarith

end BMORProp21

-- ==== BMORFinalBound.lean ====


/-!
# The final contour estimate

`‖bnd (x^s·(f'/f))‖ ≤ x^{x₂}·(2(x₂-x₁) + 2(y₂-y₁))·(Σ_ρ m_ρ·δ_ρ⁻¹ + C_g)`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

set_option maxHeartbeats 800000 in
/-- The final contour estimate. -/
theorem norm_bnd_cpow_logDeriv_le_final {f g : ℂ → ℂ} (df : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {R : Set ℂ} (hR : IsCompact R) {σ : Finset ℂ} {m : ℂ → ℕ}
    (D : ContourData f g R σ m)
    {x : ℝ} (hx : 1 < x) {x₁ x₂ y₁ y₂ : ℝ} (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hRr : R = rectSet x₁ x₂ y₁ y₂)
    (hle : Real.exp (x₁ * Real.log x) ≤ Real.exp (x₂ * Real.log x)) :
    ‖bnd (fun s => (x:ℂ) ^ s * logDeriv f s) x₁ x₂ y₁ y₂‖
      ≤ Real.exp (x₂ * Real.log x) *
          ((2 * (x₂ - x₁) + 2 * (y₂ - y₁)) *
            ((∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) + D.Cg)) := by
  subst hRr
  have hH1c : ContinuousOn (fun t : ℝ => logDeriv f ((t:ℂ) + (y₁:ℂ)*I)) (Set.uIcc x₁ x₂) := by
    intro t ht
    exact (continuousAt_logDeriv df (D.hne _ ⟨by simpa using ht, by simpa using Set.left_mem_uIcc⟩))
      |>.comp_continuousWithinAt (cont_h y₁).continuousAt.continuousWithinAt
  have hH2c : ContinuousOn (fun t : ℝ => logDeriv f ((t:ℂ) + (y₂:ℂ)*I)) (Set.uIcc x₁ x₂) := by
    intro t ht
    exact (continuousAt_logDeriv df (D.hne _ ⟨by simpa using ht, by simpa using Set.right_mem_uIcc⟩))
      |>.comp_continuousWithinAt (cont_h y₂).continuousAt.continuousWithinAt
  have hV1c : ContinuousOn (fun t : ℝ => logDeriv f ((x₁:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂) := by
    intro t ht
    exact (continuousAt_logDeriv df (D.hne _ ⟨by simpa using Set.left_mem_uIcc, by simpa using ht⟩))
      |>.comp_continuousWithinAt (cont_v x₁).continuousAt.continuousWithinAt
  have hV2c : ContinuousOn (fun t : ℝ => logDeriv f ((x₂:ℂ) + (t:ℂ)*I)) (Set.uIcc y₁ y₂) := by
    intro t ht
    exact (continuousAt_logDeriv df (D.hne _ ⟨by simpa using Set.right_mem_uIcc, by simpa using ht⟩))
      |>.comp_continuousWithinAt (cont_v x₂).continuousAt.continuousWithinAt
  have bH1 := leg_bound df hg hR D (cont_h y₁) hx12
    (fun t ht => ⟨by simpa using ht, by simpa using Set.left_mem_uIcc⟩)
  have bH2 := leg_bound df hg hR D (cont_h y₂) hx12
    (fun t ht => ⟨by simpa using ht, by simpa using Set.right_mem_uIcc⟩)
  have bV2 := leg_bound df hg hR D (cont_v x₂) hy12
    (fun t ht => ⟨by simpa using Set.right_mem_uIcc, by simpa using ht⟩)
  have bV1 := leg_bound df hg hR D (cont_v x₁) hy12
    (fun t ht => ⟨by simpa using Set.left_mem_uIcc, by simpa using ht⟩)
  have hS : ∀ L : ℝ, (∑ ρ ∈ σ, (m ρ : ℝ) * (L * (D.delta ρ)⁻¹))
      = L * (∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) := by
    intro L
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ρ _ => by ring)
  have hA : (∫ t in x₁..x₂, ‖logDeriv f ((t:ℂ) + (y₁:ℂ)*I)‖)
      ≤ (x₂ - x₁) * ((∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) + D.Cg) := by
    rw [hS] at bH1
    nlinarith [bH1]
  have hB : (∫ t in x₁..x₂, ‖logDeriv f ((t:ℂ) + (y₂:ℂ)*I)‖)
      ≤ (x₂ - x₁) * ((∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) + D.Cg) := by
    rw [hS] at bH2
    nlinarith [bH2]
  have hC : (∫ t in y₁..y₂, ‖logDeriv f ((x₂:ℂ) + (t:ℂ)*I)‖)
      ≤ (y₂ - y₁) * ((∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) + D.Cg) := by
    rw [hS] at bV2
    nlinarith [bV2]
  have hDD : (∫ t in y₁..y₂, ‖logDeriv f ((x₁:ℂ) + (t:ℂ)*I)‖)
      ≤ (y₂ - y₁) * ((∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) + D.Cg) := by
    rw [hS] at bV1
    nlinarith [bV1]
  have hbase := norm_bnd_cpow_le_on (x := x) (G := fun z => logDeriv f z) hx hx12 hy12
    hH1c hH2c hV1c hV2c hle
  refine le_trans hbase ?_
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos (x₂ * Real.log x)))
  nlinarith [hA, hB, hC, hDD, hx12, hy12]

end BMORProp21

-- ==== BMORZeroSum.lean ====


/-!
# The zero sum is bounded by the contour estimate

`‖2πi · Σ_ρ m_ρ · x^ρ‖ ≤ x^{x₂}·(2(x₂-x₁) + 2(y₂-y₁))·(Σ_ρ m_ρ·δ_ρ⁻¹ + C_g)`.

This is the exact cross-zero identity (the boundary integral equals the weighted zero sum)
combined with the contour estimate.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

set_option maxHeartbeats 800000 in
/-- Explicit bound for the weighted zero sum. -/
theorem norm_zero_sum_le {f g : ℂ → ℂ} (df : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {x₁ x₂ y₁ y₂ : ℝ}
    (hR : IsCompact (rectSet x₁ x₂ y₁ y₂)) {σ : Finset ℂ} {m : ℂ → ℕ}
    (D : ContourData f g (rectSet x₁ x₂ y₁ y₂) σ m)
    {x : ℝ} (hx : 1 < x) (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂)
    (hle : Real.exp (x₁ * Real.log x) ≤ Real.exp (x₂ * Real.log x)) :
    ‖(2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * (x:ℂ) ^ ρ‖
      ≤ Real.exp (x₂ * Real.log x) *
          ((2 * (x₂ - x₁) + 2 * (y₂ - y₁)) *
            ((∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) + D.Cg)) := by
  have hgne : ∀ z ∈ rectSet x₁ x₂ y₁ y₂, g z ≠ 0 := by
    intro z hz h0
    have h1 : f z = 0 := by simp only [D.hfg z, h0, mul_zero]
    exact D.hne z hz h1
  have heq : bnd (fun s => (x:ℂ) ^ s * logDeriv f s) x₁ x₂ y₁ y₂
      = (2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * (x:ℂ) ^ ρ :=
    cross_zero (σ := σ) (m := m) df hg (x := (x:ℂ))
      (by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx)) : (x:ℂ) ≠ 0)
      (K := fun s => (x:ℂ) ^ s) (fun s => rfl) hR rfl D.hP D.hfg hgne hin hx12 hy12
  rw [← heq]
  exact norm_bnd_cpow_logDeriv_le_final df hg hR D hx hx12 hy12 rfl hle

end BMORProp21

-- ==== BMORIAlgebra.lean ====


/-!
# The `i`-algebra used by the contour shift

`ring` does not know `i² = -1`, so these small identities are stated once and reused.
-/

namespace BMORProp21

open Complex

/-- `-i·(i·z) = z`. -/
theorem neg_I_mul_I_mul (z : ℂ) : -I * (I * z) = z := by
  have hI : I ^ 2 = (-1 : ℂ) := Complex.I_sq
  calc -I * (I * z) = -(I ^ 2) * z := by ring
    _ = -(-1 : ℂ) * z := by rw [hI]
    _ = z := by ring

/-- `i·(-i·z) = z`. -/
theorem I_mul_neg_I_mul (z : ℂ) : I * (-I * z) = z := by
  have hI : I ^ 2 = (-1 : ℂ) := Complex.I_sq
  calc I * (-I * z) = -(I ^ 2) * z := by ring
    _ = -(-1 : ℂ) * z := by rw [hI]
    _ = z := by ring

end BMORProp21

-- ==== BMORVertDiff.lean ====


/-!
# Interface between the rectangle boundary and the two vertical lines
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology

/-- The boundary functional, written with the difference of the two vertical legs. -/
theorem bnd_eq_vert_diff (F : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) :
    bnd F x₁ x₂ y₁ y₂
      = (∫ x in x₁..x₂, F ((x:ℂ) + (y₁:ℂ)*I))
        - (∫ x in x₁..x₂, F ((x:ℂ) + (y₂:ℂ)*I))
        + I * ((∫ y in y₁..y₂, F ((x₂:ℂ) + (y:ℂ)*I))
            - (∫ y in y₁..y₂, F ((x₁:ℂ) + (y:ℂ)*I))) := by
  unfold bnd segH segV
  ring

/-- Solving for the difference of the two vertical legs. -/
theorem vert_diff_eq (F : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) :
    (∫ y in y₁..y₂, F ((x₂:ℂ) + (y:ℂ)*I)) - (∫ y in y₁..y₂, F ((x₁:ℂ) + (y:ℂ)*I))
      = -I * (bnd F x₁ x₂ y₁ y₂
          - ((∫ x in x₁..x₂, F ((x:ℂ) + (y₁:ℂ)*I))
            - (∫ x in x₁..x₂, F ((x:ℂ) + (y₂:ℂ)*I)))) := by
  have h := bnd_eq_vert_diff F x₁ x₂ y₁ y₂
  have hI : I ^ 2 = (-1 : ℂ) := Complex.I_sq
  linear_combination I * h
    + ((∫ y in y₁..y₂, F ((x₂:ℂ) + (y:ℂ)*I)) - (∫ y in y₁..y₂, F ((x₁:ℂ) + (y:ℂ)*I))) * hI

end BMORProp21

-- ==== BMORShift.lean ====


/-!
# The contour shift

`V₂ − V₁ = 2π·Σ_ρ m_ρ·x^ρ + i·(H₁ − H₂)`: the difference of the two vertical legs equals the
weighted zero sum (from the cross-zero identity) plus the horizontal contribution.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- The arithmetic of the contour shift. -/
theorem shift_arith (S U : ℂ) :
    -I * ((2 * (Real.pi : ℂ) * I) * S - U) = 2 * (Real.pi : ℂ) * S + I * U := by
  have hI : I ^ 2 = (-1 : ℂ) := Complex.I_sq
  calc -I * ((2 * (Real.pi : ℂ) * I) * S - U)
      = -I * ((2 * (Real.pi : ℂ) * I) * S) + I * U := by ring
    _ = -(2 * (Real.pi : ℂ) * (I ^ 2)) * S + I * U := by ring
    _ = -(2 * (Real.pi : ℂ) * (-1)) * S + I * U := by rw [hI]
    _ = 2 * (Real.pi : ℂ) * S + I * U := by ring


set_option maxHeartbeats 800000 in
/-- The contour shift: the difference of the two vertical legs is the zero sum plus the
horizontal contribution. -/
theorem shift_eq {f g : ℂ → ℂ} (df : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {x₁ x₂ y₁ y₂ : ℝ} (hR : IsCompact (rectSet x₁ x₂ y₁ y₂)) {σ : Finset ℂ} {m : ℂ → ℕ}
    (D : ContourData f g (rectSet x₁ x₂ y₁ y₂) σ m)
    {X : ℝ} (hX : 1 < X) (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    (∫ y in y₁..y₂, (X:ℂ) ^ ((x₂:ℂ) + (y:ℂ)*I) * logDeriv f ((x₂:ℂ) + (y:ℂ)*I))
      - (∫ y in y₁..y₂, (X:ℂ) ^ ((x₁:ℂ) + (y:ℂ)*I) * logDeriv f ((x₁:ℂ) + (y:ℂ)*I))
      = 2 * (Real.pi : ℂ) * ∑ ρ ∈ σ, (m ρ : ℂ) * (X:ℂ) ^ ρ
        + I * ((∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))
          - (∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I))) := by
  have hX0 : (X:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hX))
  have hgne : ∀ z ∈ rectSet x₁ x₂ y₁ y₂, g z ≠ 0 := by
    intro z hz h0
    have h1 : f z = 0 := by simp only [D.hfg z, h0, mul_zero]
    exact D.hne z hz h1
  have hc := cross_zero (σ := σ) (m := m) df hg (x := (X:ℂ)) hX0
    (K := fun s => (X:ℂ) ^ s) (fun s => rfl) hR rfl D.hP D.hfg hgne hin hx12 hy12
  have hv := vert_diff_eq (fun s => (X:ℂ) ^ s * logDeriv f s) x₁ x₂ y₁ y₂
  rw [hc] at hv
  rw [hv]
  exact shift_arith _ _
end BMORProp21

-- ==== BMORShiftBound.lean ====


/-!
# Bounding the difference of the two vertical legs
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- Dropping the `i` does not change the norm. -/
theorem norm_two_pi_mul_eq (S : ℂ) :
    ‖(2 * (Real.pi : ℂ)) * S‖ = ‖(2 * (Real.pi : ℂ) * I) * S‖ := by
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  simp only [norm_mul, h2, hp, hI, mul_one, one_mul]

end BMORProp21

-- ==== BMORVertBound.lean ====


/-!
# Bounding the difference of the two vertical legs

The triangle-inequality step: `‖V₂ - V₁‖ ≤ ‖2πi·Σ‖ + ‖H₁‖ + ‖H₂‖`. The individual estimates for the
zero sum and for the two horizontal legs are supplied by `norm_zero_sum_le` and
`norm_segH_cpow_le_on`.
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

set_option maxHeartbeats 800000 in
/-- Triangle-inequality bound for the difference of the two vertical legs. -/
theorem norm_vert_diff_le_triangle {f g : ℂ → ℂ} (df : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {x₁ x₂ y₁ y₂ : ℝ}
    (hR : IsCompact (rectSet x₁ x₂ y₁ y₂)) {σ : Finset ℂ} {m : ℂ → ℕ}
    (D : ContourData f g (rectSet x₁ x₂ y₁ y₂) σ m)
    {X : ℝ} (hX : 1 < X) (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) :
    ‖(∫ y in y₁..y₂, (X:ℂ) ^ ((x₂:ℂ) + (y:ℂ)*I) * logDeriv f ((x₂:ℂ) + (y:ℂ)*I))
      - (∫ y in y₁..y₂, (X:ℂ) ^ ((x₁:ℂ) + (y:ℂ)*I) * logDeriv f ((x₁:ℂ) + (y:ℂ)*I))‖
      ≤ ‖(2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * (X:ℂ) ^ ρ‖
        + ‖(∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))‖
        + ‖(∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I))‖ := by
  rw [shift_eq df hg hR D hX hx12 hy12 hin]
  have h1 : ‖(2 * (Real.pi : ℂ)) * ∑ ρ ∈ σ, (m ρ : ℂ) * (X:ℂ) ^ ρ
      + I * ((∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))
        - (∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I)))‖
      ≤ ‖(2 * (Real.pi : ℂ)) * ∑ ρ ∈ σ, (m ρ : ℂ) * (X:ℂ) ^ ρ‖
        + ‖I * ((∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))
          - (∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I)))‖ :=
    norm_add_le _ _
  have h2 : ‖(2 * (Real.pi : ℂ)) * ∑ ρ ∈ σ, (m ρ : ℂ) * (X:ℂ) ^ ρ‖
      = ‖(2 * (Real.pi : ℂ) * I) * ∑ ρ ∈ σ, (m ρ : ℂ) * (X:ℂ) ^ ρ‖ :=
    norm_two_pi_mul_eq _
  have h3 : ‖I * ((∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))
      - (∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I)))‖
      = ‖(∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))
        - (∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I))‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have h4 : ‖(∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))
      - (∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I))‖
      ≤ ‖(∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₁:ℂ)*I) * logDeriv f ((t:ℂ) + (y₁:ℂ)*I))‖
        + ‖(∫ t in x₁..x₂, (X:ℂ) ^ ((t:ℂ) + (y₂:ℂ)*I) * logDeriv f ((t:ℂ) + (y₂:ℂ)*I))‖ :=
    norm_sub_le _ _
  linarith

end BMORProp21

-- ==== BMORVertBound2.lean ====


/-!
# The final bound for the difference of the two vertical legs
-/

namespace BMORProp21

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

set_option maxHeartbeats 800000 in
/-- Explicit bound for the difference of the two vertical legs. -/
theorem norm_vert_diff_le {f g : ℂ → ℂ} (df : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {x₁ x₂ y₁ y₂ : ℝ}
    (hR : IsCompact (rectSet x₁ x₂ y₁ y₂)) {σ : Finset ℂ} {m : ℂ → ℕ}
    (D : ContourData f g (rectSet x₁ x₂ y₁ y₂) σ m)
    {X : ℝ} (hX : 1 < X) (hx12 : x₁ ≤ x₂) (hy12 : y₁ ≤ y₂)
    (hin : ∀ ρ ∈ σ, x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂)
    (hle : Real.exp (x₁ * Real.log X) ≤ Real.exp (x₂ * Real.log X)) :
    ‖(∫ y in y₁..y₂, (X:ℂ) ^ ((x₂:ℂ) + (y:ℂ)*I) * logDeriv f ((x₂:ℂ) + (y:ℂ)*I))
      - (∫ y in y₁..y₂, (X:ℂ) ^ ((x₁:ℂ) + (y:ℂ)*I) * logDeriv f ((x₁:ℂ) + (y:ℂ)*I))‖
      ≤ Real.exp (x₂ * Real.log X) *
          ((2 * (x₂ - x₁) + 2 * (y₂ - y₁)) *
            ((∑ ρ ∈ σ, (m ρ : ℝ) * (D.delta ρ)⁻¹) + D.Cg))
        + (Real.exp (x₂ * Real.log X) * (∫ t in x₁..x₂, ‖logDeriv f ((t:ℂ) + (y₁:ℂ)*I)‖)
          + Real.exp (x₂ * Real.log X) * (∫ t in x₁..x₂, ‖logDeriv f ((t:ℂ) + (y₂:ℂ)*I)‖)) := by
  have hH1 : ContinuousOn (fun t : ℝ => logDeriv f ((t:ℂ) + (y₁:ℂ)*I)) (Set.uIcc x₁ x₂) := by
    intro t ht
    exact (continuousAt_logDeriv df (D.hne _ ⟨by simpa using ht, by simpa using Set.left_mem_uIcc⟩))
      |>.comp_continuousWithinAt (cont_h y₁).continuousAt.continuousWithinAt
  have hH2 : ContinuousOn (fun t : ℝ => logDeriv f ((t:ℂ) + (y₂:ℂ)*I)) (Set.uIcc x₁ x₂) := by
    intro t ht
    exact (continuousAt_logDeriv df (D.hne _ ⟨by simpa using ht, by simpa using Set.right_mem_uIcc⟩))
      |>.comp_continuousWithinAt (cont_h y₂).continuousAt.continuousWithinAt
  have ht := norm_vert_diff_le_triangle df hg hR D hX hx12 hy12 hin
  have hz := norm_zero_sum_le df hg hR D hX hx12 hy12 hin hle
  have b1 := norm_segH_cpow_le_on (x := X) (G := fun z => logDeriv f z) (y := y₁) hX hx12 hH1
  have b2 := norm_segH_cpow_le_on (x := X) (G := fun z => logDeriv f z) (y := y₂) hX hx12 hH2
  linarith [ht, hz, b1, b2]

end BMORProp21
-- ==== end analytic infrastructure block ====


section
namespace BMORProgression
open Finset ArithmeticFunction
open scoped BigOperators Classical

noncomputable def psi (q a n : ℕ) : ℝ :=
  ∑ k ∈ (range (n+1)).filter (fun k => k % q = a % q), vonMangoldt k

noncomputable def twist {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ range (n+1), χ k * (vonMangoldt k : ℂ)

theorem decompose {q : ℕ} [NeZero q] {a : ℕ} (ha : a.Coprime q) (n : ℕ) :
    (psi q a n : ℂ) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * twist χ n := by
  classical
  have hr : psi q a n =
      ∑ k ∈ range (n+1), vonMangoldt.residueClass (a : ZMod q) k := by
    simp only [psi, sum_filter, vonMangoldt.residueClass, Set.indicator_apply,
      Set.mem_ofPred_eq, ZMod.natCast_eq_natCast_iff']
  rw [hr, Complex.ofReal_sum]
  simp_rw [vonMangoldt.residueClass_apply ((ZMod.isUnit_iff_coprime a q).mpr ha)]
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  simp only [twist, mul_sum, mul_assoc]

noncomputable def centered {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  twist χ n - if χ = 1 then (n : ℂ) else 0

theorem centered_decompose {q : ℕ} [NeZero q] {a : ℕ} (ha : a.Coprime q) (n : ℕ) :
    ((psi q a n : ℂ) - (n : ℂ)/q.totient) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * centered χ n := by
  classical
  have hu := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hi : IsUnit (a : ZMod q)⁻¹ := by
    obtain ⟨u, he⟩ := hu
    rw [← he, ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  rw [decompose ha]
  simp only [centered, mul_sub, sum_sub_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, MulChar.one_apply hi, one_mul]
  ring

theorem discrepancy_le {q : ℕ} [NeZero q] {a : ℕ} (ha : a.Coprime q) (n : ℕ) :
    |psi q a n - (n : ℝ)/q.totient| ≤
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖centered χ n‖ := by
  have eq := congrArg norm (centered_decompose ha n)
  have re : ((psi q a n : ℂ) - (n : ℂ)/q.totient) =
      ((psi q a n - (n : ℝ)/q.totient : ℝ) : ℂ) := by push_cast; rfl
  rw [re, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_inv, Complex.norm_natCast] at eq
  rw [eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_sum_le _ _).trans (sum_le_sum fun χ _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

-- Proof of the nonunit mass estimate from the project's FR-7023.
theorem nonunit_mass :
    ∀ q n : ℕ, 1 ≤ q → 1 ≤ n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q), ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card:ℝ)*Real.log n := by
  intro q n hq hn
  let K := (Finset.range (n+1)).filter (fun k => ¬k.Coprime q)
  let T := K.filter IsPrimePow
  let E (p : ℕ) := (Finset.Icc 1 (Nat.log p n))
  have repr {k : ℕ} (hk : k ∈ T) :
      k.minFac ∈ q.primeFactors ∧ ∃ a ∈ E k.minFac, k.minFac^a = k := by
    obtain ⟨hkK,hpp⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkN,hbad⟩ := Finset.mem_filter.mp hkK
    obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff k).1 hpp
    rw [Nat.pow_minFac ha.ne',hp.minFac_eq]
    have hd : p ∣ q := by
      by_contra h
      exact hbad ((hp.coprime_iff_not_dvd.2 h).pow_left a)
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩,a,Finset.mem_Icc.mpr ⟨ha,?_⟩,rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by have := Finset.mem_range.mp hkN; omega)
  have fiber (p : ℕ) (hp : p ∈ q.primeFactors) :
      (∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k) ≤ Real.log n := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hsub : T.filter (fun k => k.minFac=p) ⊆ (E p).image (fun a => p^a) := by
      intro k hk
      obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
      have hrep := (repr hkT).2
      rw [hbase] at hrep
      exact Finset.mem_image.mpr hrep
    have hc : (T.filter (fun k => k.minFac=p)).card ≤ Nat.log p n := by
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      simpa [E,Nat.card_Icc] using this
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    calc
      _ = ∑ _k ∈ T.filter (fun k => k.minFac=p), Real.log (p:ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
        rw [ArithmeticFunction.vonMangoldt_apply,ite_eq_left (Finset.mem_filter.mp hkT).2,hbase]
      _ ≤ (Nat.log p n:ℝ)*Real.log p := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlog
      _ = Real.log ((p:ℝ)^(Nat.log p n)) := (Real.log_pow _ _).symm
      _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast pow_pos hpprime.pos _)
        (by exact_mod_cast Nat.pow_log_le_self p (by omega))
  change (∑ k ∈ K, ArithmeticFunction.vonMangoldt k) ≤ _
  calc
    _ = ∑ k ∈ T, ArithmeticFunction.vonMangoldt k := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun k hk hout =>
        ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (fun h => hout (Finset.mem_filter.mpr ⟨hk,h⟩)))
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k :=
      (Finset.sum_fiberwise_of_maps_to (fun k hk => (repr hk).1) _).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log n := Finset.sum_le_sum fiber
    _ = _ := by simp

theorem primitive_correction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖twist χ n - twist χ.primitiveCharacter n‖ ≤
      (q.primeFactors.card : ℝ) * Real.log n := by
  classical
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  unfold twist
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (le_trans ?_ (nonunit_mass q n (Nat.pos_of_ne_zero (NeZero.ne q)) hn))
  rw [sum_filter]
  apply sum_le_sum
  intro k _
  by_cases hk : k.Coprime q
  · have h := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hk)
    push_cast at h
    simp [hk,h]
  · have hz := χ.map_nonunit (mt (ZMod.isUnit_iff_coprime k q).mp hk)
    simp only [hz, zero_mul, zero_sub, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, ite_eq_left hk]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.primitiveCharacter.norm_le_one _)

theorem log_sqrt_budget {n : ℕ} (hn : 8000000000 ≤ n) :
    2048 * Real.log n ≤ Real.sqrt n := by
  have hn' : (8000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hl := Real.log_pos (show (1 : ℝ) < n by linarith)
  have hs := Real.sq_sqrt hp.le
  have hroot : (65536 : ℝ) ≤ Real.sqrt n := by
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hlog2 := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hbase : Real.log 65536 ≤ 16 := by
    rw [show (65536:ℝ)=2^16 by norm_num, Real.log_pow]
    norm_num
    linarith only [hlog2]
  have hdiv := Real.log_le_sub_one_of_pos
    (show 0 < Real.sqrt (n : ℝ) / 65536 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hp.le] at hdiv
  linarith

/-- The cost of passing to primitive characters fits in one hundredth of the target. -/
theorem small_modulus_cost {q n : ℕ} (hq : q ≤ 105) (hn : 8000000000 ≤ n) :
    (q.primeFactors.card : ℝ) * Real.log n ≤ (n : ℝ) / (84000 * Real.log n) := by
  have cardTable : ∀ k : Fin 106, (k : ℕ).primeFactors.card ≤ 3 := by decide +kernel
  have hc : (q.primeFactors.card : ℝ) ≤ 3 := by
    exact_mod_cast cardTable ⟨q, by omega⟩
  have hs := Real.sq_sqrt (n.cast_nonneg : 0 ≤ (n:ℝ))
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsmall := log_sqrt_budget hn
  have hsquare := mul_self_le_mul_self (by positivity) hsmall
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ (3 * Real.log n) * (84000 * Real.log n) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg (Real.log (n:ℝ))]

noncomputable def primitiveCentered {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  twist χ.primitiveCharacter n - if χ = 1 then (n : ℂ) else 0

/-- Sufficient analytic input, expressed solely through primitive twists. -/
theorem of_primitive_budget {q a n : ℕ} [NeZero q] (hq : 3 ≤ q) (hq' : q ≤ 105)
    (ha : a.Coprime q) (hn : 8000000000 ≤ n)
    (budget : ∑ χ : DirichletCharacter ℂ q, ‖primitiveCentered χ n‖ ≤
      (q.totient : ℝ) * (99 * n / (84000 * Real.log n))) :
    |psi q a n - (n : ℝ)/q.totient| ≤ (n : ℝ)/(840 * Real.log n) := by
  classical
  have ht : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hsingle (χ : DirichletCharacter ℂ q) :
      ‖centered χ n‖ ≤ ‖primitiveCentered χ n‖ + (n:ℝ)/(84000 * Real.log n) := by
    have hsplit : centered χ n = primitiveCentered χ n + (twist χ n - twist χ.primitiveCharacter n) := by
      unfold centered primitiveCentered
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((primitive_correction χ (by omega : 1 ≤ n)).trans
      (small_modulus_cost hq' hn)))
  refine (discrepancy_le ha n).trans ?_
  have hsum := sum_le_sum (s := (univ : Finset (DirichletCharacter ℂ q))) (fun χ _ => hsingle χ)
  rw [sum_add_distrib] at hsum
  simp only [sum_const,card_univ,hcard,nsmul_eq_mul] at hsum
  have h := hsum.trans (add_le_add budget le_rfl)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp [ht.ne', hl.ne'] <;> ring

/-- A square-root certificate at the same endpoint implies the required finite-range error. -/
theorem of_sqrt_certificate {q a n : ℕ} (hn : 8000000000 ≤ n)
    (bound : |psi q a n - (n:ℝ)/q.totient| ≤ 2 * Real.sqrt n) :
    |psi q a n - (n:ℝ)/q.totient| ≤ (n:ℝ)/(840 * Real.log n) := by
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have small : 1680 * Real.log (n:ℝ) ≤ Real.sqrt n := by linarith [log_sqrt_budget hn]
  apply bound.trans
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = Real.sqrt n * (1680 * Real.log n) := by ring
    _ ≤ Real.sqrt n * Real.sqrt n := by gcongr
    _ = n := Real.mul_self_sqrt (by positivity)

end BMORProgression

namespace BMORProgression
open Finset ArithmeticFunction

/-- First Riesz mean at an integer. The summand at the upper endpoint has weight zero. -/
noncomputable def riesz (q a n : ℕ) : ℝ :=
  ∑ k ∈ range n, ((n:ℝ)-k) * (if k % q = a % q then vonMangoldt k else 0)

theorem riesz_succ (q a n : ℕ) : riesz q a (n+1) = riesz q a n + psi q a n := by
  classical
  unfold riesz psi
  rw [sum_filter, sum_range_succ, sum_range_succ (f := fun k => if k % q = a % q then vonMangoldt k else 0)]
  push_cast
  simp only [show ∀ k : ℕ, (n:ℝ)+1-k = ((n:ℝ)-k)+1 by intro; ring, add_mul,
    one_mul,sum_add_distrib,sub_self,zero_add]
  ring

theorem psi_mono (q a : ℕ) : Monotone (psi q a) := by
  intro m n h
  unfold psi
  apply sum_le_sum_of_subset_of_nonneg
  · apply filter_subset_filter
    exact range_mono (by omega)
  · intro i _ _
    exact vonMangoldt_nonneg

theorem riesz_increment (q a l h : ℕ) :
    riesz q a (l+h) - riesz q a l = ∑ j ∈ range h, psi q a (l+j) := by
  induction h with
  | zero => simp
  | succ h ih => rw [Nat.add_succ,riesz_succ,sum_range_succ,←ih]; ring

/-- Upper and lower finite differences enclose the unsmoothed sum; no zero estimates enter here. -/
theorem riesz_bracket (q a l h : ℕ) :
    (h:ℝ)*psi q a l ≤ riesz q a (l+h)-riesz q a l ∧
    riesz q a (l+h)-riesz q a l ≤ (h:ℝ)*psi q a (l+h) := by
  rw [riesz_increment]
  constructor
  · simpa only [sum_const,card_range,nsmul_eq_mul] using
      (sum_le_sum (s := range h) (f := fun _ => psi q a l) (g := fun j => psi q a (l+j))
        (fun j _ => psi_mono q a (Nat.le_add_right l j)))
  · simpa only [sum_const,card_range,nsmul_eq_mul] using
      (sum_le_sum (s := range h) (f := fun j => psi q a (l+j)) (g := fun _ => psi q a (l+h))
        (fun j hj => psi_mono q a (Nat.add_le_add_left (mem_range.mp hj).le l)))

noncomputable def rieszError (q a n : ℕ) : ℝ :=
  riesz q a n - ((n:ℝ)*(n-1)/2)/q.totient

theorem smooth_endpoints (q a l h : ℕ) :
    (h:ℝ)*(psi q a l - (l:ℝ)/q.totient) ≤
      rieszError q a (l+h) - rieszError q a l + ((h:ℝ)*(h-1)/2)/q.totient ∧
    rieszError q a (l+h) - rieszError q a l - ((h:ℝ)*(h+1)/2)/q.totient ≤
      (h:ℝ)*(psi q a (l+h) - ((l:ℝ)+h)/q.totient) := by
  obtain ⟨lo,hi⟩ := riesz_bracket q a l h
  unfold rieszError
  push_cast
  constructor
  · linear_combination lo
  · linear_combination hi

/-- A pair of one-sided estimates on the smoothed explicit formula suffices at the center. -/
theorem of_smoothed_increments (q a l h : ℕ) (hh : 0 < h) (E : ℝ)
    (upper : rieszError q a (l+h+h) - rieszError q a (l+h) ≤
      (h:ℝ)*E - ((h:ℝ)*(h-1)/2)/q.totient)
    (lower : -((h:ℝ)*E) + ((h:ℝ)*(h+1)/2)/q.totient ≤
      rieszError q a (l+h) - rieszError q a l) :
    |psi q a (l+h) - (((l+h:ℕ):ℝ)/q.totient)| ≤ E := by
  have hp : (0:ℝ)<h := by exact_mod_cast hh
  have left := (smooth_endpoints q a l h).2
  have right := (smooth_endpoints q a (l+h) h).1
  push_cast at right ⊢
  apply abs_le.mpr
  constructor
  · apply le_of_mul_le_mul_left (a := (h:ℝ)) _ hp
    linear_combination left + lower
  · apply le_of_mul_le_mul_left (a := (h:ℝ)) _ hp
    linear_combination upper + right

end BMORProgression

namespace BMORProgression
open Set MeasureTheory intervalIntegral
open scoped Interval

noncomputable def triangle (x : ℝ) : ℂ :=
  (Ioc (0:ℝ) 1).indicator (fun t : ℝ => 1-(t:ℂ)) x

private theorem triangle_integrand (s : ℂ) :
    (fun x : ℝ => (x:ℂ)^(s-1) • triangle x) =
      (Ioc (0:ℝ) 1).indicator (fun x : ℝ => (x:ℂ)^(s-1) - (x:ℂ)^s) := by
  funext x
  by_cases hx : x ∈ Ioc (0:ℝ) 1
  · simp only [triangle, indicator_of_mem hx, smul_eq_mul, mul_sub, mul_one]
    have hn : (x:ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    congr 1
    simpa using (Complex.cpow_add (s-1) 1 hn).symm
  · simp [triangle,indicator_of_notMem hx]

theorem mellin_triangle {s : ℂ} (hs : 0<s.re) :
    mellin triangle s = 1/(s*(s+1)) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s+1 ≠ 0 := by
    intro h
    have eq := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at eq
    linarith
  have h0 : -1 < (s-1).re := by simp; linarith
  have h1 : -1 < s.re := by linarith
  rw [mellin,triangle_integrand,setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (show Ioc (0:ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1),
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      intervalIntegral.integral_sub (intervalIntegrable_cpow' h0) (intervalIntegrable_cpow' h1),
      integral_cpow (Or.inl h0),integral_cpow (Or.inl h1)]
  simp only [Complex.ofReal_one,Complex.ofReal_zero,sub_add_cancel,Complex.one_cpow,
    Complex.zero_cpow hs0,Complex.zero_cpow hs1,sub_zero]
  field_simp
  ring

theorem triangle_convergent {s : ℂ} (hs : 0<s.re) : MellinConvergent triangle s := by
  rw [MellinConvergent,triangle_integrand]
  apply Integrable.integrableOn
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)]
  exact (intervalIntegrable_cpow' (by simp; linarith : -1 < (s-1).re)).sub
    (intervalIntegrable_cpow' (by linarith : -1 < s.re))

theorem triangle_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt triangle x := by
  have cont : Continuous (fun y : ℝ => ((max (1-y) 0 : ℝ) : ℂ)) := by fun_prop
  apply cont.continuousAt.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx] with y hy
  by_cases h : y ≤ 1
  · simp [triangle, Set.mem_Ioc, hy, h]
  · simp [triangle, Set.mem_Ioc, h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

noncomputable def perronWeight (s : ℂ) : ℂ := 1/(s*(s+1))

set_option maxHeartbeats 2000000 in
theorem perron_vertical : Complex.VerticalIntegrable perronWeight 2 := by
  unfold Complex.VerticalIntegrable
  have nonzero (y : ℝ) : ((2:ℂ)+y*Complex.I)*((2:ℂ)+y*Complex.I+1) ≠ 0 := by
    apply mul_ne_zero <;> intro h <;> apply_fun Complex.re at h <;> norm_num at h
  apply integrable_inv_one_add_sq.mono'
  · apply Continuous.aestronglyMeasurable
    unfold perronWeight
    have line : Continuous (fun y : ℝ => (2:ℂ) + (y:ℂ)*Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact Continuous.div (f := fun _ : ℝ => (1:ℂ))
      (g := fun y : ℝ => (2+(y:ℂ)*Complex.I)*(2+(y:ℂ)*Complex.I+1))
      continuous_const (line.mul (line.add continuous_const)) nonzero
  · filter_upwards with y
    let z : ℂ := 2 + y*Complex.I
    have sq0 : ‖z‖^2 = 4+y^2 := by simp [z,Complex.sq_norm,Complex.normSq_apply]; ring
    have sq1 : ‖z+1‖^2 = 9+y^2 := by simp [z,Complex.sq_norm,Complex.normSq_apply]; ring
    have ord : ‖z‖ ≤ ‖z+1‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [sq0,sq1]; linarith)
    have low : 1+y^2 ≤ ‖z‖*‖z+1‖ := by
      have p := mul_le_mul_of_nonneg_left ord (norm_nonneg z)
      nlinarith only [p,sq0]
    change ‖1/(z*(z+1))‖ ≤ _
    rw [norm_div,norm_one,norm_mul,←one_div]
    exact one_div_le_one_div_of_le (by positivity) low

theorem perron_triangle {x : ℝ} (hx : 0<x) : mellinInv 2 perronWeight x = triangle x := by
  have onLine (y : ℝ) : mellin triangle ((2:ℂ)+y*Complex.I) = perronWeight ((2:ℂ)+y*Complex.I) :=
    mellin_triangle (by norm_num)
  have vert : Complex.VerticalIntegrable (mellin triangle) 2 := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_ofNat,onLine] using perron_vertical
  have inv := mellinInv_mellin_eq 2 triangle hx (triangle_convergent (by norm_num)) vert
    (triangle_continuousAt hx)
  simpa only [mellinInv,Complex.ofReal_ofNat,onLine] using inv

end BMORProgression

namespace BMORProgression
open Complex MeasureTheory Finset

private def lineTwo (y : ℝ) : ℂ := 2 + y * I

private theorem cont_lineTwo : Continuous lineTwo :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

private theorem lineTwo_re (y : ℝ) : (lineTwo y).re=2 := by simp [lineTwo]

private theorem cont_weight : Continuous (fun y : ℝ => perronWeight (lineTwo y)) := by
  have nz (y : ℝ) : lineTwo y * (lineTwo y+1) ≠ 0 := by
    apply mul_ne_zero <;> intro h <;> apply_fun Complex.re at h <;> norm_num [lineTwo_re] at h
  exact Continuous.div (f := fun _ : ℝ => (1:ℂ)) (g := fun y : ℝ => lineTwo y * (lineTwo y+1))
    continuous_const (cont_lineTwo.mul (cont_lineTwo.add continuous_const)) nz

private noncomputable def atom (f : ℕ → ℂ) (x : ℝ) (k : ℕ) (y : ℝ) : ℂ :=
  (x:ℂ)^(-lineTwo y) * LSeries.term f (lineTwo y) k * perronWeight (lineTwo y)

private theorem cont_atom (f : ℕ → ℂ) {x : ℝ} (hx : 0<x) (k : ℕ) :
    Continuous (atom f x k) := by
  have cp (b : ℂ) (hb : b ≠ 0) : Continuous (fun z : ℂ => b^z) :=
    continuous_iff_continuousAt.mpr fun _ => continuousAt_const_cpow hb
  unfold atom
  apply Continuous.mul _ cont_weight
  apply Continuous.mul ((cp x (by exact_mod_cast hx.ne')).comp cont_lineTwo.neg)
  by_cases hk : k=0
  · simp [hk,continuous_const]
  · simp only [LSeries.term_of_ne_zero hk,div_eq_mul_inv,←Complex.cpow_neg]
    exact continuous_const.mul ((cp k (by exact_mod_cast hk)).comp cont_lineTwo.neg)

private theorem atom_norm (f : ℕ → ℂ) {x : ℝ} (hx : 0<x) (k : ℕ) (y : ℝ) :
    ‖atom f x k y‖ = (x^(-2:ℝ) * ‖LSeries.term f 2 k‖) * ‖perronWeight (lineTwo y)‖ := by
  simp [atom, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    LSeries.norm_term_eq, lineTwo_re]

theorem perron_series {f : ℕ → ℂ} (hf : f 0=0) (hs : LSeriesSummable f 2)
    {x : ℝ} (hx : 0<x) :
    mellinInv 2 (fun s => LSeries f s * perronWeight s) x =
      ∑' k : ℕ, f k * triangle (k*x) := by
  have hw : Integrable (fun y : ℝ => perronWeight (lineTwo y)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_ofNat,lineTwo] using perron_vertical
  have hi (k : ℕ) : Integrable (atom f x k) :=
    (hw.norm.const_mul (x^(-2:ℝ)*‖LSeries.term f 2 k‖)).mono'
      (cont_atom f hx k).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (atom_norm f hx k y).le)
  have hsum : Summable (fun k : ℕ => ∫ y : ℝ, ‖atom f x k y‖) := by
    simp_rw [atom_norm f hx,integral_const_mul]
    exact (hs.norm.mul_left _).mul_right _
  have exchanged := hasSum_integral_of_summable_integral_norm hi hsum
  have each (k : ℕ) :
      (1/(2*Real.pi):ℝ) • (∫ y : ℝ, atom f x k y) = f k * triangle (k*x) := by
    by_cases hk : k=0
    · simp [hk,hf,atom]
    have hk' : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [← perron_triangle (mul_pos hk' hx),mellinInv]
    have val (y : ℝ) : atom f x k y =
        f k * (((((k:ℝ)*x : ℝ):ℂ)^(-lineTwo y)) * perronWeight (lineTwo y)) := by
      rw [atom,LSeries.term_def₀ hf,Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hk'.le hx.le]
      push_cast
      ring
    simp_rw [val]
    rw [integral_const_mul]
    simp only [Complex.ofReal_ofNat,smul_eq_mul,lineTwo,Complex.real_smul]
    ring
  have lineSum (y : ℝ) : ∑' k : ℕ, atom f x k y =
      (x:ℂ)^(-lineTwo y) * (LSeries f (lineTwo y)*perronWeight (lineTwo y)) := by
    simp only [atom,tsum_mul_left,tsum_mul_right,LSeries,mul_assoc]
  have res := exchanged.const_smul (1/(2*Real.pi):ℝ)
  simp_rw [each] at res
  rw [res.tsum_eq]
  simp only [mellinInv,Complex.ofReal_ofNat,smul_eq_mul,lineSum,lineTwo]

end BMORProgression

namespace BMORProgression
open Set Finset Complex ArithmeticFunction DirichletCharacter

theorem riesz_perron (q a n : ℕ) (hn : 0<n) :
    (riesz q a n : ℂ) = (n:ℂ) * mellinInv 2
      (fun s => LSeries (fun k : ℕ => (vonMangoldt.residueClass (a : ZMod q) k : ℂ)) s * perronWeight s) (1/(n:ℝ)) := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  have hz : (fun k : ℕ => (vonMangoldt.residueClass (a : ZMod q) k : ℂ)) 0=0 := by simp
  have hs : LSeriesSummable (fun k : ℕ => (vonMangoldt.residueClass (a : ZMod q) k : ℂ)) 2 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one (a : ZMod q)).trans_lt (by
        rw [← EReal.coe_one,EReal.coe_lt_coe_iff]; norm_num))
  rw [perron_series hz hs (by positivity)]
  have vanish (k : ℕ) (hk : k ∉ range n) :
      (vonMangoldt.residueClass (a:ZMod q) k : ℂ) * triangle ((k:ℝ)*(1/n)) = 0 := by
    have hkn : n ≤ k := Nat.le_of_not_gt (fun h => hk (mem_range.mpr h))
    have hy : 1 ≤ (k:ℝ)*(1/n) := by rw [mul_one_div,le_div_iff₀ hp]; simpa using (Nat.cast_le.mpr hkn : (n:ℝ) ≤ k)
    by_cases he : (k:ℝ)*(1/n)=1
    · rw [he]; norm_num [triangle]
    · have hout : (k:ℝ)*(1/n) ∉ Ioc (0:ℝ) 1 := fun h => he (h.2.antisymm hy)
      rw [triangle,indicator_of_notMem hout,mul_zero]
  rw [tsum_eq_sum vanish, mul_sum,riesz,Complex.ofReal_sum]
  apply sum_congr rfl
  intro k hk
  by_cases hk0 : k=0
  · simp [hk0]
  have hkpos : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hin : (k:ℝ)*(1/n) ∈ Ioc (0:ℝ) 1 := by
    constructor
    · positivity
    · rw [mul_one_div,div_le_iff₀ hp,one_mul]
      exact_mod_cast (mem_range.mp hk).le
  simp only [triangle,indicator_of_mem hin,vonMangoldt.residueClass,
    Set.indicator_apply,Set.mem_ofPred_eq,ZMod.natCast_eq_natCast_iff']
  have nc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  split_ifs <;> push_cast <;> field_simp [nc]

noncomputable def logarithmicSum (q a : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ (a:ZMod q)⁻¹ *
    (deriv (LFunction χ) s / LFunction χ s)

theorem riesz_logarithmic_integral {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n) :
    (riesz q a n : ℂ) = (n:ℂ) * mellinInv 2
      (fun s => logarithmicSum q a s * perronWeight s) (1/(n:ℝ)) := by
  rw [riesz_perron q a n hn]
  have eq (y : ℝ) := vonMangoldt.LSeries_residueClass_eq ((ZMod.isUnit_iff_coprime a q).mpr ha)
    (s := (2:ℂ)+y*I) (by norm_num)
  simp only [mellinInv,Complex.ofReal_ofNat,eq,logarithmicSum]

end BMORProgression

namespace BMORProgression
open Set Finset Complex MeasureTheory ArithmeticFunction

private theorem threeHalvesTail :
    ∑' j : ℕ, (((j+2 : ℕ):ℝ)^(-3/2:ℝ)) ≤ 2 := by
  let g : ℝ → ℝ := fun x => x^(-3/2:ℝ)
  have ha : AntitoneOn g (Ici 1) := fun x hx y _ h =>
    Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) h (by norm_num)
  have hi : IntegrableOn g (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h := AntitoneOn.tsum_comp_add_le_integral (f := g) 1 (by simpa using ha)
    (by simpa using hi) (fun t ht => Real.rpow_nonneg (le_trans (by norm_num : (0:ℝ)≤↑(1:ℕ)) (le_of_lt (show (↑(1:ℕ):ℝ)<t from ht))) _)
  change (∑' j : ℕ, (((j+2:ℕ):ℝ)^(-3/2:ℝ))) ≤ ∫ t in Ioi (↑(1:ℕ):ℝ), t^(-3/2:ℝ) at h
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)] at h
  norm_num only [Nat.cast_one, Real.one_rpow] at h
  convert h using 1 <;> norm_num

private theorem log_over_square {k : ℝ} (hk : 0<k) :
    Real.log k / k^2 ≤ 2*k^(-3/2:ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hk)
  rw [Real.log_sqrt hk.le] at h
  rw [div_le_iff₀ (by positivity), mul_assoc, ←Real.rpow_natCast k 2,
    ←Real.rpow_add hk]
  norm_num
  rw [←Real.sqrt_eq_rpow]
  linarith

theorem progression_series_bound (q a : ℕ) (y : ℝ) :
    ‖LSeries (fun k : ℕ => (vonMangoldt.residueClass (a : ZMod q) k : ℂ)) (2+y*I)‖ ≤ 4 := by
  let f : ℕ → ℂ := fun k => vonMangoldt.residueClass (a:ZMod q) k
  let z : ℂ := 2+y*I
  have sr : z.re=2 := by simp [z]
  have hs : LSeriesSummable f z := LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one (a : ZMod q)).trans_lt
      (by rw [sr,←EReal.coe_one,EReal.coe_lt_coe_iff]; norm_num))
  change ‖∑' k, LSeries.term f z k‖ ≤ 4
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  rw [← hs.norm.sum_add_tsum_nat_add 2]
  have zeroPrefix : (∑ j ∈ range 2, ‖LSeries.term f z j‖) = 0 := by
    simp [sum_range_succ,LSeries.term,f,vonMangoldt.residueClass,Set.indicator_apply]
  rw [zeroPrefix,zero_add]
  have sp : Summable (fun j : ℕ => (((j+2:ℕ):ℝ)^(-3/2:ℝ))) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  calc
    _ ≤ ∑' j : ℕ, 2*(((j+2:ℕ):ℝ)^(-3/2:ℝ)) := by
      apply ((summable_nat_add_iff 2).mpr hs.norm).tsum_le_tsum _ (sp.mul_left 2)
      intro j
      let k := j+2
      have hk : 0<k := by dsimp [k]; omega
      have hp : (0:ℝ)<k := by exact_mod_cast hk
      change ‖LSeries.term f z k‖ ≤ 2*(k:ℝ)^(-3/2:ℝ)
      rw [LSeries.norm_term_eq,ite_eq_right hk.ne',sr]
      simp only [Real.rpow_ofNat]
      apply (div_le_div_of_nonneg_right _ (sq_nonneg _)).trans (log_over_square hp)
      simpa [f, Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg (vonMangoldt.residueClass_nonneg _ _)]
        using ((vonMangoldt.residueClass_le (a:ZMod q) k).trans vonMangoldt_le_log)
    _ = 2 * ∑' j : ℕ, (((j+2:ℕ):ℝ)^(-3/2:ℝ)) := by rw [tsum_mul_left]
    _ ≤ 4 := by linarith [threeHalvesTail]

end BMORProgression

namespace BMORProgression
open Set MeasureTheory Complex ArithmeticFunction

private theorem truncate_symmetric {F : ℝ → ℂ} (hi : Integrable F)
    {C T : ℝ} (hT : 0<T) (h : ∀ y : ℝ, y ≠ 0 → ‖F y‖ ≤ C / y^2) :
    ‖(∫ y : ℝ, F y) - ∫ y in Ioc (-T) T, F y‖ ≤ 2*C/T := by
  have estimate (f : ℝ → ℂ) (hf : ∀ y ∈ Ioi T, ‖f y‖ ≤ C / y^2) :
      ‖∫ y in Ioi T, f y‖ ≤ C/T := by
    have ir := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hT
    have eq (y : ℝ) : C/y^2 = C*y^(-2:ℝ) := by
      rw [div_eq_mul_inv,show (-2:ℝ)=((-2:ℤ):ℝ) by norm_num,Real.rpow_intCast]
      simp
    calc
      _ ≤ ∫ y in Ioi T, C*y^(-2:ℝ) := by
        apply norm_integral_le_of_norm_le (ir.const_mul C)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        simpa only [←eq] using hf y hy
      _ = C/T := by
        rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hT]
        norm_num [div_eq_mul_inv,Real.rpow_neg_one]
  have hr := estimate F (fun y hy => h y (ne_of_gt (lt_trans hT hy)))
  have hl := estimate (fun y => F (-y)) (by
    intro y hy
    simpa only [neg_sq] using h (-y) (neg_ne_zero.mpr (ne_of_gt (lt_trans hT hy))))
  rw [integral_comp_neg_Ioi] at hl
  have split := intervalIntegral.integral_Iic_add_Ioi (b := -T) hi.integrableOn hi.integrableOn
  have decomp := setIntegral_union (f := F)
    (Iic_disjoint_Ioi (le_refl T) |>.mono_left (show Ioc (-T) T ⊆ Iic T from fun _ hx => hx.2))
    measurableSet_Ioi hi.integrableOn hi.integrableOn
  rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at decomp
  rw [←split, decomp, show ∀ a b c : ℂ, a+(b+c)-b=a+c by intros; ring]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

noncomputable def perronIntegrand (q a n : ℕ) (y : ℝ) : ℂ :=
  let z : ℂ := 2+y*I
  (((1/(n:ℝ)):ℝ):ℂ)^(-z) *
    (LSeries (fun k : ℕ => (vonMangoldt.residueClass (a:ZMod q) k : ℂ)) z * perronWeight z)

private theorem perronIntegrand_majorant (q a n : ℕ) (hn : 0<n) (y : ℝ) :
    ‖perronIntegrand q a n y‖ ≤ 4*(n:ℝ)^2*‖perronWeight (2+y*I)‖ := by
  let z : ℂ := 2+y*I
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hnrm : ‖(((1/(n:ℝ)):ℝ):ℂ)^(-z)‖ = (n:ℝ)^2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [z]
  unfold perronIntegrand
  simp only [norm_mul]
  rw [hnrm,←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (progression_series_bound q a y) (sq_nonneg (n:ℝ))

set_option maxHeartbeats 1200000 in
theorem perronIntegrand_integrable (q a n : ℕ) (hn : 0<n) :
    Integrable (perronIntegrand q a n) := by
  let f : ℕ → ℂ := fun k => vonMangoldt.residueClass (a:ZMod q) k
  let z : ℝ → ℂ := fun y => 2+y*I
  have cz : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have cw : Integrable (fun y => perronWeight (z y)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_ofNat,z] using perron_vertical
  apply (cw.norm.const_mul (4*(n:ℝ)^2)).mono' _ (Filter.Eventually.of_forall (perronIntegrand_majorant q a n hn))
  apply Continuous.aestronglyMeasurable
  apply continuous_iff_continuousAt.mpr
  intro y
  have hRe : LSeries.abscissaOfAbsConv f < (z y).re :=
    (vonMangoldt.abscissaOfAbsConv_residueClass_le_one (a:ZMod q)).trans_lt (by
      rw [show (z y).re = 2 by simp [z]]
      rw [←EReal.coe_one,EReal.coe_lt_coe_iff]; norm_num)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h0 : (((1/(n:ℝ)):ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by positivity : 0<1/(n:ℝ)))
  have nz : z y * (z y+1) ≠ 0 := by
    apply mul_ne_zero <;> intro e <;> apply_fun Complex.re at e <;> norm_num [z] at e
  change ContinuousAt (fun t : ℝ => (((1/(n:ℝ)):ℝ):ℂ)^(-z t) *
    (LSeries f (z t) * ((1:ℂ)/(z t*(z t+1))))) y
  exact ((continuousAt_const_cpow h0).comp cz.continuousAt.neg).mul
    (((LSeries_hasDerivAt hRe).continuousAt.comp cz.continuousAt).mul
      (continuousAt_const.div (cz.continuousAt.mul (cz.continuousAt.add continuousAt_const)) nz))

theorem riesz_truncation (q a n : ℕ) (hn : 0<n) {T : ℝ} (hT : 0<T) :
    ‖(riesz q a n : ℂ) - (n:ℂ) * ((1/(2*Real.pi):ℝ) •
      (∫ y in Ioc (-T) T, perronIntegrand q a n y))‖ ≤ 4*(n:ℝ)^3/(Real.pi*T) := by
  have ht := truncate_symmetric (perronIntegrand_integrable q a n hn) (C := 4*(n:ℝ)^2) hT (by
    intro y hy
    let z : ℂ := 2+y*I
    have hz : |y| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
    have hzp : |y| ≤ ‖z+1‖ := by simpa [z] using Complex.abs_im_le_norm (z+1)
    have low : y^2 ≤ ‖z‖*‖z+1‖ := by simpa [←sq] using mul_le_mul hz hzp (abs_nonneg y) (norm_nonneg z)
    have hw : ‖perronWeight z‖ ≤ 1/y^2 := by
      rw [perronWeight,norm_div,norm_one,norm_mul]
      exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hy) low
    exact (perronIntegrand_majorant q a n hn y).trans (by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hw (by positivity : 0≤4*(n:ℝ)^2)))
  rw [riesz_perron q a n hn]
  change ‖(n:ℂ)*((1/(2*Real.pi):ℝ) • (∫ y : ℝ, perronIntegrand q a n y)) - _‖ ≤ _
  rw [←mul_sub,←smul_sub,norm_mul,norm_smul]
  simp only [Complex.norm_natCast, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ)<1/(2*Real.pi))]
  calc
    _ ≤ (n:ℝ) * ((1/(2*Real.pi))* (2*(4*(n:ℝ)^2)/T)) := by gcongr
    _ = _ := by ring

end BMORProgression

namespace BMORProgression
open Set Complex MeasureTheory ArithmeticFunction

noncomputable def poleProfile (x : ℝ) : ℂ :=
  (((x:ℂ)^(-1:ℂ) • triangle x) - triangle x)/2

theorem poleProfile_transform {s : ℂ} (hs : 1<s.re) :
    HasMellin poleProfile s (perronWeight s/(s-1)) := by
  have hs' : 0<(s+(-1)).re := by simp; linarith
  have h0 := triangle_convergent (s := s) (by linarith)
  have h1 := (MellinConvergent.cpow_smul (f := triangle) (s := s) (a := -1)).mpr (triangle_convergent hs')
  obtain ⟨hc,he⟩ := hasMellin_sub h1 h0
  refine ⟨hc.div_const 2, ?_⟩
  unfold poleProfile
  rw [mellin_div_const,he,mellin_cpow_smul,mellin_triangle hs',mellin_triangle (by linarith : 0<s.re)]
  have n (j : ℂ) (hj : j.re ≠ 0) : j ≠ 0 := fun eq => hj (by simp [eq])
  have n0 := n s (by linarith)
  have nm := n (s-1) (by simp; linarith)
  have np := n (s+1) (by simp; linarith)
  simp only [←sub_eq_add_neg,sub_add_cancel,perronWeight]
  field_simp
  <;> ring

private theorem poleProfile_cont {x : ℝ} (hx : 0<x) : ContinuousAt poleProfile x := by
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold poleProfile
  simp only [Complex.cpow_neg_one,smul_eq_mul]
  exact (((Complex.continuous_ofReal.continuousAt.inv₀ hx').mul (triangle_continuousAt hx)).sub
    (triangle_continuousAt hx)).div_const 2

theorem poleWeight_vertical :
    Complex.VerticalIntegrable (fun s => perronWeight s/(s-1)) 2 := by
  let z : ℝ → ℂ := fun y => 2+y*I
  have hw : Integrable (fun y => perronWeight (z y)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_ofNat,z] using perron_vertical
  have cz : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have low (y : ℝ) : 1 ≤ ‖z y-1‖ := by
    have h := Complex.abs_re_le_norm (z y-1)
    norm_num [z] at h ⊢
    exact h
  have nzero (y : ℝ) : z y-1 ≠ 0 := fun e => by have := low y; norm_num [e] at this
  change Integrable (fun y => perronWeight (z y)/(z y-1))
  apply hw.norm.mono'
  · have cm : Continuous (fun y : ℝ => (z y-1)⁻¹) := (cz.sub continuous_const).inv₀ nzero
    have eq : (fun y : ℝ => perronWeight (z y)/(z y-1)) =
        (fun y : ℝ => perronWeight (z y)) * (fun y : ℝ => (z y-1)⁻¹) :=
      funext fun y => div_eq_mul_inv _ _
    rw [eq]
    exact hw.aestronglyMeasurable.mul cm.aestronglyMeasurable
  · filter_upwards with y
    change ‖perronWeight (z y)/(z y-1)‖ ≤ _
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (low y)

theorem pole_inverse {x : ℝ} (hx : 0<x) :
    mellinInv 2 (fun s => perronWeight s/(s-1)) x = poleProfile x := by
  have onLine (y : ℝ) : mellin poleProfile ((2:ℂ)+y*I) = _ :=
    (poleProfile_transform (s := (2:ℂ)+y*I) (by norm_num)).2
  have vert : Complex.VerticalIntegrable (mellin poleProfile) 2 := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_ofNat,onLine] using poleWeight_vertical
  have inv := mellinInv_mellin_eq 2 poleProfile hx (poleProfile_transform (by norm_num)).1 vert
    (poleProfile_cont hx)
  simpa only [mellinInv,Complex.ofReal_ofNat,onLine] using inv

theorem pole_inverse_nat (n : ℕ) (hn : 0<n) :
    (n:ℂ) * mellinInv 2 (fun s => perronWeight s/(s-1)) (1/(n:ℝ)) = ((n:ℂ)-1)^2/2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h1 : 1≤(n:ℝ) := by exact_mod_cast hn
  have mem : 1/(n:ℝ) ∈ Ioc 0 1 := ⟨by positivity, (div_le_one hn').mpr h1⟩
  rw [pole_inverse (by positivity)]
  unfold poleProfile
  rw [show triangle (1/(n:ℝ)) = 1 - ((1/(n:ℝ):ℝ):ℂ) by
    exact indicator_of_mem mem (fun t : ℝ => 1-(t:ℂ))]
  simp only [Complex.cpow_neg_one,smul_eq_mul,one_div,Complex.ofReal_inv,
    Complex.ofReal_natCast,inv_inv]
  have nz : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

end BMORProgression
end

section
namespace BMORProgression
open Set Complex MeasureTheory ArithmeticFunction

noncomputable def endpointFactor (n : ℕ) (y : ℝ) : ℂ :=
  (n:ℂ) * (((1/(n:ℝ)):ℝ):ℂ)^(-((2:ℂ)+y*I))

noncomputable def regularFactor (q a : ℕ) [NeZero q] (y : ℝ) : ℂ :=
  let z := (2:ℂ)+y*I
  vonMangoldt.LFunctionResidueClassAux (a:ZMod q) z * perronWeight z

private noncomputable def poleInput (n : ℕ) (y : ℝ) : ℂ :=
  let z := (2:ℂ)+y*I
  (((1/(n:ℝ)):ℝ):ℂ)^(-z) * (perronWeight z/(z-1))

private theorem poleInput_integrable {n : ℕ} (hn : 0<n) : Integrable (poleInput n) := by
  let z : ℝ → ℂ := fun y => 2+y*I
  let x : ℝ := 1/(n:ℝ)
  have hx : 0<x := by dsimp [x]; positivity
  have nz : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hw : Integrable (fun y => perronWeight (z y)/(z y-1)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_ofNat,z] using poleWeight_vertical
  have cz : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have cp : Continuous (fun y : ℝ => (x:ℂ)^(-z y)) :=
    continuous_iff_continuousAt.mpr fun _ => (continuousAt_const_cpow nz).comp cz.continuousAt.neg
  change Integrable (fun y : ℝ => (x:ℂ)^(-z y) * (perronWeight (z y)/(z y-1)))
  apply (hw.norm.const_mul (x^(-2:ℝ))).mono' (cp.aestronglyMeasurable.mul hw.aestronglyMeasurable)
  filter_upwards with y
  simp only [Pi.mul_apply]
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [z]

private theorem split_integrand {q a : ℕ} [NeZero q] (ha : a.Coprime q) (n : ℕ) :
    (fun y => endpointFactor n y * regularFactor q a y) =
    fun y => (n:ℂ) * (perronIntegrand q a n y - (q.totient:ℂ)⁻¹ * poleInput n y) := by
  funext y
  let z : ℂ := 2+y*I
  have hz : 1<z.re := by norm_num [z]
  have eq := vonMangoldt.eqOn_LFunctionResidueClassAux ((ZMod.isUnit_iff_coprime a q).mpr ha)
    (show z ∈ {s : ℂ | 1<s.re} from hz)
  change (n:ℂ) * _ * (vonMangoldt.LFunctionResidueClassAux (a:ZMod q) z * perronWeight z) = _
  rw [eq]
  simp only [perronIntegrand,poleInput,z,div_eq_mul_inv]
  ring

private theorem regular_integrable {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n) :
    Integrable (fun y => endpointFactor n y * regularFactor q a y) := by
  rw [split_integrand ha]
  exact ((perronIntegrand_integrable q a n hn).sub
    ((poleInput_integrable hn).const_mul (q.totient:ℂ)⁻¹)).const_mul _

noncomputable def centeredIntegral (q a n : ℕ) [NeZero q] : ℂ :=
  (1/(2*Real.pi):ℝ) • ∫ y : ℝ, endpointFactor n y * regularFactor q a y

theorem centeredIntegral_eq {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n) :
    centeredIntegral q a n = (riesz q a n:ℂ) - ((n:ℂ)-1)^2/2/(q.totient:ℂ) := by
  have full : (n:ℂ) * ((1/(2*Real.pi):ℝ) • ∫ y, perronIntegrand q a n y) = (riesz q a n:ℂ) := by
    simpa only [mellinInv,perronIntegrand,Complex.ofReal_ofNat,smul_eq_mul] using (riesz_perron q a n hn).symm
  have pole : (n:ℂ) * ((1/(2*Real.pi):ℝ) • ∫ y, poleInput n y) = ((n:ℂ)-1)^2/2 := by
    simpa only [mellinInv,poleInput,Complex.ofReal_ofNat,smul_eq_mul] using pole_inverse_nat n hn
  rw [centeredIntegral,split_integrand ha,integral_const_mul,integral_sub (perronIntegrand_integrable q a n hn)
    ((poleInput_integrable hn).const_mul (q.totient:ℂ)⁻¹), integral_const_mul,←full,←pole]
  simp only [Complex.real_smul,div_eq_mul_inv]
  ring

/-- The same regular factor is integrated at both endpoints, so the difference can be taken before integration. -/
noncomputable def regularIncrement (q a m n : ℕ) [NeZero q] : ℂ :=
  (1/(2*Real.pi):ℝ) • ∫ y : ℝ, (endpointFactor n y - endpointFactor m y) * regularFactor q a y

theorem regularIncrement_eq {q a m n : ℕ} [NeZero q] (ha : a.Coprime q) (hm : 0<m) (hn : 0<n) :
    regularIncrement q a m n = centeredIntegral q a n - centeredIntegral q a m := by
  simp only [regularIncrement,centeredIntegral,sub_mul,integral_sub (regular_integrable ha hn)
    (regular_integrable ha hm),smul_sub]

theorem discrepancy_eq_regularIncrement {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n) :
    ((psi q a n - (n:ℝ)/q.totient : ℝ):ℂ) =
      regularIncrement q a n (n+1) - 1/(2*(q.totient:ℂ)) := by
  rw [regularIncrement_eq ha hn (Nat.succ_pos _),centeredIntegral_eq ha (Nat.succ_pos _),
    centeredIntegral_eq ha hn,riesz_succ]
  push_cast
  ring

theorem error_eq_increment_norm {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n) :
    |psi q a n - (n:ℝ)/q.totient| =
      ‖regularIncrement q a n (n+1) - 1/(2*(q.totient:ℂ))‖ := by
  rw [←discrepancy_eq_regularIncrement ha hn,Complex.norm_real,Real.norm_eq_abs]

end BMORProgression
end

section
namespace BMORProgression
open Set Complex MeasureTheory ArithmeticFunction

noncomputable def incrementKernel (m n : ℕ) (s : ℂ) : ℂ :=
  ((n:ℂ)^(s+1) - (m:ℂ)^(s+1)) * perronWeight s

private theorem endpointFactor_eq {n : ℕ} (hn : 0<n) (y : ℝ) :
    endpointFactor n y = (n:ℂ)^(((2:ℂ)+y*I)+1) := by
  have hp : (0:ℝ)≤(n:ℝ) := by positivity
  have nz : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [endpointFactor,one_div,Complex.ofReal_inv]
  rw [Complex.inv_cpow_ofReal_nonneg hp,Complex.cpow_neg,inv_inv,Complex.cpow_add _ _ nz,Complex.cpow_one]
  push_cast
  ring

theorem regularIncrement_kernel {q a m n : ℕ} [NeZero q] (hm : 0<m) (hn : 0<n) :
    regularIncrement q a m n = (1/(2*Real.pi):ℝ) •
      ∫ y : ℝ, let s := (2:ℂ)+y*I
               incrementKernel m n s * vonMangoldt.LFunctionResidueClassAux (a:ZMod q) s := by
  have eq (y : ℝ) : (endpointFactor n y-endpointFactor m y)*regularFactor q a y =
      incrementKernel m n ((2:ℂ)+y*I) * vonMangoldt.LFunctionResidueClassAux (a:ZMod q) ((2:ℂ)+y*I) := by
    rw [endpointFactor_eq hm,endpointFactor_eq hn]
    unfold regularFactor incrementKernel
    ring
  simp only [regularIncrement,eq]

private theorem power_increment_bound {m n : ℕ} (hm : 0<m) (hmn : m≤n) {s : ℂ} (hs : 0≤s.re) :
    ‖(n:ℂ)^(s+1)-(m:ℂ)^(s+1)‖ ≤ (‖s+1‖*(n:ℝ)^s.re)*((n:ℝ)-m) := by
  have hmn' : (m:ℝ)≤n := by exact_mod_cast hmn
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have h1 : s+1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at this
    linarith
  let f : ℝ → ℂ := fun x => (x:ℂ)^(s+1)
  let df : ℝ → ℂ := fun x => (s+1)*(x:ℂ)^s
  have hd (x : ℝ) (hx : x ∈ Icc (m:ℝ) n) : HasDerivWithinAt f (df x) (Icc (m:ℝ) n) x := by
    simpa only [f,df,add_sub_cancel_right] using
      (hasDerivAt_ofReal_cpow_const (hm'.trans_le hx.1).ne' h1).hasDerivWithinAt (s := Icc (m:ℝ) n)
  have hb (x : ℝ) (hx : x ∈ Icc (m:ℝ) n) : ‖df x‖ ≤ ‖s+1‖*(n:ℝ)^s.re := by
    dsimp only [df]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hm'.trans_le hx.1)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hm'.le.trans hx.1) hx.2 hs) (norm_nonneg _)
  have val := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc (m:ℝ) n)
    (left_mem_Icc.mpr hmn') (right_mem_Icc.mpr hmn')
  simpa only [f,Complex.ofReal_natCast,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hmn')] using val

/-- A joint kernel estimate: at small height one factor cancels, at large height both denominators remain. -/
theorem incrementKernel_bound {m n : ℕ} (hm : 0<m) (hmn : m≤n) {s : ℂ} (hs : 0≤s.re) :
    ‖incrementKernel m n s‖ ≤ min (((n:ℝ)-m)*(n:ℝ)^s.re/‖s‖)
      (2*(n:ℝ)^(s.re+1)/(‖s‖*‖s+1‖)) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hmn' : (m:ℝ)≤n := by exact_mod_cast hmn
  have hn' := hm'.trans_le hmn'
  have hp : s+1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at this
    linarith
  have hnorm : ‖s+1‖≠0 := norm_ne_zero_iff.mpr hp
  rw [incrementKernel,perronWeight,norm_mul,norm_div,norm_mul,norm_one,mul_one_div]
  apply le_min
  · calc
      _ ≤ ((‖s+1‖*(n:ℝ)^s.re)*((n:ℝ)-m))/(‖s‖*‖s+1‖) :=
        div_le_div_of_nonneg_right (power_increment_bound hm hmn hs) (by positivity)
      _ = _ := by
        rw [div_mul_eq_div_div_swap]
        field_simp [hnorm]
        <;> ring
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have h0 : (0:ℝ)≤s.re+1 := by linarith
    have h := norm_sub_le ((n:ℂ)^(s+1)) ((m:ℂ)^(s+1))
    have hnrm (k : ℕ) (hk : (0:ℝ)<k) : ‖(k:ℂ)^(s+1)‖=(k:ℝ)^(s.re+1) := by
      simpa only [Complex.ofReal_natCast,Complex.add_re,Complex.one_re] using
        Complex.norm_cpow_eq_rpow_re_of_pos (y := s+1) hk
    rw [hnrm n hn',hnrm m hm'] at h
    linarith [Real.rpow_le_rpow hm'.le hmn' h0]

end BMORProgression
end

section
namespace BMORProgression
open Set Complex DirichletCharacter

/-- Cancel the unique possible pole before working on a compact height range. -/
noncomputable def poleRemoved {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then LFunctionTrivChar₁ q else LFunction χ

theorem poleRemoved_continuous {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (poleRemoved χ) := by
  classical
  by_cases h : χ=1
  · simpa [poleRemoved,h] using (differentiable_LFunctionTrivChar₁ q).continuous
  · simpa [poleRemoved,h] using (differentiable_LFunction h).continuous

theorem poleRemoved_ne_zero_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) : poleRemoved χ s ≠ 0 := by
  classical
  by_cases h : χ=1
  · subst χ
    simp only [poleRemoved,ite_true]
    by_cases eq : s=1
    · subst s; exact LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [LFunctionTrivChar₁,Function.update_of_ne eq]
      exact mul_ne_zero (sub_ne_zero.mpr eq) (LFunction_ne_zero_of_one_le_re 1 (.inr eq) hs)
  · simpa [poleRemoved,h] using LFunction_ne_zero_of_one_le_re χ (.inl h) hs

/-- At fixed height, all the characters of a fixed modulus have a common positive
zero-free width to the left of the line of absolute convergence. -/
theorem exists_poleRemoved_strip {q : ℕ} [NeZero q] (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
      |s.im| ≤ T → 1-δ ≤ s.re → poleRemoved χ s ≠ 0 := by
  classical
  let K : Set ℂ := (fun t : ℝ => (⟨1,t⟩ : ℂ)) '' Icc (-T) T
  let U : Set ℂ := ⋂ χ : DirichletCharacter ℂ q, {s | poleRemoved χ s ≠ 0}
  have line : (fun t : ℝ => (⟨1,t⟩ : ℂ)) = fun t : ℝ => (1:ℂ)+(t:ℂ)*I := by
    funext t
    apply Complex.ext <;> simp
  have cK : IsCompact K := isCompact_Icc.image (by rw [line]; fun_prop)
  have oU : IsOpen U := isOpen_iInter_of_finite fun χ =>
    isOpen_ne.preimage (poleRemoved_continuous χ)
  have incl : K ⊆ U := by
    rintro _ ⟨t,_,rfl⟩
    exact mem_iInter.mpr fun χ => poleRemoved_ne_zero_right χ le_rfl
  obtain ⟨δ,hδ,hsub⟩ := cK.exists_cthickening_subset_open oU incl
  refine ⟨δ,hδ,?_⟩
  intro χ s him hre
  by_cases hright : 1≤s.re
  · exact poleRemoved_ne_zero_right χ hright
  have hm : (⟨1,s.im⟩ : ℂ) ∈ K := ⟨s.im, abs_le.mp him,rfl⟩
  have dif : s - (⟨1,s.im⟩ : ℂ) = ((s.re-1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have dist_le : dist s (⟨1,s.im⟩ : ℂ) ≤ δ := by
    rw [dist_eq_norm,dif,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : s.re-1≤0)]
    linarith
  exact mem_iInter.mp (hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hm dist_le)) χ

theorem exists_LFunction_zero_free_strip {q : ℕ} [NeZero q] (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
      |s.im| ≤ T → 1-δ ≤ s.re → (χ≠1 ∨ s≠1) → LFunction χ s ≠ 0 := by
  classical
  obtain ⟨δ,hδ,H⟩ := exists_poleRemoved_strip (q := q) T
  refine ⟨δ,hδ,?_⟩
  intro χ s him hre hp
  have h := H χ s him hre
  by_cases hχ : χ=1
  · subst χ
    have hs := hp.resolve_left (not_not_intro rfl)
    have hn : (s-1)*LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by simpa only [poleRemoved,ite_true,LFunctionTrivChar₁,Function.update_of_ne hs] using h
    exact fun hz => hn (mul_eq_zero_of_right _ hz)
  · simpa [poleRemoved,hχ] using h

/-- Finite conductors and finite heights have a common zero-free width. -/
theorem exists_bounded_moduli_zero_free_strip (Q : ℕ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ) [NeZero q], q ≤ Q →
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), |s.im| ≤ T →
        1-δ ≤ s.re → (χ≠1 ∨ s≠1) → LFunction χ s ≠ 0 := by
  induction Q with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    intro q hq hle
    exact ((NeZero.ne q) (by omega)).elim
  | succ Q ih =>
    obtain ⟨a,ha,A⟩ := ih
    obtain ⟨b,hb,B⟩ := exists_LFunction_zero_free_strip (q := Q+1) T
    refine ⟨min a b,lt_min ha hb,?_⟩
    intro q hq hle χ s ht hr hp
    rcases Nat.eq_or_lt_of_le hle with rfl | h
    · exact B χ s ht (by linarith [min_le_right a b]) hp
    · exact A q (Nat.lt_succ_iff.mp h) χ s ht (by linarith [min_le_left a b]) hp

/-- Explicit disk bounds from a certified value at the center and an upper bound on
the derivative. The same margin controls the logarithmic derivative on the disk. -/
theorem poleRemoved_disk_certificate {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (z : ℂ) {r m B : ℝ} (hr : 0 ≤ r) (hmargin : B*r < m) (hcenter : m ≤ ‖poleRemoved χ z‖)
    (hder : ∀ w ∈ Metric.closedBall z r, ‖deriv (poleRemoved χ) w‖ ≤ B)
    (w : ℂ) (hw : w ∈ Metric.closedBall z r) :
    m-B*r ≤ ‖poleRemoved χ w‖ ∧ poleRemoved χ w ≠ 0 ∧
      ‖deriv (poleRemoved χ) w / poleRemoved χ w‖ ≤ B/(m-B*r) := by
  classical
  have hd : Differentiable ℂ (poleRemoved χ) := by
    by_cases h : χ=1
    · simpa [poleRemoved,h] using differentiable_LFunctionTrivChar₁ q
    · simpa [poleRemoved,h] using differentiable_LFunction h
  have hz : z ∈ Metric.closedBall z r := Metric.mem_closedBall_self hr
  have hb := (norm_nonneg _).trans (hder z hz)
  have lip := (convex_closedBall z r).norm_image_sub_le_of_norm_deriv_le (fun x _ => hd x) hder hz hw
  have distw : ‖w-z‖ ≤ r := by simpa [Metric.mem_closedBall,dist_eq_norm] using hw
  have diff := lip.trans (mul_le_mul_of_nonneg_left distw hb)
  have triangle := norm_le_norm_add_norm_sub (poleRemoved χ w) (poleRemoved χ z)
  have low : m-B*r ≤ ‖poleRemoved χ w‖ := by linarith
  have pos : 0 < m-B*r := by linarith
  refine ⟨low,norm_pos_iff.mp (pos.trans_le low),?_⟩
  rw [norm_div]
  exact div_le_div₀ hb (hder w hw) pos low

end BMORProgression
end

section
namespace BMORProgression
open Set Complex MeasureTheory ArithmeticFunction DirichletCharacter
open scoped Interval

theorem regularAux_differentiableAt {q a : ℕ} [NeZero q] {s : ℂ}
    (hn : ∀ χ : DirichletCharacter ℂ q, poleRemoved χ s ≠ 0) :
    DifferentiableAt ℂ (vonMangoldt.LFunctionResidueClassAux (a:ZMod q)) s := by
  classical
  have pd := differentiable_LFunctionTrivChar₁ q
  have nz : LFunctionTrivChar₁ q s ≠ 0 := by simpa [poleRemoved] using hn 1
  have princ : DifferentiableAt ℂ (fun v => -deriv (LFunctionTrivChar₁ q) v / LFunctionTrivChar₁ q v) s :=
    ((pd.analyticAt _).deriv.differentiableAt.neg).div (pd s) nz
  unfold vonMangoldt.LFunctionResidueClassAux
  apply (differentiableAt_const _).mul
  apply princ.sub
  apply DifferentiableAt.fun_sum
  intro χ hχ
  have ne : χ ≠ 1 := by simpa using hχ
  have d := differentiable_LFunction ne
  have nχ : LFunction χ s ≠ 0 := by simpa [poleRemoved,ne] using hn χ
  exact ((differentiableAt_const _).mul ((d.analyticAt _).deriv.differentiableAt)).div (d s) nχ

noncomputable def regularContour (q a m n : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  incrementKernel m n s * vonMangoldt.LFunctionResidueClassAux (a:ZMod q) s

set_option maxHeartbeats 1200000 in
theorem regularContour_differentiableAt {q a m n : ℕ} [NeZero q] (hm : 0<m) (hn : 0<n)
    {s : ℂ} (hs : 0<s.re) (hz : ∀ χ : DirichletCharacter ℂ q, poleRemoved χ s ≠ 0) :
    DifferentiableAt ℂ (regularContour q a m n) s := by
  have di : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
  have ds : DifferentiableAt ℂ (fun w : ℂ => w+1) s := di.add_const 1
  have cp (k : ℕ) (hk : 0<k) : DifferentiableAt ℂ (fun w : ℂ => (k:ℂ)^(w+1)) s := by
    have nz : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have dc : DifferentiableAt ℂ (fun u : ℂ => (k:ℂ)^u) (s+1) :=
      (Complex.hasStrictDerivAt_const_cpow (.inl nz)).hasDerivAt.differentiableAt
    exact dc.comp s ds
  have u : s*(s+1) ≠ 0 := by
    apply mul_ne_zero <;> intro h <;> apply_fun Complex.re at h <;> simp at h <;> linarith
  have w : DifferentiableAt ℂ perronWeight s := (differentiableAt_const (1:ℂ)).div (di.mul ds) u
  unfold regularContour incrementKernel
  exact (((cp n hn).sub (cp m hm)).mul w).mul (regularAux_differentiableAt (a := a) hz)

noncomputable def contourVertical (f : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T, f ((σ:ℂ)+y*I)

noncomputable def contourHorizontal (f : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  ∫ x : ℝ in σ..2, f ((x:ℂ)+t*I)

theorem shift_regularContour {q a m n : ℕ} [NeZero q] (hm : 0<m) (hn : 0<n)
    {σ T : ℝ} (hσ : 0<σ) (hb : σ≤2) (hT : 0≤T)
    (hz : ∀ (s : ℂ), s.re ∈ Icc σ 2 → |s.im|≤T → ∀ χ : DirichletCharacter ℂ q, poleRemoved χ s ≠ 0) :
    let f := regularContour q a m n
    contourVertical f 2 T = contourVertical f σ T +
        I*(contourHorizontal f σ (-T) - contourHorizontal f σ T) := by
  let f := regularContour q a m n
  have hd : DifferentiableOn ℂ f (Icc σ 2 ×ℂ Icc (-T) T) := by
    intro s hs
    apply (regularContour_differentiableAt hm hn (hσ.trans_le hs.1.1)
      (hz s hs.1 (abs_le.mpr hs.2))).differentiableWithinAt
  have hbdy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (⟨σ,-T⟩ : ℂ) (⟨2,T⟩ : ℂ) (by simpa only [uIcc_of_le hb,uIcc_of_le (neg_le_self hT)] using hd)
  change contourHorizontal f σ (-T) - contourHorizontal f σ T + I • contourVertical f 2 T
    - I • contourVertical f σ T = 0 at hbdy
  change contourVertical f 2 T = contourVertical f σ T + I*_
  simp only [smul_eq_mul] at hbdy
  linear_combination (norm := ring_nf <;> simp [Complex.I_sq] <;> ring) -I * hbdy

theorem exists_shift_below_one {q : ℕ} [NeZero q] {T : ℝ} (hT : 0≤T) :
    ∃ σ : ℝ, 0<σ ∧ σ<1 ∧ ∀ (a m n : ℕ), 0<m → 0<n →
      let f := regularContour q a m n
      contourVertical f 2 T = contourVertical f σ T +
        I*(contourHorizontal f σ (-T) - contourHorizontal f σ T) := by
  obtain ⟨δ,hδ,hnz⟩ := exists_poleRemoved_strip (q := q) T
  let σ := max (1/2:ℝ) (1-δ)
  have hσ : 0<σ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hs1 : σ<1 := max_lt (by norm_num) (by linarith)
  refine ⟨σ,hσ,hs1,?_⟩
  intro a m n hm hn
  exact shift_regularContour hm hn hσ (by linarith) hT
    (fun s hs him χ => hnz χ s him ((le_max_right _ _).trans hs.1))

end BMORProgression
end

section
namespace BMORProgression
open Set Complex MeasureTheory ArithmeticFunction DirichletCharacter
open scoped Interval

theorem regularAux_right_bound {q a : ℕ} [NeZero q] (ha : a.Coprime q) (y : ℝ) :
    ‖vonMangoldt.LFunctionResidueClassAux (a:ZMod q) ((2:ℂ)+y*I)‖ ≤ 5 := by
  let s := (2:ℂ)+y*I
  have hs : 1<s.re := by norm_num [s]
  have heq := vonMangoldt.eqOn_LFunctionResidueClassAux ((ZMod.isUnit_iff_coprime a q).mpr ha)
    (show s ∈ {w : ℂ | 1<w.re} from hs)
  change ‖vonMangoldt.LFunctionResidueClassAux (a:ZMod q) s‖ ≤ 5
  rw [heq]
  have hφ : (1:ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hs1 : (1:ℝ) ≤ ‖s-1‖ := by
    have h := Complex.abs_re_le_norm (s-1)
    norm_num [s] at h
    exact h
  have hφinv : ‖(q.totient:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ hφ
  have hpart : ‖(q.totient:ℂ)⁻¹ / (s-1)‖ ≤ 1 := by
    rw [norm_div]
    exact (div_le_one (by linarith : 0<‖s-1‖)).mpr (hφinv.trans hs1)
  exact (norm_sub_le _ _).trans (by linarith [progression_series_bound q a y])

private theorem rectangle_majorant {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n)
    (y : ℝ) : let s := (2:ℂ)+y*I
    ‖regularContour q a n (n+1) s‖ ≤ 10*((n:ℝ)+1)^3*‖perronWeight s‖ := by
  let s := (2:ℂ)+y*I
  have hpower (m : ℕ) (hm : 0<m) : ‖(m:ℂ)^(s+1)‖ = (m:ℝ)^3 := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (y := s+1) (show (0:ℝ)<m by exact_mod_cast hm)
    norm_num [s] at h ⊢
    exact h
  have hdiff : ‖((n+1:ℕ):ℂ)^(s+1)-(n:ℂ)^(s+1)‖ ≤ 2*((n:ℝ)+1)^3 := by
    have ht := norm_sub_le (((n+1:ℕ):ℂ)^(s+1)) ((n:ℂ)^(s+1))
    rw [hpower (n+1) (Nat.succ_pos _), hpower n hn] at ht
    push_cast at ht ⊢
    have hp : (n:ℝ)^3 ≤ ((n:ℝ)+1)^3 := by gcongr; linarith
    linarith
  have hA := regularAux_right_bound ha y
  change ‖(((↑(n+1):ℂ)^(s+1)-(n:ℂ)^(s+1))*perronWeight s)*
      vonMangoldt.LFunctionResidueClassAux (a:ZMod q) s‖ ≤ _
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (2*((n:ℝ)+1)^3 * ‖perronWeight s‖)*5 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)) hA (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem rectangle_integrable {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n) :
    Integrable (fun y : ℝ => regularContour q a n (n+1) ((2:ℂ)+y*I)) := by
  let z := fun y : ℝ => (2:ℂ)+y*I
  have hw : Integrable (fun y => perronWeight (z y)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_ofNat,z] using perron_vertical
  apply (hw.norm.const_mul (10*((n:ℝ)+1)^3)).mono' _ (Filter.Eventually.of_forall (rectangle_majorant ha hn))
  apply Continuous.aestronglyMeasurable
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have h2 : (z y).re = 2 := by simp [z]
  exact (regularContour_differentiableAt hn (Nat.succ_pos n) (by linarith : 0 < (z y).re)
    (fun χ => poleRemoved_ne_zero_right χ (by linarith))).continuousAt.comp hz.continuousAt

/-- Bound the exact AP discrepancy by the three finite edges of a zero-free rectangle. -/
theorem discrepancy_rectangle_budget {q a n : ℕ} [NeZero q] (ha : a.Coprime q) (hn : 0<n)
    {σ T : ℝ} (hσ : 0<σ) (hb : σ≤2) (hT : 0<T)
    (hz : ∀ (s : ℂ), s.re ∈ Icc σ 2 → |s.im|≤T →
      ∀ χ : DirichletCharacter ℂ q, poleRemoved χ s ≠ 0) :
    let f := regularContour q a n (n+1)
    |psi q a n - (n:ℝ)/q.totient| ≤ 1/(2*(q.totient:ℝ)) + 10*((n:ℝ)+1)^3/(Real.pi*T) +
      (‖contourVertical f σ T‖ + ‖contourHorizontal f σ (-T)‖ + ‖contourHorizontal f σ T‖) /
      (2*Real.pi) := by
  let f := regularContour q a n (n+1)
  let F := fun y : ℝ => f ((2:ℂ)+y*I)
  let c := (1/(2*Real.pi):ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  let v := contourVertical f 2 T
  have hv : v = ∫ y in Ioc (-T) T, F y := by
    simpa only [v,contourVertical,F,Complex.ofReal_ofNat] using
      (intervalIntegral.integral_of_le (f := F) (neg_le_self hT.le))
  have ht := truncate_symmetric (F := F) (rectangle_integrable ha hn)
    (C := 10*((n:ℝ)+1)^3) hT (by
      intro y hy
      let z := (2:ℂ)+y*I
      have hz0 : |y| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
      have hz1 : |y| ≤ ‖z+1‖ := by simpa [z] using Complex.abs_im_le_norm (z+1)
      have hprod : y^2 ≤ ‖z‖*‖z+1‖ := by
        simpa [←sq] using mul_le_mul hz0 hz1 (abs_nonneg y) (norm_nonneg z)
      have hw : ‖perronWeight z‖ ≤ 1/y^2 := by
        rw [perronWeight,norm_div,norm_one,norm_mul]
        exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hy) hprod
      exact (rectangle_majorant ha hn y).trans (by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hw
          (by positivity : 0≤10*((n:ℝ)+1)^3)))
  rw [←hv] at ht
  have hshift : v = contourVertical f σ T +
      I*(contourHorizontal f σ (-T)-contourHorizontal f σ T) :=
    shift_regularContour hn (Nat.succ_pos n) hσ hb hT.le hz
  have hev : ‖v‖ ≤ ‖contourVertical f σ T‖ + ‖contourHorizontal f σ (-T)‖ +
        ‖contourHorizontal f σ T‖ := by
    rw [hshift]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul,Complex.norm_I,one_mul]
    linarith [norm_sub_le (contourHorizontal f σ (-T)) (contourHorizontal f σ T)]
  have hi : ‖∫ y : ℝ, F y‖ ≤ 2 * (10*((n:ℝ)+1)^3)/T +
      (‖contourVertical f σ T‖ + ‖contourHorizontal f σ (-T)‖ + ‖contourHorizontal f σ T‖) := by
    calc
      _ = ‖((∫ y : ℝ, F y)-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add ht hev)
  have hreg : regularIncrement q a n (n+1) = c • ∫ y : ℝ, F y :=
    regularIncrement_kernel hn (Nat.succ_pos n)
  change |psi q a n - (n:ℝ)/q.totient| ≤ _
  rw [error_eq_increment_norm ha hn,hreg]
  have hpole : ‖(1:ℂ)/(2*(q.totient:ℂ))‖ = 1/(2*(q.totient:ℝ)) := by simp
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc,hpole]
  calc
    _ ≤ c*(2*(10*((n:ℝ)+1)^3)/T + (‖contourVertical f σ T‖ +
          ‖contourHorizontal f σ (-T)‖ + ‖contourHorizontal f σ T‖)) + 1/(2*(q.totient:ℝ)) :=
      by exact add_le_add (mul_le_mul_of_nonneg_left hi hc.le) (le_refl _)
    _ = _ := by dsimp only [c,f]; ring

end BMORProgression
end

section
/-!
Numerical comparison of the BMOR low-zero cutoff budgets for 3 ≤ q ≤ 105.
Table: https://nt.math.ubc.ca/BeMaObRe/c-psi-theta-pi/c_all_rounded.txt
SHA-256 of the header and first 103 rows (original bytes):
9921ec224e6e847aac89eeecff17a0489c43f4bf71d9e42aa4b15fadbf28791f.
The theorem checks the arithmetic expression using the tabulated rounded cψ.
An analytic bound D_old ≤ cψ, as well as the analytic cutoff loss ≤ 41/5
per character, would each require its own proof for an application to D_new.
-/

namespace BMORLowZerosBudget

/-- The fourth numeric column cψ, in units of 10⁻⁷, starting at q = 3. -/
def scaledPsi (q : ℕ) : ℕ :=
  (#[3964, 4770, 3665, 3964, 4584, 5742, 5048, 3665, 4508, 6730, 4491, 4584,
  5330, 5742, 4472, 5048, 4467, 6257, 5195, 4508, 4450, 6733, 4703, 4491,
  5051, 6078, 4440, 5330, 4439, 5745, 5090, 4472, 4890, 6897, 4431, 4467,
  5061, 6261, 4426, 5195, 4425, 5937, 5446, 4450, 4421, 6735, 4584, 4703,
  5029, 5895, 4416, 5051, 4793, 6079, 5019, 4440, 4412, 7449, 4411, 4439,
  5299, 5736, 4767, 5090, 4407, 5851, 4999, 4890, 4404, 6898, 4402, 4431,
  5354, 5836, 4677, 5061, 4399, 6259, 5035, 4426, 4396, 7211, 4735, 4425,
  4982, 5928, 4393, 5446, 4651, 5810, 4977, 4421, 4722, 6729, 4390, 4584,
  5177, 6284, 8443, 5029, 8440, 9591, 9122][q - 3]?).getD 0

inductive Cutoff | small | middle | large

def cutoff : ℕ → Cutoff
  | 101 | 103 | 104 | 105 => .small
  | 3 | 4 | 5 | 6 | 10 => .large
  | _ => .middle

def Cutoff.x : Cutoff → ℕ
  | .small => 10^12
  | .middle => 10^13
  | .large => 4 * 10^13

private def Cutoff.lowerRoot : Cutoff → ℕ
  | .small => 1000000
  | .middle => 3000000
  | .large => 6000000

private def Cutoff.upperLog : Cutoff → ℕ
  | .small => 28
  | .middle => 31
  | .large => 33

noncomputable def cPsi (q : ℕ) : ℝ := (scaledPsi q : ℝ) / 10000000

private theorem log_ten_lt : Real.log 10 < 7 / 3 := by
  have he : (27 / 10 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hp : (10 : ℝ)^3 < (Real.exp 1)^7 := calc
    (10 : ℝ)^3 < (27 / 10 : ℝ)^7 := by norm_num
    _ < (Real.exp 1)^7 := by gcongr
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 10^3) hp
  rw [Real.log_pow, Real.log_pow, Real.log_exp] at hlog
  norm_num at hlog
  linarith

private theorem Cutoff.log_le (k : Cutoff) : Real.log (k.x : ℝ) ≤ k.upperLog := by
  have h := log_ten_lt
  cases k with
  | small =>
    change Real.log ((10^12 : ℕ) : ℝ) ≤ 28
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  | middle =>
    change Real.log ((10^13 : ℕ) : ℝ) ≤ 31
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  | large =>
    have hbound : Real.log ((4 * 10^13 : ℕ) : ℝ) ≤ Real.log ((10 : ℝ)^14) :=
      Real.log_le_log (by norm_num) (by norm_num)
    change Real.log ((4 * 10^13 : ℕ) : ℝ) ≤ 33
    rw [Real.log_pow] at hbound
    norm_num at hbound ⊢
    linarith

private theorem Cutoff.le_sqrt (k : Cutoff) : (k.lowerRoot : ℝ) ≤ Real.sqrt k.x := by
  apply Real.le_sqrt_of_sq_le
  cases k <;> norm_num [Cutoff.lowerRoot, Cutoff.x]

private theorem Cutoff.lowerRoot_pos (k : Cutoff) : 0 < k.lowerRoot := by
  cases k <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem checked_rows : ∀ q : Fin 106, 3 ≤ q.val →
    840 * (5 * scaledPsi q.val * (cutoff q.val).lowerRoot +
      41 * (scaledPsi q.val * q.val.totient + (cutoff q.val).upperLog * 10000000)) <
      5 * (cutoff q.val).lowerRoot * 10000000 := by decide +kernel

/-- All 103 rounded rows meet the modified numerical budget. -/
theorem low_zero_budget (q : ℕ) (hq₀ : 3 ≤ q) (hq₁ : q ≤ 105) :
    cPsi q + (41 / 5) * (cPsi q * (q.totient : ℝ) + Real.log ((cutoff q).x : ℝ)) /
      Real.sqrt ((cutoff q).x : ℝ) < 1 / 840 := by
  let k := cutoff q
  have hR : 0 < (k.lowerRoot : ℝ) := by exact_mod_cast k.lowerRoot_pos
  have hU : 0 ≤ (k.upperLog : ℝ) := by positivity
  have hroot := k.le_sqrt
  have hlog := k.log_le
  have hpos : 0 ≤ cPsi q := by unfold cPsi; positivity
  have hcalcN := checked_rows ⟨q, by omega⟩ hq₀
  have hcalc : (840 : ℝ) * (5 * (scaledPsi q : ℝ) * (k.lowerRoot : ℝ) +
      41 * ((scaledPsi q : ℝ) * (q.totient : ℝ) + (k.upperLog : ℝ) * 10000000)) <
      5 * (k.lowerRoot : ℝ) * 10000000 := by exact_mod_cast hcalcN
  calc
    _ ≤ cPsi q + (41 / 5) * (cPsi q * (q.totient : ℝ) + (k.upperLog : ℝ)) /
        Real.sqrt (k.x : ℝ) := by
      exact add_le_add (le_refl _) (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hlog) (by norm_num))
        (Real.sqrt_nonneg _))
    _ ≤ cPsi q + (41 / 5) * (cPsi q * (q.totient : ℝ) + (k.upperLog : ℝ)) /
        (k.lowerRoot : ℝ) := by
      exact add_le_add (le_refl _) (div_le_div_of_nonneg_left
        (show 0 ≤ (41 / 5 : ℝ) * (cPsi q * (q.totient : ℝ) + (k.upperLog : ℝ)) by positivity)
        hR hroot)
    _ < 1 / 840 := by
      unfold cPsi
      field_simp
      nlinarith only [hcalc]

end BMORLowZerosBudget
end

section
/- The following unconditional summation by parts and analytic continuation lemmas
are adapted from the project's accepted L_goldbach_grh_progression_error,
namespace GoldbachGrhGrowth. -/
open scoped BigOperators Topology
open Asymptotics Complex Filter Finset MeasureTheory Set

noncomputable section

namespace BMORModThree.Mellin

variable {q : ℕ} [NeZero q]

/-- The average value of a Dirichlet character over a full period. -/
def charMean (χ : DirichletCharacter ℂ q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : ZMod q, χ a

open scoped Classical in
theorem charMean_eq (χ : DirichletCharacter ℂ q) :
    charMean χ = if χ = 1 then (q.totient : ℂ) / (q : ℂ) else 0 := by
  by_cases hχ : χ = 1
  · subst χ
    simp [charMean, MulChar.sum_one_eq_card_units,
      ZMod.card_units_eq_totient, div_eq_inv_mul]
  · simp only [charMean, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem level_mul_charMean (χ : DirichletCharacter ℂ q) :
    (q : ℂ) * charMean χ = ∑ a : ZMod q, χ a := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [charMean, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem norm_charMean_le_one (χ : DirichletCharacter ℂ q) : ‖charMean χ‖ ≤ 1 := by
  classical
  by_cases hχ : χ = 1
  · simp only [charMean_eq, ite_eq_left hχ, norm_div, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast q.pos_of_neZero)).2
    exact_mod_cast q.totient_le
  · simp [charMean_eq, hχ]

/-- The character sum over the positive integers at most `n`. -/
def charPartialSum (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ range n, χ ((k + 1 : ℕ) : ZMod q)

omit [NeZero q] in
theorem norm_charPartialSum_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖charPartialSum χ n‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ k ∈ range n, ‖χ ((k + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
    _ = n := by simp

private theorem sum_character_block (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ k ∈ range q, χ ((m + k : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
  let e : Fin q ≃ ZMod q :=
    { toFun := fun k => (k.val : ZMod q)
      invFun := fun a => ⟨a.val, a.val_lt⟩
      left_inv := fun k => Fin.ext (by simp [Nat.mod_eq_of_lt k.isLt])
      right_inv := ZMod.natCast_zmod_val }
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => χ ((m + k : ℕ) : ZMod q)) q]
  refine Fintype.sum_equiv (e.trans (Equiv.addRight (m : ZMod q))) _ _ fun k => ?_
  change χ ((m + k.val : ℕ) : ZMod q) = χ ((k.val : ZMod q) + (m : ZMod q))
  rw [Nat.cast_add, add_comm]

/-- The centered character sum at a natural-number endpoint. -/
def integerRemainder (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  charPartialSum χ n - (n : ℂ) * charMean χ

theorem integerRemainder_periodic (χ : DirichletCharacter ℂ q) :
    Function.Periodic (integerRemainder χ) q := by
  intro n
  have hBlock : (∑ k ∈ range q, χ ((n + k + 1 : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using sum_character_block χ (n + 1)
  simp only [integerRemainder, charPartialSum, Finset.sum_range_add]
  rw [hBlock]
  simp only [Nat.cast_add, add_mul, level_mul_charMean]
  abel

theorem norm_integerRemainder_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖integerRemainder χ n‖ ≤ 2 * (q : ℝ) := by
  rw [← (integerRemainder_periodic χ).map_mod_nat n]
  let r := n % q
  have hr : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt n q.pos_of_neZero).le
  calc
    _ ≤ ‖charPartialSum χ r‖ + ‖(r : ℂ) * charMean χ‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) + (r : ℝ) := by
      refine add_le_add (norm_charPartialSum_le χ r) ?_
      rw [norm_mul, Complex.norm_natCast]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_charMean_le_one χ) r.cast_nonneg
    _ ≤ _ := by linarith

/-- The centered character sum for real endpoints, extended by zero at `x ≤ 1`. -/
def periodicRemainder (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ

theorem norm_periodicRemainder_le (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖periodicRemainder χ x‖ ≤ 3 * (q : ℝ) := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · have hx0 : 0 ≤ x := zero_le_one.trans (mem_Ioi.mp hx).le
    have hd : ‖(⌊x⌋₊ : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hx0))]
      linarith [Nat.lt_floor_add_one x]
    have hsplit : charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ =
        integerRemainder χ ⌊x⌋₊ + ((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ := by
      unfold integerRemainder
      ring
    rw [periodicRemainder, indicator_of_mem hx, hsplit]
    calc
      _ ≤ ‖integerRemainder χ ⌊x⌋₊‖ + ‖((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ‖ :=
        norm_add_le _ _
      _ ≤ 2 * (q : ℝ) + 1 := by
        refine add_le_add (norm_integerRemainder_le χ _) ?_
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hd (norm_charMean_le_one χ) (norm_nonneg _) zero_le_one
      _ ≤ _ := by
        have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
        linarith
  · rw [periodicRemainder, indicator_of_notMem hx, norm_zero]
    positivity

omit [NeZero q] in
private theorem measurable_partialSum_floor (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊) :=
  (measurable_of_countable (charPartialSum χ)).comp measurable_id.nat_floor

private theorem measurable_centeredCharSum (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) :=
  (measurable_partialSum_floor χ).sub (continuous_ofReal.measurable.mul_const _)

theorem measurable_periodicRemainder (χ : DirichletCharacter ℂ q) :
    Measurable (periodicRemainder χ) :=
  (measurable_centeredCharSum χ).indicator measurableSet_Ioi

/-- The Mellin transform of the centered sum, with exponent `-s-1` in the integral. -/
def remainderMellin (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  mellin (periodicRemainder χ) (-s)

theorem remainderMellin_eq_integral (χ : DirichletCharacter ℂ q) (s : ℂ) :
    remainderMellin χ s = ∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) := by
  have hIntegrand : (fun x : ℝ => (x : ℂ) ^ (-s - 1) • periodicRemainder χ x) =
      (Ioi (1 : ℝ)).indicator (fun x => (x : ℂ) ^ (-s - 1) *
        (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) := by
    ext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [periodicRemainder, indicator_of_mem hx, smul_eq_mul]
    · simp only [periodicRemainder, indicator_of_notMem hx, smul_zero]
  rw [remainderMellin, mellin, hIntegrand, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi zero_le_one)]

private theorem norm_weightedRemainder_le (χ : DirichletCharacter ℂ q) (s : ℂ)
    {x : ℝ} (hx : x ∈ Ioi (1 : ℝ)) :
    ‖(x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)‖ ≤
      (3 * (q : ℝ)) * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans (mem_Ioi.mp hx)
  have hBound := norm_periodicRemainder_le χ x
  rw [periodicRemainder, indicator_of_mem hx] at hBound
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, neg_re, one_re]
  exact (mul_le_mul_of_nonneg_left hBound (Real.rpow_nonneg hx0.le _)).trans_eq (mul_comm _ _)

private theorem weightedRemainder_integrableOn (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) := by
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine Integrable.mono' hBound ?_ ?_
  · have hKernel : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
      intro x hx
      exact (continuousAt_ofReal_cpow_const x _ (Or.inr (zero_lt_one.trans (mem_Ioi.mp hx)).ne')).continuousWithinAt
    exact (hKernel.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_centeredCharSum χ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx

theorem norm_remainderMellin_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    ‖remainderMellin χ s‖ ≤ (3 * (q : ℝ)) / s.re := by
  rw [remainderMellin_eq_integral]
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine (norm_integral_le_of_norm_le hBound ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hp zero_lt_one]
    rw [show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
    simp only [div_neg, neg_div, neg_neg, mul_one_div]

theorem differentiableAt_remainderMellin (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (remainderMellin χ) s := by
  have hLoc : LocallyIntegrableOn (periodicRemainder χ) (Ioi (0 : ℝ)) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hK => ?_
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_periodicRemainder χ).aestronglyMeasurable
      (Eventually.of_forall (norm_periodicRemainder_le χ))
  have hTop : periodicRemainder χ =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound (3 * (q : ℝ)) (Eventually.of_forall fun x => ?_)
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using norm_periodicRemainder_le χ x
  have hBot : periodicRemainder χ =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine IsBigO.of_bound 0 ?_
    have hNear : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hNear] with x hx
    have hOutside : x ∉ Ioi (1 : ℝ) := fun h => (mem_Iio.mp hx).not_gt (mem_Ioi.mp h)
    simp only [periodicRemainder, indicator_of_notMem hOutside, norm_zero, zero_mul, le_refl]
  have hNeg : (-s).re < 0 := by simpa only [neg_re, neg_lt_zero] using hs
  have hAbove : -s.re - 1 < (-s).re := by rw [neg_re]; linarith
  exact (mellin_differentiableAt_of_isBigO_rpow hLoc hTop hNeg hBot hAbove).comp s
    differentiableAt_id.neg

omit [NeZero q] in
private def seriesCoefficient (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ (n : ZMod q)

omit [NeZero q] in
private theorem sum_seriesCoefficient_eq (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k) = charPartialSum χ n := by
  rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
  simp [seriesCoefficient, charPartialSum]

private theorem integral_centeringTerm (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) ∧
      (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) =
        charMean χ / (s - 1) := by
  have hPower : (-s).re < -1 := by rw [neg_re]; linarith
  have hIntegrand (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) = charMean χ * (x : ℂ) ^ (-s) := by
    have hx0 : 0 < x := zero_lt_one.trans (Set.mem_Ioi.mp hx)
    have hProd : (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s) := by
      simpa only [sub_add_cancel, cpow_one] using
        (cpow_add (-s - 1) 1 (ofReal_ne_zero.mpr hx0.ne')).symm
    rw [← mul_assoc, hProd, mul_comm]
  constructor
  · have hInt : IntegrableOn (fun x : ℝ => charMean χ * (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt hPower zero_lt_one).const_mul (charMean χ)
    exact hInt.congr_fun (fun x hx => (hIntegrand x hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hIntegrand, integral_const_mul,
      integral_Ioi_cpow_of_lt hPower zero_lt_one]
    rw [show -s + 1 = -(s - 1) by ring]
    simp only [ofReal_one, one_cpow, div_neg, neg_div, neg_neg, mul_one_div]

/-- Abel summation on the half-plane of absolute convergence. -/
theorem LFunction_eq_centeredMellin_of_one_lt_re (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s =
      s * (remainderMellin χ s + charMean χ / (s - 1)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hDiff : ∀ x ∈ Ici (1 : ℝ), DifferentiableAt ℝ f x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le (Set.mem_Ici.mp hx)).ne'
      (neg_ne_zero.mpr hs0)).differentiableAt
  have hDerivLoc : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    have hNeg : (-s).re < 0 := by rw [neg_re]; linarith
    refine ((integrableOn_Ioi_deriv_ofReal_cpow (t := (1 / 2 : ℝ)) (by norm_num) hNeg).mono_set
      (fun x hx => ?_)).locallyIntegrableOn
    exact (by norm_num : (1 / 2 : ℝ) < 1).trans_le (Set.mem_Ici.mp hx)
  have hPowerLim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
  have hBoundary : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hPowerLim
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [f, norm_mul, Complex.ofReal_natCast, norm_natCast_cpow_of_pos hn, neg_re,
      sum_seriesCoefficient_eq]
    calc
      _ ≤ (n : ℝ) ^ (-s.re) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_charPartialSum_le χ n) (Real.rpow_nonneg n.cast_nonneg _)
      _ = _ := by
        rw [← Real.rpow_add_one (Nat.cast_ne_zero.mpr hn.ne'), neg_add_eq_sub]
  have hSumDom : (fun x : ℝ => ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k) =O[atTop]
      fun x : ℝ => x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [sum_seriesCoefficient_eq, one_mul, Real.norm_of_nonneg hx.le]
    exact (norm_charPartialSum_le χ _).trans (Nat.floor_le hx.le)
  have hDerivativeDom : (fun x : ℝ => deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k)
      =O[atTop] fun x : ℝ => x ^ (-s.re) := by
    refine ((isBigO_deriv_ofReal_cpow_const_atTop (-s)).mul hSumDom).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_re, ← Real.rpow_add_one hx.ne', sub_add_cancel]
  have hDominatingIntegral : IntegrableAtFilter (fun x : ℝ => x ^ (-s.re)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop _, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  have hAbel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (seriesCoefficient χ)
    (by simp [seriesCoefficient]) hDiff hDerivLoc hBoundary hDerivativeDom hDominatingIntegral
  have hCoeff (n : ℕ) : f n * seriesCoefficient χ n =
      LSeries.term (fun k : ℕ => χ (k : ZMod q)) s n := by
    by_cases hn : n = 0
    · subst n
      simp [seriesCoefficient]
    · simp [f, seriesCoefficient, hn, cpow_neg, div_eq_inv_mul]
  have hSum : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n,
      f k * seriesCoefficient χ k) atTop (𝓝 (LSeries (fun k : ℕ => χ (k : ZMod q)) s)) := by
    simp_rw [hCoeff, ← Nat.range_succ_eq_Icc_zero]
    exact (χ.LSeriesSummable_of_one_lt_re hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hSeriesIdentity : DirichletCharacter.LFunction χ s = (0 : ℂ) -
      ∫ x : ℝ in Ioi (1 : ℝ), deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact tendsto_nhds_unique hSum hAbel
  calc
    _ = (0 : ℂ) - ∫ x : ℝ in Ioi (1 : ℝ), (-s) *
        ((x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [hSeriesIdentity]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : x ≠ 0 := (zero_lt_one.trans (Set.mem_Ioi.mp hx)).ne'
      simp only [f, deriv_ofReal_cpow_const (-s) hx0, sum_seriesCoefficient_eq, mul_assoc]
    _ = s * (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [integral_const_mul, zero_sub, neg_mul, neg_neg]
    _ = _ := by
      have hSplit (x : ℝ) : (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊ =
          (x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) +
            (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) := by ring
      simp_rw [hSplit]
      rw [integral_add (weightedRemainder_integrableOn χ (zero_lt_one.trans hs))
        (integral_centeringTerm χ hs).1, ← remainderMellin_eq_integral, (integral_centeringTerm χ hs).2]

private theorem eq_on_right_halfPlane {f g : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ f z)
    (hg : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ g z)
    (hfg : ∀ z : ℂ, 1 < z.re → f z = g z) {s : ℂ} (hs : 0 < s.re) : f s = g s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUConnected : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage reCLM.toLinearMap).isPreconnected
  have hFA : AnalyticOnNhd ℂ f U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hUOpen
  have hGA : AnalyticOnNhd ℂ g U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hUOpen
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hAbsConv : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  have hEq : f =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [hAbsConv] with z hz
    exact hfg z hz
  exact hFA.eqOn_of_preconnected_of_eventuallyEq hGA hUConnected h2 hEq hs

/-- The centered Mellin representation of a nonprincipal L-function on the right half-plane. -/
theorem LFunction_eq_remainderMellin (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = s * remainderMellin χ s := by
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunction χ)
    (g := fun z : ℂ => z * remainderMellin χ z)
    (fun z _ => DirichletCharacter.differentiable_LFunction hχ z) ?_ ?_ hs
  · intro z hz
    exact differentiableAt_id.mul (differentiableAt_remainderMellin χ hz)
  · intro z hz
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    simp only [charMean_eq, ite_eq_right hχ, zero_div, add_zero]

end BMORModThree.Mellin
end

namespace BMORModThree
open Complex DirichletCharacter Finset MeasureTheory Set
open Mellin

theorem partial_eq (χ : DirichletCharacter ℂ 3) (hχ : χ≠1) (n : ℕ) :
    charPartialSum χ n = if n % 3=1 then 1 else 0 := by
  classical
  have red (k : ℕ) : integerRemainder χ k=charPartialSum χ k := by
    simp [integerRemainder,charMean_eq,hχ]
  have per (k : ℕ) : charPartialSum χ (k % 3)=charPartialSum χ k := by
    simpa only [red] using (integerRemainder_periodic χ).map_mod_nat k
  have two : charPartialSum χ 2=0 := by
    have h := per 3
    norm_num [charPartialSum,Finset.sum_range_succ] at h ⊢
    simpa [show (3 : ZMod 3)=0 by decide,χ.map_zero] using h.symm
  rw [←per n]
  have hn := Nat.mod_lt n (by decide : 0<3)
  generalize h : n % 3 = j at *
  interval_cases j <;> simp [charPartialSum,Finset.sum_range_succ] at * <;> assumption

theorem norm_remainder_le (χ : DirichletCharacter ℂ 3) (hχ : χ≠1)
    {s : ℂ} (hs : 0<s.re) : ‖remainderMellin χ s‖ ≤ 1/s.re := by
  rw [remainderMellin_eq_integral]
  have hp : -s.re-1 < -1 := by linarith
  have hI := integrableOn_Ioi_rpow_of_lt hp zero_lt_one
  refine (norm_integral_le_of_norm_le hI ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 := zero_lt_one.trans (mem_Ioi.mp hx)
    rw [norm_mul,norm_cpow_eq_rpow_re_of_pos hx0,sub_re,neg_re,one_re]
    classical
    rw [charMean_eq,ite_eq_right hχ,mul_zero,sub_zero,partial_eq χ hχ]
    split <;> simp [Real.rpow_nonneg hx0.le]
  · rw [integral_Ioi_rpow_of_lt hp zero_lt_one,show -s.re-1+1 = -s.re by ring,Real.one_rpow]
    simp

theorem norm_L_le (χ : DirichletCharacter ℂ 3) (hχ : χ≠1)
    {s : ℂ} (hs : 0<s.re) : ‖LFunction χ s‖ ≤ ‖s‖/s.re := by
  rw [LFunction_eq_remainderMellin χ hχ hs,norm_mul]
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (norm_remainder_le χ hχ hs) (norm_nonneg s)

/-- The first nonzero block of the nonnegative real Mellin integrand contributes 1/2. -/
theorem center_lower (χ : DirichletCharacter ℂ 3) (hχ : χ≠1) :
    1/2 ≤ (LFunction χ 1).re := by
  classical
  let g : ℝ → ℝ := fun x => if ⌊x⌋₊%3=1 then x^(-2:ℝ) else 0
  have hmeas : Measurable (fun x : ℝ => ⌊x⌋₊%3) :=
    (measurable_of_countable (fun n : ℕ => n % 3)).comp measurable_id.nat_floor
  have hm : MeasurableSet {x : ℝ | ⌊x⌋₊%3=1} := hmeas (measurableSet_singleton 1)
  have hgi : IntegrableOn g (Ioi 1) := by
    have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) zero_lt_one
    apply (hp.indicator hm).congr_fun _ measurableSet_Ioi
    intro x _
    by_cases hx : ⌊x⌋₊%3=1 <;> simp [g,hx]
  have hn : LFunction χ 1 = ((∫ x in Ioi (1:ℝ), g x : ℝ) : ℂ) := by
    rw [LFunction_eq_remainderMellin χ hχ (by norm_num),one_mul,
      remainderMellin_eq_integral,←integral_complex_ofReal (μ := volume.restrict (Ioi (1:ℝ))) (f := g)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0≤x := (zero_lt_one.trans (mem_Ioi.mp hx)).le
    rw [charMean_eq,ite_eq_right hχ,mul_zero,sub_zero,partial_eq χ hχ]
    dsimp [g]
    split
    · simp only [mul_one]
      rw [show (-1-1:ℂ)=((-2:ℝ):ℂ) by norm_num]
      exact (Complex.ofReal_cpow hx0 _).symm
    · simp
  rw [hn,ofReal_re]
  calc
    1/2 = ∫ x : ℝ in Ioo 1 2, x^(-2:ℝ) := by
      rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),
        integral_rpow (Or.inr ⟨by norm_num,by norm_num [uIcc_of_le (by norm_num : (1:ℝ)≤2)]⟩)]
      norm_num
    _ = ∫ x : ℝ in Ioo 1 2, g x := by
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hf : ⌊x⌋₊=1 := (Nat.floor_eq_iff (by linarith [hx.1] : 0≤x)).mpr (by
        norm_num; exact ⟨hx.1.le,hx.2⟩)
      simp [g,hf]
    _ ≤ _ := setIntegral_mono_set hgi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      dsimp [g]
      have hx0 : 0≤x := (zero_lt_one.trans (mem_Ioi.mp hx)).le
      split <;> first | exact Real.rpow_nonneg hx0 _ | exact le_rfl) (show Ioo (1:ℝ) 2 ⊆ Ioi 1 from fun x hx => hx.1).eventuallySubset

theorem deriv_le_seven (χ : DirichletCharacter ℂ 3) (hχ : χ≠1)
    (z : ℂ) (hz : z ∈ Metric.closedBall 1 (1/64)) : ‖deriv (LFunction χ) z‖ ≤ 7 := by
  have hb (w : ℂ) (hw : w ∈ Metric.sphere z (1/2)) : ‖LFunction χ w‖ ≤ 7/2 := by
    have d1 : dist w 1 ≤ 33/64 := by
      have h := dist_triangle w z 1
      rw [Metric.mem_sphere.mp hw] at h
      linarith [Metric.mem_closedBall.mp hz]
    have reL : 31/64 ≤ w.re := by
      have r := abs_le.mp (Complex.abs_re_le_norm (w-1))
      rw [←dist_eq_norm] at r
      simp only [sub_re,one_re] at r
      linarith [r.1]
    have n : ‖w‖ ≤ 97/64 := by
      have t := norm_le_norm_add_norm_sub (1:ℂ) w
      rw [norm_one,norm_sub_rev,←dist_eq_norm] at t
      linarith
    refine (norm_L_le χ hχ (by linarith : 0<w.re)).trans ((div_le_iff₀ (by linarith : 0<w.re)).mpr ?_)
    linarith
  have c := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ)<1/2) (differentiable_LFunction hχ).diffContOnCl hb
  linarith

theorem mod_three_zero_free_disk (χ : DirichletCharacter ℂ 3) (hχ : χ≠1)
    (s : ℂ) (hs : s ∈ Metric.closedBall 1 (1/64)) :
    25/64 ≤ ‖LFunction χ s‖ ∧ LFunction χ s ≠ 0 ∧ ‖deriv (LFunction χ) s/LFunction χ s‖ ≤ 448/25 := by
  have he : BMORProgression.poleRemoved χ = LFunction χ := by classical simp [BMORProgression.poleRemoved,hχ]
  have center : (1/2:ℝ) ≤ ‖LFunction χ 1‖ :=
    (center_lower χ hχ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have cert := BMORProgression.poleRemoved_disk_certificate χ 1 (r:=1/64) (m:=1/2) (B:=7)
    (by norm_num) (by norm_num) (by simpa only [he] using center)
    (by simpa only [he] using deriv_le_seven χ hχ) s hs
  norm_num [he] at cert ⊢
  exact cert

theorem exists_nonprincipal_mod_three : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  classical
  have h : Fintype.card (DirichletCharacter ℂ 3) = Nat.totient 3 := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 3
  exact Fintype.exists_ne_of_one_lt_card (by rw [h]; decide) 1

/-- The remainder integrand of the unique nonprincipal character of modulus three. -/
noncomputable def masked (s : ℂ) (x : ℝ) : ℂ :=
  if ⌊x⌋₊%3 = 1 then (x:ℂ)^(-s-1) else 0

theorem masked_formula (χ : DirichletCharacter ℂ 3) (hχ : χ≠1) (s : ℂ) (x : ℝ) :
    (x:ℂ)^(-s-1)*(charPartialSum χ ⌊x⌋₊ - (x:ℂ)*charMean χ)=masked s x := by
  classical
  rw [charMean_eq,ite_eq_right hχ,mul_zero,sub_zero,partial_eq χ hχ]
  unfold masked
  split <;> simp

theorem masked_integrable (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0<s.re) : IntegrableOn (masked s) (Ioi 1) := by
  exact (Mellin.weightedRemainder_integrableOn χ hs).congr_fun
    (fun x _ => masked_formula χ hχ s x) measurableSet_Ioi

theorem remainder_eq_masked (χ : DirichletCharacter ℂ 3) (hχ : χ≠1) (s : ℂ) :
    remainderMellin χ s = ∫ x : ℝ in Ioi 1, masked s x := by
  rw [remainderMellin_eq_integral]
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ => masked_formula χ hχ s x

theorem remainder_eq_head_add_tail (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0<s.re) :
    remainderMellin χ s = (∫ x : ℝ in Ioo 1 2, (x:ℂ)^(-s-1)) +
      ∫ x : ℝ in Ioi 4, masked s x := by
  have integ := masked_integrable χ hχ hs
  have cut (a b : ℝ) (ha : 1≤a) (hb : a≤b) :
      (∫ x : ℝ in Ioi a, masked s x) = (∫ x : ℝ in Ioo a b, masked s x) +
        ∫ x : ℝ in Ioi b, masked s x := by
    simpa only [intervalIntegral.integral_of_le hb,integral_Ioc_eq_integral_Ioo] using
      (intervalIntegral.integral_interval_add_Ioi (integ.mono_set (Ioi_subset_Ioi ha))
        (integ.mono_set (Ioi_subset_Ioi (ha.trans hb)))).symm
  have head : (∫ x : ℝ in Ioo 1 2, masked s x) = ∫ x : ℝ in Ioo 1 2, (x:ℂ)^(-s-1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have fl : ⌊x⌋₊=1 := (Nat.floor_eq_iff (by linarith [hx.1] : 0≤x)).mpr (by
      norm_num; exact ⟨hx.1.le,hx.2⟩)
    simp [masked,fl]
  have gap : (∫ x : ℝ in Ioo 2 4, masked s x) = 0 := by
    calc
      _ = ∫ _x : ℝ in Ioo 2 4, (0:ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        have lo : 2≤⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.1.le)
        have hi : ⌊x⌋₊<4 := (Nat.floor_lt (by linarith [hx.1] : 0≤x)).mpr (by exact_mod_cast hx.2)
        simp [masked,show ⌊x⌋₊%3≠1 by omega]
      _ = _ := by simp
  rw [remainder_eq_masked χ hχ,cut 1 2 (by norm_num) (by norm_num),cut 2 4 (by norm_num) (by norm_num),
    head,gap,zero_add]

/-- Cauchy's estimate for a circle of radius half the distance to the imaginary axis. -/
theorem deriv_le_right (χ : DirichletCharacter ℂ 3) (hχ : χ≠1)
    (z : ℂ) (hz : 0<z.re) :
    ‖deriv (LFunction χ) z‖ ≤ (4*‖z‖+2*z.re)/z.re^2 := by
  have hr : 0 < z.re/2 := by linarith
  have c := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := LFunction χ) (c := z) (C := (‖z‖+z.re/2)/(z.re/2))
    hr (differentiable_LFunction hχ).diffContOnCl (by
      intro w hw
      have e : ‖w-z‖=z.re/2 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hw
      have hl : z.re/2 ≤ w.re := by
        have a := (abs_le.mp (Complex.abs_re_le_norm (w-z))).1
        rw [sub_re,e] at a
        linarith
      have hn : ‖w‖ ≤ ‖z‖+z.re/2 := by
        simpa only [norm_sub_rev z w,e] using norm_le_norm_add_norm_sub z w
      exact (norm_L_le χ hχ (hr.trans_le hl)).trans
        (div_le_div₀ (by positivity) hn hr hl))
  exact c.trans_eq (by field_simp; ring)

theorem deriv_le_height_two (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    (z : ℂ) (hlo : 1/2≤z.re) (hhi : z.re≤1) (ht : |z.im|≤2) :
    ‖deriv (LFunction χ) z‖ ≤ 52 := by
  have hp : 0<z.re := by linarith
  have bound := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hp.le] at bound
  apply (deriv_le_right χ hχ z hp).trans
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith [sq_nonneg (z.re-1/2)]

end BMORModThree
end

section
namespace BMORModThree
open Set Complex MeasureTheory
open scoped Interval

private theorem rotated_head_point (s : ℂ) {x : ℝ} (hx : 0<x) :
    (Complex.exp ((s.im*Real.log (Real.sqrt 2):ℝ)*I) * (x:ℂ)^(-s-1)).re =
      x^(-s.re-1) * Real.cos (s.im*(Real.log (Real.sqrt 2)-Real.log x)) := by
  have nz : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero nz,←Complex.exp_add,Complex.exp_re,
    ←Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_I_re,Complex.mul_I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.sub_re,
    Complex.sub_im,Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,
    Complex.I_re,Complex.I_im,neg_zero,zero_mul,mul_zero,mul_one,zero_add,sub_zero,add_zero]
  congr 2 <;> ring

private theorem head_cos_lower {t x : ℝ} (ht : |t|≤2) (hx : x ∈ Icc (1:ℝ) 2) :
    151/200 ≤ Real.cos (t*(Real.log (Real.sqrt 2)-Real.log x)) := by
  have lx := Real.log_nonneg hx.1
  have l2 := Real.log_le_log (zero_lt_one.trans_le hx.1) hx.2
  have hlog : Real.log 2 ≤ 7/10 := by linarith [Real.log_two_lt_d9]
  have hdiff : |Real.log (Real.sqrt 2)-Real.log x| ≤ Real.log 2/2 := by
    rw [Real.log_sqrt (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  let u := t*(Real.log (Real.sqrt 2)-Real.log x)
  have hu : |u|≤7/10 := by
    rw [show |u| = |t| * |Real.log (Real.sqrt 2)-Real.log x| by exact abs_mul _ _]
    have h := mul_le_mul ht hdiff (abs_nonneg _) (by norm_num)
    linarith
  have hsq := mul_self_le_mul_self (abs_nonneg u) hu
  rw [abs_mul_abs_self] at hsq
  have hcos : 1-u^2/2 ≤ Real.cos u := Real.one_sub_sq_div_two_le_cos
  change 151/200 ≤ Real.cos u
  nlinarith

private theorem head_weight_mass :
    (∫ x in Ioc (1:ℝ) 2, x^(-3/2:ℝ)) = 2-Real.sqrt 2 := by
  rw [←intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),
    integral_rpow (Or.inr ⟨by norm_num,by norm_num [uIcc_of_le]⟩)]
  norm_num only [show (-3/2:ℝ)+1=-(1/2) by norm_num,Real.one_rpow,
    Real.rpow_neg (by norm_num : (0:ℝ)≤2),←Real.sqrt_eq_rpow]
  have hp : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem head_rotated_lower {s : ℂ} (hσ : 1/2 ≤ s.re) (ht : |s.im|≤2) :
    (2:ℝ)^(1/2-s.re)*(43/100) <
      (Complex.exp ((s.im*Real.log (Real.sqrt 2):ℝ)*I) *
        (∫ x in Ioc (1:ℝ) 2, (x:ℂ)^(-s-1))).re := by
  let A := (2:ℝ)^(1/2-s.re)
  let rot := Complex.exp ((s.im*Real.log (Real.sqrt 2):ℝ)*I)
  have hA : 0<A := Real.rpow_pos_of_pos (by norm_num) _
  have hr : (0:ℝ) ∉ [[(1:ℝ),2]] := by norm_num [uIcc_of_le]
  have hc : IntegrableOn (fun x : ℝ => (x:ℂ)^(-s-1)) (Ioc 1 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ)≤2)).mp
      (intervalIntegral.intervalIntegrable_cpow (Or.inr hr))
  have hw : IntegrableOn (fun x : ℝ => x^(-3/2:ℝ)) (Ioc 1 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ)≤2)).mp
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hr))
  have hi := hc.const_mul rot
  have lower (x : ℝ) (hx : x ∈ Ioc (1:ℝ) 2) :
      (A*(151/200))*x^(-3/2:ℝ) ≤ (rot*(x:ℂ)^(-s-1)).re := by
    have hp := zero_lt_one.trans hx.1
    rw [show (rot*(x:ℂ)^(-s-1)).re = _ from rotated_head_point s hp]
    have pw : A ≤ x^(1/2-s.re) := Real.rpow_le_rpow_of_nonpos hp hx.2 (by linarith)
    have w : A*x^(-3/2:ℝ) ≤ x^(-s.re-1) := by
      rw [show -s.re-1=(1/2-s.re)+(-3/2) by ring,Real.rpow_add hp]
      exact mul_le_mul_of_nonneg_right pw (Real.rpow_nonneg hp.le _)
    calc
      _ = (A*x^(-3/2:ℝ))*(151/200) := by ring
      _ ≤ _ := mul_le_mul w (head_cos_lower ht ⟨hx.1.le,hx.2⟩) (by norm_num) (Real.rpow_nonneg hp.le _)
  have hInt := setIntegral_mono_on (hw.const_mul (A*(151/200))) hi.re measurableSet_Ioc lower
  rw [integral_const_mul,head_weight_mass] at hInt
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hsqrt : Real.sqrt 2 < 10/7 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have strict : (43/100:ℝ)<151/200*(2-Real.sqrt 2) := by linarith
  change A*(43/100)< (rot * (∫ x in Ioc (1:ℝ) 2, (x:ℂ)^(-s-1))).re
  rw [←integral_const_mul]
  rw [integral_re hi] at hInt
  exact (show A*(43/100)<(A*(151/200))*(2-Real.sqrt 2) by
    rw [mul_assoc]; exact mul_lt_mul_of_pos_left strict hA).trans_le hInt

end BMORModThree
end

section
namespace BMORModThree
open DirichletCharacter Complex Set

theorem primitive_of_mod_three_nonprincipal {χ : DirichletCharacter ℂ 3} (hχ : χ≠1) :
    χ.IsPrimitive := by
  have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp χ.conductor_dvd_level
  exact h.resolve_left (fun H => hχ ((eq_one_iff_conductor_eq_one (χ := χ)).mpr H))

theorem gammaFactor_ne_zero_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0<s.re) : gammaFactor χ s ≠ 0 := by
  classical
  unfold gammaFactor
  split
  · exact Gammaℝ_ne_zero_of_re_pos hs
  · exact Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)

/-- Reflection transports nonvanishing across the center of the critical strip. -/
theorem reflect_nonvanishing {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {s : ℂ} (hs : 0<s.re) (hu : s.re<1)
    (href : LFunction χ⁻¹ (1-s)≠0) : LFunction χ s ≠ 0 := by
  have ns : s ≠ 0 := fun e => by simp [e] at hs
  have ns' : 1-s ≠ 0 := sub_ne_zero.mpr fun e => by simp [←e] at hu
  have hcomp : completedLFunction χ⁻¹ (1-s) ≠ 0 := by
    intro h
    apply href
    rw [LFunction_eq_completed_div_gammaFactor _ _ (.inl ns'),h,zero_div]
  have hpwr : (q : ℂ) ^ ((1-s)-(1/2:ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne q))
  have hFE := hp.completedLFunction_one_sub (1-s)
  rw [show 1-(1-s)=s by ring] at hFE
  rw [LFunction_eq_completed_div_gammaFactor _ _ (.inl ns),hFE]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hpwr (rootNumber_ne_zero hp)) hcomp)
    (gammaFactor_ne_zero_of_re_pos χ hs)

/-- The half strip includes the critical line; the functional equation handles its left side. -/
theorem reflect_mod_three_band {T : ℝ}
    (H : ∀ (χ : DirichletCharacter ℂ 3), χ≠1 → ∀ s : ℂ,
      1/2≤s.re → s.re<1 → |s.im|≤T → LFunction χ s ≠ 0)
    (χ : DirichletCharacter ℂ 3) (hχ : χ≠1) {s : ℂ}
    (hs : 0<s.re) (hu : s.re<1) (ht : |s.im|≤T) : LFunction χ s ≠ 0 := by
  by_cases h : 1/2≤s.re
  · exact H χ hχ s h hu ht
  apply reflect_nonvanishing χ (primitive_of_mod_three_nonprincipal hχ) hs hu
  apply H χ⁻¹ (fun e => hχ (inv_eq_one.mp e))
  · simp only [sub_re,one_re]; linarith
  · simp only [sub_re,one_re]; linarith
  · simpa only [sub_im,one_im,zero_sub,abs_neg] using ht

/-- Nontrivial zeros of a character of modulus three within a fixed height. -/
def lowZeros (χ : DirichletCharacter ℂ 3) (T : ℝ) : Set ℂ :=
  {s | 0<s.re ∧ s.re<1 ∧ |s.im|≤T ∧ LFunction χ s = 0}

theorem lowZeros_empty_iff (χ : DirichletCharacter ℂ 3) (T : ℝ) :
    lowZeros χ T=∅ ↔ ∀ s : ℂ, 0<s.re → s.re<1 → |s.im|≤T → LFunction χ s≠0 := by
  constructor
  · intro h s hlo hhi ht hz
    have hm : s∈lowZeros χ T := ⟨hlo,hhi,ht,hz⟩
    simp only [h,Set.notMem_empty] at hm
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨hlo,hhi,ht,hz⟩
    exact h s hlo hhi ht hz

theorem lowZeros_empty_of_half_band {T : ℝ}
    (H : ∀ (χ : DirichletCharacter ℂ 3), χ≠1 → ∀ s : ℂ,
      1/2≤s.re → s.re<1 → |s.im|≤T → LFunction χ s ≠ 0)
    (χ : DirichletCharacter ℂ 3) (hχ : χ≠1) : lowZeros χ T=∅ :=
  (lowZeros_empty_iff χ T).mpr fun _ => reflect_mod_three_band H χ hχ

theorem inverse_eq_self_mod_three (χ : DirichletCharacter ℂ 3) : χ⁻¹=χ := by
  have h : Nat.card (DirichletCharacter ℂ 3) = 2 :=
    (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 3).trans (by decide)
  have sq : χ*χ=1 := by simpa only [h,pow_two] using (pow_card_eq_one' (x := χ))
  exact (eq_inv_of_mul_eq_one_right sq).symm

theorem lowZeros_empty_of_fixed_half_band (χ : DirichletCharacter ℂ 3) (hχ : χ≠1) {T : ℝ}
    (H : ∀ s : ℂ, 1/2≤s.re → s.re<1 → |s.im|≤T → LFunction χ s ≠ 0) :
    lowZeros χ T=∅ := by
  apply (lowZeros_empty_iff χ T).mpr
  intro s hs hu ht
  by_cases h : 1/2≤s.re
  · exact H s h hu ht
  apply reflect_nonvanishing χ (primitive_of_mod_three_nonprincipal hχ) hs hu
  rw [inverse_eq_self_mod_three χ]
  apply H
  · simp only [sub_re,one_re]; linarith
  · simp only [sub_re,one_re]; linarith
  · simpa only [sub_im,one_im,zero_sub,abs_neg] using ht

end BMORModThree
end

section
noncomputable section
open MeasureTheory Set
open scoped Interval

namespace BMORModThree.HeightTwo

/-- The modulus-three mask applied to the integrable comparison density. -/
def weight (x : ℝ) : ℝ := if ⌊x⌋₊ % 3 = 1 then x ^ (-(3/2) : ℝ) else 0

theorem weight_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn weight (Ioi a) := by
  have hm : Measurable (fun x : ℝ => ⌊x⌋₊ % 3) :=
    (measurable_of_countable (fun n : ℕ => n % 3)).comp measurable_id.nat_floor
  have hs : MeasurableSet {x : ℝ | ⌊x⌋₊ % 3 = 1} := hm (measurableSet_singleton 1)
  have hw : weight = {x : ℝ | ⌊x⌋₊ % 3 = 1}.indicator (fun x : ℝ => x ^ (-(3/2) : ℝ)) := by
    funext x
    by_cases h : ⌊x⌋₊ % 3 = 1 <;> simp [weight, Set.indicator, h]
  rw [hw]
  exact
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2) : ℝ) < -1) ha).indicator hs

theorem weight_three {x : ℝ} (hx : 0 < x) :
    weight x + weight (x+1) + weight (x+2) ≤ x ^ (-(3/2) : ℝ) := by
  have hf : ⌊x+(2:ℝ)⌋₊ = ⌊x⌋₊+2 := by
    exact_mod_cast Nat.floor_add_natCast hx.le 2
  have h1 := Real.rpow_le_rpow_of_nonpos hx (show x ≤ x+1 by linarith)
    (by norm_num : (-(3/2) : ℝ) ≤ 0)
  have h2 := Real.rpow_le_rpow_of_nonpos hx (show x ≤ x+2 by linarith)
    (by norm_num : (-(3/2) : ℝ) ≤ 0)
  simp only [weight, Nat.floor_add_one hx.le, hf]
  split_ifs <;> first | omega | linarith

private theorem shifted (k : ℝ) (hk : 0 ≤ k) (hk2 : k ≤ 2) :
    IntegrableOn (fun x => weight (x+k)) (Ioi (5:ℝ)) ∧
    ∫ x in Ioi (5:ℝ), weight (x+k) = ∫ x in Ioi (5:ℝ), weight x := by
  have hi := weight_integrable (show 0 < 5+k by linarith)
  have ht : (fun x : ℝ => x+k) ⁻¹' Ioi (5+k) = Ioi (5:ℝ) := by
    ext x
    simp only [mem_preimage, mem_Ioi, add_lt_add_iff_right]
  have hp := measurePreserving_add_right (volume : Measure ℝ) k
  have he := measurableEmbedding_addRight k
  constructor
  · simpa only [ht, Function.comp_def] using (hp.integrableOn_comp_preimage he).mpr hi
  · have hc := hp.setIntegral_preimage_emb he weight (Ioi (5+k))
    rw [ht] at hc
    rw [hc]
    have hzero : ∫ x in (5:ℝ)..5+k, weight x = 0 := by
      rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have h5 : 5 ≤ ⌊x⌋₊ := (Nat.le_floor (by linarith [hx.1] : (5:ℝ) ≤ x))
      have h7 : ⌊x⌋₊ < 7 := (Nat.floor_lt (by linarith [hx.1] : 0 ≤ x)).mpr
        (by push_cast; linarith [hx.2])
      simp [weight, show ⌊x⌋₊ % 3 ≠ 1 by omega]
    simpa only [hzero, zero_add] using intervalIntegral.integral_interval_add_Ioi
      (weight_integrable (by norm_num : (0:ℝ) < 5)) hi

/-- Past 5, summing the three translates of the mask costs at most one unmasked tail. -/
theorem weight_tail_five :
    3 * (∫ x in Ioi (5:ℝ), weight x) ≤ ∫ x in Ioi (5:ℝ), x ^ (-(3/2) : ℝ) := by
  obtain ⟨h1, e1⟩ := shifted 1 (by norm_num) (by norm_num)
  obtain ⟨h2, e2⟩ := shifted 2 (by norm_num) (by norm_num)
  have hi := weight_integrable (by norm_num : (0:ℝ) < 5)
  have bound := integral_mono_ae ((hi.add h1).add h2)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2) : ℝ) < -1)
      (by norm_num : (0:ℝ)<5)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact weight_three (lt_trans (by norm_num : (0:ℝ)<5) hx))
  simp only [Pi.add_apply] at bound
  rw [integral_add (f:=fun x => weight x + weight (x+1)) (g:=fun x => weight (x+2))
      (hi.add h1) h2, integral_add hi h1, e1, e2] at bound
  linarith

private theorem density_tail {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi b, x ^ (-(3/2) : ℝ)) = 2 / Real.sqrt b := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3/2) : ℝ) < -1) hb]
  rw [show (-(3/2)+1 : ℝ) = -(1/2) by ring, Real.rpow_neg hb.le, ←Real.sqrt_eq_rpow]
  ring

theorem weight_tail_four :
    (∫ x in Ioi (4:ℝ), weight x) ≤ 1 - 4 / (3 * Real.sqrt 5) := by
  let f : ℝ → ℝ := fun x => x ^ (-(3/2) : ℝ)
  have hi {b : ℝ} (hb : 0<b) : IntegrableOn f (Ioi b) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hb
  have eh := intervalIntegral.integral_interval_add_Ioi
    (weight_integrable (by norm_num : (0:ℝ)<4)) (weight_integrable (by norm_num : (0:ℝ)<5))
  have ed := intervalIntegral.integral_interval_add_Ioi (hi (by norm_num : (0:ℝ)<4))
    (hi (by norm_num : (0:ℝ)<5))
  have head : ∫ x in (4:ℝ)..5, weight x ≤ ∫ x in (4:ℝ)..5, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (4:ℝ) ≤ 5),
      intervalIntegral.integral_of_le (by norm_num : (4:ℝ) ≤ 5)]
    apply setIntegral_mono_on ((weight_integrable (by norm_num : (0:ℝ)<4)).mono_set Ioc_subset_Ioi_self)
      ((hi (by norm_num : (0:ℝ)<4)).mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
    intro x hx
    dsimp [weight, f]
    split <;> first | rfl | exact Real.rpow_nonneg (by linarith [hx.1]) _
  have tail := weight_tail_five
  have ef4 : (∫ x in Ioi (4:ℝ), f x)=1 := by
    rw [show (∫ x in Ioi (4:ℝ), f x)=_ from density_tail (by norm_num)]
    have hs : Real.sqrt 4 = 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 4 by norm_num), Real.sqrt_nonneg 4]
    rw [hs]
    norm_num
  have ef5 : (∫ x in Ioi (5:ℝ), f x)=2 / Real.sqrt 5 := density_tail (by norm_num)
  change 3 * (∫ x in Ioi (5:ℝ), weight x) ≤ ∫ x in Ioi (5:ℝ), f x at tail
  rw [ef4,ef5] at ed
  rw [ef5] at tail
  rw [show 4 / (3 * Real.sqrt 5) = (2/3)*(2 / Real.sqrt 5) by ring]
  linarith

theorem norm_tail_le (s : ℂ) (h : 1/2 ≤ s.re) :
    ‖∫ x in Ioi (4:ℝ), BMORModThree.masked s x‖ ≤
      (2:ℝ)^(1/2-s.re) * (1 - 4 / (3 * Real.sqrt 5)) := by
  let A : ℝ := (2:ℝ)^(1/2-s.re)
  have hA : 0 ≤ A := Real.rpow_nonneg (by norm_num) _
  have hi := (weight_integrable (by norm_num : (0:ℝ)<4)).const_mul A
  calc
    _ ≤ ∫ x in Ioi (4:ℝ), A * weight x := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans (by norm_num : (0:ℝ)<4) hx
      have hx2 : 2 ≤ x := le_trans (by norm_num : (2:ℝ)≤4) hx.le
      simp only [BMORModThree.masked, weight]
      split
      · rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.neg_re, Complex.one_re,
            show -s.re-1 = 1/2-s.re + -(3/2) by ring, Real.rpow_add hx0]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (by norm_num) hx2 (by linarith))
          (Real.rpow_nonneg hx0.le _)
      · simp
    _ = A * (∫ x in Ioi (4:ℝ), weight x) := integral_const_mul A weight
    _ ≤ _ := mul_le_mul_of_nonneg_left weight_tail_four hA

theorem norm_L_lower_of_head (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    (s : ℂ) (hσ : 1/2 ≤ s.re)
    (head : (2:ℝ)^(1/2-s.re)*(43/100) <
      (Complex.exp ((s.im*Real.log (Real.sqrt 2):ℝ)*Complex.I) *
        (∫ x in Set.Ioc (1:ℝ) 2, (x:ℂ)^(-s-1))).re) :
    ‖s‖ * ((2:ℝ)^(1/2-s.re)*(61/2700)) < ‖DirichletCharacter.LFunction χ s‖ := by
  let A : ℝ := (2:ℝ) ^ (1/2-s.re)
  let H : ℂ := ∫ x in Set.Ioo (1:ℝ) 2, (x:ℂ)^(-s-1)
  let T : ℂ := ∫ x in Set.Ioi (4:ℝ), BMORModThree.masked s x
  let R : ℂ := Complex.exp ((s.im*Real.log (Real.sqrt 2):ℝ)*Complex.I)
  have hA : 0 ≤ A := Real.rpow_nonneg (by norm_num) _
  have hR : ‖R‖ = 1 := by simp [R,Complex.norm_exp,Complex.mul_re]
  rw [integral_Ioc_eq_integral_Ioo] at head
  change A*(43/100) < (R*H).re at head
  have major : A*(43/100) < ‖H‖ := by
    have bound := (le_abs_self _).trans (Complex.abs_re_le_norm (R*H))
    rw [norm_mul,hR,one_mul] at bound
    exact head.trans_le bound
  have sqrt5 : Real.sqrt 5 ≤ 9/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  have frac : 1 - 4/(3*Real.sqrt 5) ≤ (11/27:ℝ) := by
    have hp : 0 < 3 * Real.sqrt 5 := by positivity
    nlinarith [(le_div_iff₀ hp).mpr (show (16/27:ℝ)*(3*Real.sqrt 5) ≤ 4 by linarith)]
  have tail : ‖T‖ ≤ A*(11/27) :=
    (norm_tail_le s hσ).trans (mul_le_mul_of_nonneg_left frac hA)
  have triangle : ‖H‖ ≤ ‖H+T‖ + ‖T‖ := by simpa using norm_sub_le (H+T) T
  have remain : A*(61/2700) < ‖H+T‖ := by linarith
  have hs : 0<s.re := by linarith
  have hsn : 0<‖s‖ := norm_pos_iff.mpr (by intro e; simp [e] at hs)
  rw [BMORModThree.Mellin.LFunction_eq_remainderMellin χ hχ hs,
    BMORModThree.remainder_eq_head_add_tail χ hχ hs,norm_mul]
  exact mul_lt_mul_of_pos_left remain hsn

theorem norm_L_gt_one_div_two_hundred_of_head (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    (s : ℂ) (hσ : 1/2 ≤ s.re) (hσ' : s.re ≤ 1)
    (head : (2:ℝ)^(1/2-s.re)*(43/100) <
      (Complex.exp ((s.im*Real.log (Real.sqrt 2):ℝ)*Complex.I) *
        (∫ x in Set.Ioc (1:ℝ) 2, (x:ℂ)^(-s-1))).re) :
    1/200 < ‖DirichletCharacter.LFunction χ s‖ := by
  have hs : 1/2 ≤ ‖s‖ := hσ.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have hA : 1/2 ≤ (2:ℝ)^(1/2-s.re) := by
    calc
      (1/2:ℝ) = (2:ℝ)^(-1:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hc : (1/2:ℝ) * ((1/2 : ℝ)*(61/2700)) ≤ ‖s‖ * ((2:ℝ)^(1/2-s.re)*(61/2700)) :=
    mul_le_mul hs (mul_le_mul_of_nonneg_right hA (by norm_num)) (by norm_num) (norm_nonneg _)
  exact lt_trans (by norm_num : (1/200:ℝ) < (1/2)*((1/2)*(61/2700)))
    (hc.trans_lt (norm_L_lower_of_head χ hχ s hσ head))

theorem norm_L_lower (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    {s : ℂ} (hσ : 1/2 ≤ s.re) (hσ' : s.re ≤ 1) (ht : |s.im| ≤ 2) :
    1/200 < ‖DirichletCharacter.LFunction χ s‖ :=
  norm_L_gt_one_div_two_hundred_of_head χ hχ s hσ hσ' (BMORModThree.head_rotated_lower hσ ht)

theorem half_strip (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    {s : ℂ} (hσ : 1/2 ≤ s.re) (hσ' : s.re < 1) (ht : |s.im| ≤ 2) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  norm_pos_iff.mp (lt_trans (by norm_num) (norm_L_lower χ hχ hσ hσ'.le ht))

theorem low_zeros_empty (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    BMORModThree.lowZeros χ 2 = ∅ :=
  BMORModThree.lowZeros_empty_of_half_band (fun ψ hp _ hs hu ht => half_strip ψ hp hs hu ht) χ hχ

/-- The sum vanishes for every possible choice of zero multiplicities. -/
theorem low_zero_weighted_sum (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1)
    (multiplicity : ℂ → ℕ) :
    (∑ᶠ z : BMORModThree.lowZeros χ 2, (multiplicity z : ℝ) /
      Real.sqrt ((z : ℂ).im ^ 2 + 1/4)) = 0 := by
  have : IsEmpty (BMORModThree.lowZeros χ 2) :=
    ⟨fun z => (Set.eq_empty_iff_forall_notMem.mp (low_zeros_empty χ hχ)) z.val z.property⟩
  exact finsum_of_isEmpty _

theorem low_zero_count (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    Nat.card (BMORModThree.lowZeros χ 2) = 0 := by
  rw [low_zeros_empty χ hχ]
  simp

end BMORModThree.HeightTwo
end
end

section
namespace BMORProgression
open Complex Set DirichletCharacter

theorem eulerLevelFactor_ne_zero {d p : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (hp : Nat.Prime p) {s : ℂ} (hs : 0<s.re) : 1 - χ p*(p:ℂ)^(-s) ≠ 0 := by
  have h1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hw : ‖(p:ℂ)^(-s)‖ < 1 := by
    rw [show (p:ℂ) = ((p:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans h1),Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.mpr hs)
  have less : ‖χ p*(p:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans_lt hw
  exact sub_ne_zero.mpr (fun h => by rw [←h,norm_one] at less; exact lt_irrefl _ less)

theorem LFunction_changeLevel_zero_iff {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q)
    (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : 0<s.re) (hp : χ≠1 ∨ s≠1) :
    LFunction (changeLevel hd χ) s = 0 ↔ LFunction χ s = 0 := by
  rw [LFunction_changeLevel hd χ hp]
  have nz : (∏ p ∈ q.primeFactors, (1-χ p*(p:ℂ)^(-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p h => eulerLevelFactor_ne_zero χ (Nat.prime_of_mem_primeFactors h) hs
  simp [nz]

theorem LFunction_changeLevel_order {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q)
    (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : 0<s.re) (hp : s≠1) :
    analyticOrderAt (LFunction (changeLevel hd χ)) s = analyticOrderAt (LFunction χ) s := by
  let g : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - χ p*(p:ℂ)^(-z))
  have eq : LFunction (changeLevel hd χ) =ᶠ[nhds s] LFunction χ * g := by
    filter_upwards [eventually_ne_nhds hp] with z hz using LFunction_changeLevel hd χ (.inr hz)
  have hL : DifferentiableOn ℂ (LFunction χ) ({1}:Set ℂ)ᶜ := fun z hz =>
    (differentiableAt_LFunction χ z (.inl hz)).differentiableWithinAt
  have ag : Differentiable ℂ g := by
    unfold g
    apply Differentiable.fun_finsetProd
    intro p h
    have hn : (p:ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors h).ne_zero
    have cp : Differentiable ℂ (fun z : ℂ => (p:ℂ)^z) := fun _ =>
      (Complex.hasStrictDerivAt_const_cpow (.inl hn)).hasDerivAt.differentiableAt
    exact (differentiable_const _).sub ((differentiable_const _).mul (cp.comp differentiable_id.neg))
  have nz : g s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p h =>
    eulerLevelFactor_ne_zero χ (Nat.prime_of_mem_primeFactors h) hs
  rw [analyticOrderAt_congr eq,analyticOrderAt_mul (hL.analyticOnNhd isClosed_singleton.isOpen_compl s hp)
    (ag.analyticAt _), (ag.analyticAt _).analyticOrderAt_eq_zero.mpr nz,add_zero]

theorem primitive_order_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0<s.re) (hp : s≠1) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    analyticOrderNatAt (LFunction χ) s = analyticOrderNatAt (LFunction χ.primitiveCharacter) s := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [analyticOrderNatAt,changeLevel_primitiveCharacter] using
    congrArg ENat.toNat (LFunction_changeLevel_order χ.conductor_dvd_level χ.primitiveCharacter hs hp)

theorem modThree_induced_lowZeros_empty {q : ℕ} [NeZero q] (h3 : 3∣q)
    (χ : DirichletCharacter ℂ 3) (hc : χ ≠ 1) :
    {s : ℂ | 0<s.re ∧ s.re<1 ∧ |s.im|≤2 ∧ LFunction (changeLevel h3 χ) s = 0} = ∅ := by
  have hbase := (BMORModThree.lowZeros_empty_iff χ 2).mp (BMORModThree.HeightTwo.low_zeros_empty χ hc)
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro s ⟨hlo,hhi,ht,hz⟩
  exact hbase s hlo hhi ht ((LFunction_changeLevel_zero_iff h3 χ hlo (.inl hc)).mp hz)

theorem exists_induced_lowZeros_empty {q : ℕ} [NeZero q] (h3 : 3∣q) :
    ∃ χ : DirichletCharacter ℂ q, χ≠1 ∧
      {s : ℂ | 0<s.re ∧ s.re<1 ∧ |s.im|≤2 ∧ LFunction χ s = 0} = ∅ := by
  obtain ⟨χ,hχ⟩ := BMORModThree.exists_nonprincipal_mod_three
  exact ⟨changeLevel h3 χ, fun h => hχ ((changeLevel_eq_one_iff h3).mp h),
    modThree_induced_lowZeros_empty h3 χ hχ⟩

theorem principal_zero_iff_zeta {q : ℕ} [NeZero q] {s : ℂ} (hs : 0<s.re) (hp : s≠1) :
    LFunction (1 : DirichletCharacter ℂ q) s = 0 ↔ riemannZeta s = 0 := by
  change LFunctionTrivChar q s = 0 ↔ _
  rw [LFunctionTrivChar_eq_mul_riemannZeta hp]
  have nz : (∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p h
    have pp : Nat.Prime p := Nat.prime_of_mem_primeFactors h
    have h1 : (1:ℝ)<p := by exact_mod_cast pp.one_lt
    have hw : ‖(p:ℂ)^(-s)‖ < 1 := by
      rw [show (p:ℂ) = ((p:ℝ):ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans h1),Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.mpr hs)
    exact sub_ne_zero.mpr (fun e => by rw [←e,norm_one] at hw; exact lt_irrefl _ hw)
  simp [nz]

end BMORProgression
end

section
/-!
Euler–Maclaurin source adapted to version 4.36 from Salvatore Mercuri's Apache-2.0-licensed Zeta project.
https://github.com/smmercuri/zeta/tree/4704234df2d97563936adcaf0b89e2f8955389f9/Zeta
The original copyright headers are reproduced for each adapted file.
The changes combine the five Mathlib-only source files and adapt the analytic-continuation
proof to version 4.36. The final BMORZetaHeight section specializes the bounds at cutoff 1.
-/
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/




/-!
# The Euler–Maclaurin summation formula

The Euler–Maclaurin summation formula for a function `f : ℝ → E` valued in a real Banach space
`E` (blueprint `euler_maclaurin.tex`). The Bernoulli kernel acts on the integrand as a *real*
scalar, so the real- and complex-valued formulas are one and the same theorem; the file
`Zeta/Summation/Complex.lean` carries only the `ℂ`-flavoured restatement.

## Main definitions

- `eulerMaclaurinRemainder`: the periodized-Bernoulli remainder `R_p(f; a, b)`.

## Main results

- `eulerMaclaurin_sum_eq`: the Euler–Maclaurin summation formula with that remainder.

The tower lemmas leading to `eulerMaclaurin_sum_eq` are `private`.
-/
section


open MeasureTheory

open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


/-- Per-interval Euler–Maclaurin step: the trapezoidal rule with remainder on the unit
interval `[n, n+1]`, for real `n`:
`∫ₙⁿ⁺¹ f = (f n + f (n+1))/2 - ∫ₙⁿ⁺¹ B₁(x - n) · f'(x) dx`. -/
private theorem integral_interval_eq {f f' : ℝ → E} {n : ℝ}
    (hf : ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume n (n + 1)) :
    ∫ x in n..(n + 1), f x
      = (2⁻¹ : ℝ) • (f n + f (n + 1)) - ∫ x in n..(n + 1), bernoulliFun 1 (x - n) • f' x := by
  -- Integration by parts with `u = B₁(· - n)`, `u' = 1`, `v = f`, `v' = f'`.
  have hu : ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (fun y ↦ bernoulliFun 1 (y - n)) ((fun _ ↦ (1 : ℝ)) x) x := by
    intro x _
    have hcomp := (hasDerivAt_bernoulliFun 1 (x - n)).comp x ((hasDerivAt_id x).sub_const n)
    simp only [Nat.cast_one, Nat.sub_self, bernoulliFun_zero, mul_one] at hcomp
    exact hcomp
  have key := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu hf intervalIntegrable_const hf'
  simp only [add_sub_cancel_left, sub_self, bernoulliFun_one, one_smul] at key
  simp only [bernoulliFun_one]
  rw [key]
  module

/-- Unit-interval Euler–Maclaurin step: the case `n = 0` of `integral_interval_eq`. -/
private theorem integral_unitInterval_eq {f f' : ℝ → E}
    (hf : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume 0 1) :
    ∫ x in (0 : ℝ)..1, f x
      = (2⁻¹ : ℝ) • (f 0 + f 1) - ∫ x in (0 : ℝ)..1, bernoulliFun 1 x • f' x := by
  have h := integral_interval_eq (n := 0) (f := f) (f' := f')
    (by simpa using hf) (by simpa using hf')
  simpa only [zero_add, sub_zero] using h

/-- Order-raising recurrence for the Euler–Maclaurin tower: the order-`q` remainder integral
over `[n, n+1]` in terms of the order-`(q+1)` one, for `q ≠ 0`. -/
private theorem integral_bernoulliFun_smul_eq {g g' : ℝ → E} {n : ℝ} {q : ℕ} (hq : q ≠ 0)
    (hg : ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' volume n (n + 1)) :
    ∫ x in n..(n + 1), bernoulliFun q (x - n) • g x
      = ((bernoulli (q + 1) : ℝ) / ((q : ℝ) + 1)) • (g (n + 1) - g n)
        - (1 / ((q : ℝ) + 1)) • ∫ x in n..(n + 1), bernoulliFun (q + 1) (x - n) • g' x := by
  have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
  -- The antiderivative `u(x) = B_{q+1}(x - n)/(q+1)` has `u'(x) = B_q(x - n)`.
  have hu : ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (fun y ↦ bernoulliFun (q + 1) (y - n) / ((q : ℝ) + 1))
        (bernoulliFun q (x - n)) x := by
    intro x _
    have hcomp := ((hasDerivAt_bernoulliFun (q + 1) (x - n)).comp x
      ((hasDerivAt_id x).sub_const n)).div_const ((q : ℝ) + 1)
    have hval : ((q + 1 : ℕ) : ℝ) * bernoulliFun ((q + 1) - 1) (x - n) * 1 / ((q : ℝ) + 1)
        = bernoulliFun q (x - n) := by
      rw [show (q + 1) - 1 = q by lia, mul_one]; push_cast
      exact mul_div_cancel_left₀ _ hq1
    rwa [hval] at hcomp
  have hu' : IntervalIntegrable (fun x ↦ bernoulliFun q (x - n)) volume n (n + 1) :=
    (by fun_prop : Continuous fun x ↦ bernoulliFun q (x - n)).intervalIntegrable _ _
  have key := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu hg hu' hg'
  simp only [add_sub_cancel_left, sub_self, bernoulliFun_eval_zero,
    bernoulliFun_endpoints_eq_of_ne_one (show q + 1 ≠ 1 by lia)] at key
  -- Factor the constant `1/(q+1)` out of the order-`(q+1)` integral.
  have hfac : (∫ x in n..(n + 1), (bernoulliFun (q + 1) (x - n) / ((q : ℝ) + 1)) • g' x)
      = ((q : ℝ) + 1)⁻¹ • ∫ x in n..(n + 1), bernoulliFun (q + 1) (x - n) • g' x := by
    simp_rw [div_eq_inv_mul, mul_smul, intervalIntegral.integral_smul]
  rw [hfac] at key
  rw [one_div, smul_sub, key]
  module

/-- Per-interval Euler–Maclaurin tower (raw form): for a family `F 0, …, F p` on `[n, n+1]`
with `F (q+1)` the derivative of `F q`,
`∫ₙⁿ⁺¹ F 0 = (F 0 n + F 0 (n+1))/2 + ∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · ΔF q`
`+ (-1)^p/p! · ∫ₙⁿ⁺¹ B_p(x-n)·F p`, with `ΔF q = F q (n+1) - F q n`.
This is the tower before the even/odd collapse of the Bernoulli sum. -/
private theorem integral_interval_eq_tower {n : ℝ} (F : ℕ → ℝ → E) {p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume n (n + 1)) :
    ∫ x in n..(n + 1), F 0 x
      = (2⁻¹ : ℝ) • (F 0 n + F 0 (n + 1))
        + ∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (n + 1) - F q n)
        + ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∫ x in n..(n + 1), bernoulliFun p (x - n) • F p x := by
  revert hderiv hF_int
  induction p, hp using Nat.le_induction with
  | base =>
    intro hderiv hF_int
    have hbase := integral_interval_eq (f := F 0) (f' := F 1)
      (hderiv 0 one_pos) (hF_int 1 one_pos le_rfl)
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one]
    rw [hbase]
    module
  | succ p hp ih =>
    intro hderiv hF_int
    have IH := ih (fun q hq ↦ hderiv q (Nat.lt_succ_of_lt hq))
      (fun q hq0 hqp ↦ hF_int q hq0 (hqp.trans (Nat.le_succ p)))
    have hrec := integral_bernoulliFun_smul_eq (g := F p) (g' := F (p + 1)) (n := n) (q := p)
      (Nat.one_le_iff_ne_zero.mp hp) (hderiv p (Nat.lt_succ_self p))
      (hF_int (p + 1) (Nat.succ_pos p) le_rfl)
    rw [Finset.sum_Ico_succ_top (by lia : 1 ≤ p), IH, hrec, pow_succ, Nat.factorial_succ]
    have hp0 : (p ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
    have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    match_scalars <;> field_simp

/-- Each unit subinterval `[a+k, a+k+1]` (`k < N`) sits inside `[a, a+N]`. -/
private theorem uIcc_add_natCast_subset_uIcc (a : ℝ) {N k : ℕ} (hk : k < N) :
    Set.uIcc (a + (k : ℝ)) (a + (k : ℝ) + 1) ⊆ Set.uIcc a (a + N) := by
  have hk1 : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  apply Set.uIcc_subset_uIcc <;> rw [Set.mem_uIcc] <;> left <;> constructor <;> linarith

/-- Global Euler–Maclaurin tower (raw form): the per-interval tower summed over the `N` unit
intervals `[a+n, a+n+1]`, with the Bernoulli boundary sum telescoped:
`∫ₐ^{a+N} F 0 = ∑_{n<N} (F 0 (a+n) + F 0 (a+n+1))/2
  + ∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · (F q (a+N) - F q a)
  + (-1)^p/p! · ∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·F p`. -/
private theorem integral_eq_tower_sum {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∫ x in a..(a + N), F 0 x
      = (∑ n ∈ Finset.range N, (2⁻¹ : ℝ) • (F 0 (a + n) + F 0 (a + n + 1)))
        + (∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a))
        + ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  -- Each unit subinterval `[a+k, a+k+1]` sits inside `[a, a+N]`.
  have hsub : ∀ k, k < N → Set.uIcc (a + (k : ℝ)) (a + (k : ℝ) + 1) ⊆ Set.uIcc a (a + N) :=
    fun _ hk ↦ uIcc_add_natCast_subset_uIcc a hk
  -- `F 0` is continuous on `[a, a+N]`, so its unit-interval integrals concatenate.
  have hcont0 : ContinuousOn (F 0) (Set.uIcc a (a + N)) := fun x hx ↦
    (hderiv 0 hp x hx).continuousAt.continuousWithinAt
  have hconcat :
      (∑ k ∈ Finset.range N, ∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1), F 0 x)
        = ∫ x in a..(a + N), F 0 x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := F 0)
      (a := fun k ↦ a + (k : ℝ)) (n := N)
      (fun k hk ↦ by
        have := (hcont0.mono (hsub k hk)).intervalIntegrable (μ := volume)
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using this)
    simpa [add_assoc] using h
  -- The per-interval tower applied on each `[a+k, a+k+1]`.
  have hstep : ∀ k ∈ Finset.range N,
      (∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1), F 0 x)
        = (2⁻¹ : ℝ) • (F 0 (a + (k : ℝ)) + F 0 (a + (k : ℝ) + 1))
          + (∑ q ∈ Finset.Ico 1 p,
              ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ))
                • (F q (a + (k : ℝ) + 1) - F q (a + (k : ℝ))))
          + ((-1 : ℝ) ^ p / (p ! : ℝ))
              • ∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1),
                  bernoulliFun p (x - (a + (k : ℝ))) • F p x := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact integral_interval_eq_tower (n := a + (k : ℝ)) F hp
      (fun q hq x hx ↦ hderiv q hq x (hsub k hk hx))
      (fun q hq0 hqp ↦ (hF_int q hq0 hqp).mono_set (hsub k hk))
  -- Telescope the Bernoulli boundary differences.
  have hbern :
      (∑ k ∈ Finset.range N, ∑ q ∈ Finset.Ico 1 p,
          ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ))
            • (F q (a + (k : ℝ) + 1) - F q (a + (k : ℝ))))
        = ∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ ↦ ?_)
    rw [← Finset.smul_sum]
    congr 1
    have h := Finset.sum_range_sub (fun k ↦ F q (a + (k : ℝ))) N
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h
  -- Assemble: concatenate, expand each interval, distribute, telescope, factor.
  rw [← hconcat, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hbern, ← Finset.smul_sum, ← Finset.smul_sum]

omit [CompleteSpace E] in
/-- Trapezoidal reindexing: the trapezoidal sum over the `N` unit intervals starting at `a`
equals the full sum of the `N + 1` sample values minus half the two endpoint values. -/
private theorem sum_trapezoid_eq (a : ℝ) (g : ℝ → E) (N : ℕ) :
    ∑ n ∈ Finset.range N, (2⁻¹ : ℝ) • (g (a + (n : ℝ)) + g (a + (n : ℝ) + 1))
      = (∑ n ∈ Finset.range (N + 1), g (a + (n : ℝ))) - (2⁻¹ : ℝ) • (g a + g (a + (N : ℝ))) := by
  induction N with
  | zero => simp; module
  | succ M ih =>
    rw [Finset.sum_range_succ _ M, ih, Finset.sum_range_succ _ (M + 1)]
    push_cast
    simp only [← add_assoc]
    module

/-- Euler–Maclaurin summation formula (raw form): the value-sum counterpart of
`integral_eq_tower_sum`, for a family `F 0, …, F p` on `[a, a+N]`:
`∑_{n=0}^{N} F 0 (a+n) = ∫ₐ^{a+N} F 0 + (F 0 a + F 0 (a+N))/2
  - ∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · (F q (a+N) - F q a)
  - (-1)^p/p! · ∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·F p`. -/
private theorem sum_eq_tower_integral {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∑ n ∈ Finset.range (N + 1), F 0 (a + n)
      = (∫ x in a..(a + N), F 0 x) + (2⁻¹ : ℝ) • (F 0 a + F 0 (a + N))
        - (∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a))
        - ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  rw [integral_eq_tower_sum F hp hderiv hF_int, sum_trapezoid_eq a (F 0) N]
  abel

omit [CompleteSpace E] in
/-- Even/odd collapse of the Euler–Maclaurin Bernoulli sum: for any coefficient family
`c : ℕ → E`,
`∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · c q = -∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · c (2k-1)`. -/
private theorem sum_Ico_bernoulli_collapse (c : ℕ → E) (p : ℕ) :
    ∑ q ∈ Finset.Ico 1 p,
        ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • c q
      = -∑ k ∈ Finset.Ico 1 (p / 2 + 1),
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ)) • c (2 * k - 1) := by
  -- The terms with `q` even vanish, since then `q + 1` is odd and `≥ 3`.
  have hne : ∀ q ∈ Finset.Ico 1 p,
      ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • c q ≠ 0 → Odd q := by
    intro q hq hne0
    rw [Finset.mem_Ico] at hq
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    apply hne0
    simp [bernoulli_eq_zero_of_odd hodd.add_one (by lia)]
  rw [← Finset.sum_filter_of_ne hne, ← Finset.sum_neg_distrib]
  -- Reindex the surviving odd `q = 2k - 1` by `k = (q + 1) / 2`.
  refine Finset.sum_bij' (fun q _ ↦ (q + 1) / 2) (fun k _ ↦ 2 * k - 1) ?_ ?_ ?_ ?_ ?_
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    obtain ⟨⟨_, hqp⟩, m, rfl⟩ := hq
    lia
  · rintro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    exact ⟨⟨by lia, by lia⟩, k - 1, by lia⟩
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨_, m, rfl⟩ := hq
    change 2 * ((2 * m + 1 + 1) / 2) - 1 = 2 * m + 1
    lia
  · rintro k hk
    simp only [Finset.mem_Ico] at hk
    show (2 * k - 1 + 1) / 2 = k
    lia
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨_, m, rfl⟩ := hq
    -- `simp only [hi]` both beta-reduces `(fun k ↦ …) ((q + 1) / 2)` and rewrites the index.
    simp only [show (2 * m + 1 + 1) / 2 = m + 1 by lia]
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by lia, show 2 * (m + 1) = 2 * m + 1 + 1 by lia,
      Odd.neg_one_pow ⟨m, rfl⟩]
    module

/-- Euler–Maclaurin summation formula (even-index form): the value-sum tower with the
Bernoulli boundary sum folded onto the even indices:
`∑_{n=0}^{N} F 0 (a+n) = ∫ₐ^{a+N} F 0 + (F 0 a + F 0 (a+N))/2
  + ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · (F (2k-1) (a+N) - F (2k-1) a)
  - (-1)^p/p! · ∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·F p`.
The remainder integrals are still the per-interval ones. -/
private theorem sum_eq_tower_integral_even {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∑ n ∈ Finset.range (N + 1), F 0 (a + n)
      = (∫ x in a..(a + N), F 0 x) + (2⁻¹ : ℝ) • (F 0 a + F 0 (a + N))
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (F (2 * k - 1) (a + N) - F (2 * k - 1) a))
        - ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  have hcol := sum_Ico_bernoulli_collapse (fun q ↦ F q (a + N) - F q a) p
  -- Beta-reduce the `(fun q ↦ …) (2 * k - 1)` redexes left by instantiating `c`.
  beta_reduce at hcol
  rw [sum_eq_tower_integral F hp hderiv hF_int, hcol]
  abel

/-- Per-interval Euler–Maclaurin tower (even-index form): the classical
iterated-derivative form on a single unit interval `[n, n+1]`:
`∫ₙⁿ⁺¹ f = (f n + f (n+1))/2 - ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · Δf⁽²ᵏ⁻¹⁾`
`+ (-1)^p/p! · ∫ₙⁿ⁺¹ B_p(x-n)·f⁽ᵖ⁾`, with `Δg = g (n+1) - g n`. -/
private theorem integral_unitInterval_eq_tower {n : ℝ} {f : ℝ → E} {p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (iteratedDeriv q f) volume n (n + 1)) :
    ∫ x in n..(n + 1), f x
      = (2⁻¹ : ℝ) • (f n + f (n + 1))
        - (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (iteratedDeriv (2 * k - 1) f (n + 1) - iteratedDeriv (2 * k - 1) f n))
        + ((-1 : ℝ) ^ p / (p ! : ℝ))
            • ∫ x in n..(n + 1), bernoulliFun p (x - n) • iteratedDeriv p f x := by
  have hmain := integral_interval_eq_tower (n := n) (fun q ↦ iteratedDeriv q f) hp hderiv hf_int
  have hcol := sum_Ico_bernoulli_collapse
    (fun q ↦ iteratedDeriv q f (n + 1) - iteratedDeriv q f n) p
  beta_reduce at hcol
  simp only [iteratedDeriv_zero] at hmain ⊢
  rw [hmain, hcol]
  abel

omit [CompleteSpace E] in
/-- Concatenation of the per-interval remainder integrals: for an integer `a`,
`∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·G(x) dx = ∫_a^{a+N} B_p(Int.fract x)·G(x) dx`. -/
private theorem sum_integral_bernoulliFun_eq (a : ℤ) (p N : ℕ) (G : ℝ → E)
    (hG : IntervalIntegrable G volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range N,
        ∫ x in ((a : ℝ) + n)..((a : ℝ) + n + 1), bernoulliFun p (x - ((a : ℝ) + n)) • G x
      = ∫ x in (a : ℝ)..((a : ℝ) + N), bernoulliFun p (Int.fract x) • G x := by
  -- On `(a+k, a+k+1]`, off the right endpoint, `Int.fract x = x - (a+k)`.
  have hker : ∀ k, k < N → ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Set.uIoc ((a : ℝ) + k) ((a : ℝ) + k + 1) →
        bernoulliFun p (x - ((a : ℝ) + k)) • G x = bernoulliFun p (Int.fract x) • G x := by
    intro k hk
    have hsing : {x : ℝ | x = (a : ℝ) + (k : ℝ) + 1}ᶜ ∈ (ae (volume : Measure ℝ)) := by
      rw [compl_mem_ae_iff, Set.ofPred_eq_eq_singleton]; exact Real.volume_singleton
    filter_upwards [hsing] with x hx hmem
    have hxne : x ≠ (a : ℝ) + (k : ℝ) + 1 := by simpa using hx
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
    have hlt : x < (a : ℝ) + (k : ℝ) + 1 := lt_of_le_of_ne hmem.2 hxne
    have hfr : Int.fract x = x - ((a : ℝ) + (k : ℝ)) := by
      rw [← Int.fract_sub_intCast x (a + k), Int.fract_eq_self.mpr
        ⟨by push_cast; linarith [hmem.1], by push_cast; linarith⟩]
      push_cast; ring
    rw [hfr]
  -- Hence the periodized kernel is interval-integrable on each unit interval.
  have hint : ∀ k, k < N →
      IntervalIntegrable (fun x ↦ bernoulliFun p (Int.fract x) • G x) volume
        ((a : ℝ) + k) ((a : ℝ) + k + 1) := by
    intro k hk
    have hHk : IntervalIntegrable (fun x ↦ bernoulliFun p (x - ((a : ℝ) + k)) • G x) volume
        ((a : ℝ) + k) ((a : ℝ) + k + 1) :=
      (hG.mono_set (uIcc_add_natCast_subset_uIcc (a : ℝ) hk)).continuousOn_smul (by fun_prop)
    refine hHk.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hker k hk
  -- Replace each unit kernel, then concatenate via adjacent intervals.
  rw [Finset.sum_congr rfl (fun k hk ↦
    intervalIntegral.integral_congr_ae (hker k (Finset.mem_range.mp hk)))]
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x ↦ bernoulliFun p (Int.fract x) • G x) (a := fun k ↦ (a : ℝ) + (k : ℝ)) (n := N)
    (fun k hk ↦ by simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hint k hk)
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h


/-- The Euler–Maclaurin remainder `R_p(f; a, b) = (-1)^(p+1)/p! · ∫_a^b B̃_p(x) · f⁽ᵖ⁾(x) dx`,
with `B̃_p` the periodized Bernoulli function `bernoulliFun p (Int.fract x)` and
`f⁽ᵖ⁾ = iteratedDeriv p f`. The kernel is a *real* scalar, so this one definition serves any
real Banach space `E`. -/
noncomputable def eulerMaclaurinRemainder (p : ℕ) (f : ℝ → E) (a b : ℝ) : E :=
  ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ))
    • ∫ x in a..b, bernoulliFun p (Int.fract x) • iteratedDeriv p f x

/-- Euler–Maclaurin summation formula with remainder: for an integer `a`, an order `p ≥ 1`
and `f : ℝ → E` whose iterated derivatives form a derivative chain on `[a, a+N]` and are
interval-integrable there,
`∑_{n=0}^{N} f(a+n) = ∫_a^{a+N} f + (f a + f (a+N))/2
  + ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · (f⁽²ᵏ⁻¹⁾(a+N) - f⁽²ᵏ⁻¹⁾(a)) + R_p(f; a, a+N)`.
See `Complex.sum_eq` for the `ℂ`-flavoured restatement. -/
theorem eulerMaclaurin_sum_eq {f : ℝ → E} (a : ℤ) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc (a : ℝ) ((a : ℝ) + N),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p →
      IntervalIntegrable (iteratedDeriv q f) volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range (N + 1), f ((a : ℝ) + n)
      = (∫ x in (a : ℝ)..((a : ℝ) + N), f x) + (2⁻¹ : ℝ) • (f (a : ℝ) + f ((a : ℝ) + N))
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (iteratedDeriv (2 * k - 1) f ((a : ℝ) + N) - iteratedDeriv (2 * k - 1) f (a : ℝ)))
        + eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N) := by
  have hmain := sum_eq_tower_integral_even (a := (a : ℝ))
    (fun q ↦ iteratedDeriv q f) hp hderiv hf_int
  have hrem : eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N)
      = -(((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
          ∫ x in ((a : ℝ) + n)..((a : ℝ) + n + 1),
            bernoulliFun p (x - ((a : ℝ) + n)) • iteratedDeriv p f x) := by
    rw [eulerMaclaurinRemainder, ← sum_integral_bernoulliFun_eq a p N
      (iteratedDeriv p f) (hf_int p hp le_rfl), pow_succ, ← neg_smul]
    congr 1
    ring
  simp only [iteratedDeriv_zero] at hmain ⊢
  rw [hmain, hrem]
  abel

end

/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/






/-!
# Complex-valued Euler–Maclaurin and the iterated derivatives of `x ↦ x⁻ˢ`

The `ℂ`-flavoured restatement of the Euler–Maclaurin formula of `Zeta/Summation/Basic.lean`,
together with the iterated derivatives of the zeta summand `f_s(x) = (x : ℂ)⁻ˢ`, which discharge
its derivative-chain hypothesis. Throughout, `(s)_j = (ascPochhammer ℂ j).eval s` is the rising
factorial.

## Main results

- `Complex.eulerMaclaurinRemainder_eq`: the generic Euler–Maclaurin remainder in
  `ℂ`-multiplicative form.
- `Complex.sum_eq`: the complex-valued Euler–Maclaurin summation formula.
- `Complex.iteratedDeriv_cpow_ofReal_neg`: the closed form of `(f_s)⁽ʲ⁾(x)` for `x > 0`.
- `Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg`: its `HasDerivAt` chain form.
- `Complex.sum_cpow_eq`: the finite Euler–Maclaurin expansion of `∑ n⁻ˢ`.
-/
section


open MeasureTheory
open scoped Topology Nat

namespace Complex

/-- **The Euler–Maclaurin remainder, in `ℂ`-multiplicative form**:
`R_p(f; a, b) = (-1)^(p+1)/p! · ∫_a^b B̃_p(x) · f⁽ᵖ⁾(x) dx`. -/
theorem eulerMaclaurinRemainder_eq (p : ℕ) (f : ℝ → ℂ) (a b : ℝ) :
    eulerMaclaurinRemainder p f a b
      = (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
        * ∫ x in a..b, (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p f x := by
  rw [eulerMaclaurinRemainder]
  simp only [real_smul, ofReal_div, ofReal_pow, ofReal_neg, ofReal_one, ofReal_natCast]

/-- The periodized Bernoulli kernel `x ↦ B̃_p(x) = bernoulliFun p (Int.fract x)`, read as a
complex-valued function, is measurable. -/
theorem measurable_bernoulliFun_fract (p : ℕ) :
    Measurable (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ)) := by fun_prop

/-- **Uniform bound on the periodized Bernoulli kernel**: `B̃_p` is bounded by some `C ≥ 0`. -/
theorem exists_norm_bernoulliFun_fract_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖(bernoulliFun p (Int.fract x) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_bernoulliFun p).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  rw [Complex.norm_real]
  exact (hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩).trans (le_max_left _ _)

/-- The complex power `x ↦ (x : ℂ) ^ w` is a.e.-strongly-measurable on `(c, ∞)` for any
`0 ≤ c`. -/
theorem aestronglyMeasurable_ofReal_cpow_Ioi {c : ℝ} (hc : 0 ≤ c) (w : ℂ) :
    AEStronglyMeasurable (fun x : ℝ ↦ (x : ℂ) ^ w) (volume.restrict (Set.Ioi c)) := by
  refine ContinuousOn.aestronglyMeasurable (fun x hx ↦ ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const x w
    (Or.inr (lt_of_le_of_lt hc (Set.mem_Ioi.mp hx)).ne')).continuousWithinAt

/-- **Improper (`Ioi`) domination for periodized-Bernoulli-weighted integrands.** If a kernel
`K : ℝ → ℂ` is a.e.-strongly-measurable on `(c, ∞)` and dominated there by an integrable
majorant `h`, then `x ↦ B̃_p(x) · K(x)` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le (p : ℕ) {c : ℝ} {K : ℝ → ℂ}
    {h : ℝ → ℝ} (hh : IntegrableOn h (Set.Ioi c))
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Ioi c)))
    (hbound : ∀ x ∈ Set.Ioi c, ‖K x‖ ≤ h x) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * K x) (Set.Ioi c) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_bernoulliFun_fract_le p
  refine Integrable.mono' (g := fun x ↦ C * h x) (hh.const_mul C)
    ((measurable_bernoulliFun_fract p).aestronglyMeasurable.mul hK) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul]
  exact mul_le_mul (hC x) (hbound x hx) (norm_nonneg _) hC0

/-- **Complex-valued Euler–Maclaurin summation formula**, the `ℂ`-flavoured restatement of
`eulerMaclaurin_sum_eq`:
`∑_{n=0}^{N} f(a+n) = ∫_a^{a+N} f + (f a + f (a+N))/2
  + ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · (f⁽²ᵏ⁻¹⁾(a+N) - f⁽²ᵏ⁻¹⁾(a)) + R_p(f; a, a+N)`. -/
theorem sum_eq {f : ℝ → ℂ} (a : ℤ) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc (a : ℝ) ((a : ℝ) + N),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p →
      IntervalIntegrable (iteratedDeriv q f) volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range (N + 1), f ((a : ℝ) + n)
      = (∫ x in (a : ℝ)..((a : ℝ) + N), f x) + (f (a : ℝ) + f ((a : ℝ) + N)) / 2
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (iteratedDeriv (2 * k - 1) f ((a : ℝ) + N) - iteratedDeriv (2 * k - 1) f (a : ℝ)))
        + eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N) := by
  rw [eulerMaclaurin_sum_eq a hp hderiv hf_int]
  simp only [real_smul, ofReal_div, ofReal_inv, ofReal_natCast, ofReal_ofNat]
  ring

/-- The closed form `(-1)ʲ · (s)_j · (x : ℂ)^(-s - j)` of the `j`-th derivative of `x ↦ x⁻ˢ` has
as its own derivative the `(j+1)`-st member of the same family. -/
private theorem hasDerivAt_cpow_closed_form (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)))
      ((-1 : ℂ) ^ (j + 1) * (ascPochhammer ℂ (j + 1)).eval s * (x : ℂ) ^ (-s - ((j : ℂ) + 1)))
      x := by
  by_cases he : -s - (j : ℂ) = 0
  · -- `s = -j`: the power is the constant `1` and the new rising factorial vanishes.
    have hsj : s + (j : ℂ) = 0 := by linear_combination -he
    have hp : (ascPochhammer ℂ (j + 1)).eval s = 0 := by
      rw [ascPochhammer_succ_eval, hsj, mul_zero]
    rw [he, hp]
    simp only [Complex.cpow_zero, mul_one, mul_zero, zero_mul]
    exact hasDerivAt_const x _
  · -- general case: differentiate the power via the cpow rule.
    have hpow := hasDerivAt_ofReal_cpow_const (r := -s - (j : ℂ)) hx.ne' he
    have key : (-1 : ℂ) ^ (j + 1) * (ascPochhammer ℂ (j + 1)).eval s
          * (x : ℂ) ^ (-s - ((j : ℂ) + 1))
        = ((-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s)
          * ((-s - (j : ℂ)) * (x : ℂ) ^ ((-s - (j : ℂ)) - 1)) := by
      rw [show -s - ((j : ℂ) + 1) = (-s - (j : ℂ)) - 1 from by ring, ascPochhammer_succ_eval]
      ring
    rw [key]
    exact hpow.const_mul _

/-- **Iterated derivatives of `x ↦ x⁻ˢ`.** For `x > 0`,
`(f_s)⁽ʲ⁾(x) = (-1)ʲ · (s)_j · (x : ℂ)^(-s - j)`. -/
theorem iteratedDeriv_cpow_ofReal_neg (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x
      = (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (x : ℂ) ^ (-s - (j : ℂ)) := by
  induction j generalizing x with
  | zero => simp [ascPochhammer_zero]
  | succ j ih =>
    have heq : iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s))
        =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy ↦ ih (Set.mem_Ioi.mp hy)
    rw [iteratedDeriv_succ, heq.deriv_eq, (hasDerivAt_cpow_closed_form s j hx).deriv]
    push_cast
    ring

/-- **Derivative chain for `x ↦ x⁻ˢ`.** For `x > 0`, the `j`-th iterated derivative of
`f_s(x) = (x : ℂ)⁻ˢ` is differentiable with derivative the `(j+1)`-st iterated derivative
(the derivative-chain hypothesis of `Complex.sum_eq`). -/
theorem hasDerivAt_iteratedDeriv_cpow_ofReal_neg (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s)))
      (iteratedDeriv (j + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) x := by
  have heq : iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s))
      =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx)
      fun y hy ↦ iteratedDeriv_cpow_ofReal_neg s j (Set.mem_Ioi.mp hy)
  rw [iteratedDeriv_cpow_ofReal_neg s (j + 1) hx]
  have hd := (hasDerivAt_cpow_closed_form s j hx).congr_of_eventuallyEq heq
  rw [show -s - ((j + 1 : ℕ) : ℂ) = -s - ((j : ℂ) + 1) by push_cast; ring]
  exact hd

/-- **Finite Euler–Maclaurin expansion of `∑ n⁻ˢ`.** For `s ≠ 1` and integers `1 ≤ N ≤ R`, at
order `p = 2M+1` and with `f_s(x) = (x : ℂ)⁻ˢ`,
`∑_{n=N}^{R} n⁻ˢ = (R^{1-s} - N^{1-s})/(1-s) + (N⁻ˢ + R⁻ˢ)/2
  - ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · (R^{-s-(2k-1)} - N^{-s-(2k-1)}) + R_{2M+1}(f_s; N, R)`.
-/
theorem sum_cpow_eq (s : ℂ) (hs : s ≠ 1) (M N R : ℕ) (hN : 1 ≤ N) (hNR : N ≤ R) :
    ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)
      = ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
        + ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2
        - (∑ k ∈ Finset.Icc 1 M,
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (ascPochhammer ℂ (2 * k - 1)).eval s
              * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
                  - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
        + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  have hNa : ((N : ℤ) : ℝ) = (N : ℝ) := Int.cast_natCast N
  have hRN : ((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ) = (R : ℝ) := by push_cast [Nat.cast_sub hNR]; ring
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le hN0 (by exact_mod_cast hNR)
  have hpos : Set.uIcc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hRN, hNa, Set.uIcc_of_le (by exact_mod_cast hNR)]
    exact fun x hx ↦ lt_of_lt_of_le hN0 hx.1
  have key := sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 1) (by positivity)
    (fun q _ x hx ↦ hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q (hpos hx))
    (fun q _ _ ↦ ContinuousOn.intervalIntegrable fun x hx ↦
      (hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q (hpos hx)).continuousAt.continuousWithinAt)
  -- Normalize the integer/natural casts and the boundary index set in `key`.
  rw [hRN, hNa, show Finset.Ico 1 ((2 * M + 1) / 2 + 1) = Finset.Icc 1 M from by
    ext x; rw [Finset.mem_Ico, Finset.mem_Icc]; lia] at key
  -- Closed form for the iterated derivatives of `f` on `(0, ∞)`.
  have hDeriv_eq : ∀ (j : ℕ) (x : ℝ), 0 < x →
      iteratedDeriv j f x
        = (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (x : ℂ) ^ (-s - (j : ℂ)) :=
    fun j _ hx ↦ iteratedDeriv_cpow_ofReal_neg s j hx
  -- Rewrite the left-hand `Icc` sum as the `range` sum of `key`.
  have hLHS : ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)
      = ∑ n ∈ Finset.range (R - N + 1), f ((N : ℝ) + (n : ℝ)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      show R + 1 - N = R - N + 1 from by lia]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hf]; push_cast; ring_nf
  -- The integral via `integral_cpow`.
  have hIeq : (∫ x in (N : ℝ)..(R : ℝ), f x)
      = ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) := by
    simp only [hf]
    rw [integral_cpow (Or.inr ⟨fun h ↦ hs (neg_injective h), ?_⟩)]
    · rw [show -s + 1 = 1 - s from by ring]; push_cast; ring_nf
    · rw [Set.uIcc_of_le (by exact_mod_cast hNR : (N : ℝ) ≤ R), Set.mem_Icc]
      exact fun ⟨h1, _⟩ ↦ absurd h1 (not_le.mpr hN0)
  -- The endpoint correction (just a cast).
  have hEeq : (f (N : ℝ) + f (R : ℝ)) / 2 = ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2 := by
    simp only [hf]; push_cast; ring_nf
  -- Each Bernoulli boundary term collapses to the closed form, with a sign flip.
  have hBeq : ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ)
          * (iteratedDeriv (2 * k - 1) f (R : ℝ) - iteratedDeriv (2 * k - 1) f (N : ℝ))
      = -∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s
            * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
                - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hodd : (-1 : ℂ) ^ (2 * k - 1) = -1 :=
      Odd.neg_one_pow ⟨k - 1, by have := (Finset.mem_Icc.mp hk).1; lia⟩
    rw [hDeriv_eq _ _ hRpos, hDeriv_eq _ _ hN0, hodd]
    push_cast
    ring
  rw [hLHS, key, hIeq, hEeq, hBeq]
  ring

end Complex

end

/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/






/-!
# Euler–Maclaurin expansion of the Riemann zeta function (region `Re s > 1`)

The Euler–Maclaurin expansion of `riemannZeta s` in the region of absolute convergence
`Re s > 1`, with the improper (`(N, ∞)`) remainder integral of the zeta summand
`f_s(x) = (x : ℂ)⁻ˢ`.

## Main definitions

- `Complex.eulerMaclaurinRemainderIoi`: the improper Euler–Maclaurin remainder.

## Main results

- `Complex.integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow`: absolute convergence of the
  zeta remainder integral for `Re s + p > 1`.
- `riemannZeta_eq_of_one_lt_re`: the Euler–Maclaurin expansion of `riemannZeta s` for `Re s > 1`.
-/
section


open MeasureTheory Filter Topology
open scoped Nat

namespace Complex

/-- For `c.re < 0`, the natural-indexed powers `(R : ℂ)^c` tend to `0` as `R → ∞`. -/
theorem tendsto_natCast_cpow_nhds_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun R : ℕ ↦ (R : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine ((tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp
    tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [Function.comp_apply, neg_neg]
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hR) c).symm

/-- For `1 ≤ N` and `w.re < -1`, the
function `x ↦ B̃_p(x) · (x:ℂ)^w` is integrable on `(N, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_fract_mul_cpow (p N : ℕ) (hN : 1 ≤ N) {w : ℂ}
    (hw : w.re < -1) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact Complex.integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le p (h := fun x : ℝ ↦ x ^ w.re)
    (integrableOn_Ioi_rpow_of_lt hw hN0)
    (Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N) w) fun x hx ↦
      le_of_eq (Complex.norm_cpow_eq_rpow_re_of_pos
        (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le) w)

/-- The improper Euler–Maclaurin remainder
`(-1)^(p+1)/p! · ∫_{(a,∞)} B̃_p(x) · f⁽ᵖ⁾(x) dx`, the `R → ∞` limit of the compact-interval
remainder `eulerMaclaurinRemainder p f a R` where the integral over `Set.Ioi a` converges. -/
noncomputable def eulerMaclaurinRemainderIoi (p : ℕ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
    * ∫ x in Set.Ioi a, (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p f x

/-- Absolute convergence of the zeta remainder integral: for `1 ≤ N` and `Re s + p > 1`,
the integrand `B̃_p(x) · f_s⁽ᵖ⁾(x)` of the order-`p` Euler–Maclaurin remainder is integrable on
`(N, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow
    (s : ℂ) (p N : ℕ) (hN : 1 ≤ N) (hsp : 1 < s.re + p) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (-s - (p : ℂ)).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith
  -- The closed form `f_s⁽ᵖ⁾(x) = (-1)^p (s)_p x^{-s-p}` reduces this to the
  -- kernel-times-power case.
  have h : IntegrableOn (fun x : ℝ ↦ (-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s *
      ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hw).const_mul _
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [Complex.iteratedDeriv_cpow_ofReal_neg s p (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le)]
  ring

end Complex

/-- Euler–Maclaurin expansion of `riemannZeta s` for `Re s > 1`: for `1 ≤ N` and order
`p = 2M+1`,
`ζ(s) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
          + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)} + R_M(s, N)`,
with the improper remainder `R_M(s,N) = Complex.eulerMaclaurinRemainderIoi (2M+1) f_s N`. -/
theorem riemannZeta_eq_of_one_lt_re (s : ℂ) (hs : 1 < s.re) (M N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
        + (∑ k ∈ Finset.Icc 1 M,
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (ascPochhammer ℂ (2 * k - 1)).eval s
              * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  have hsne1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (by rintro rfl; norm_num at hs)
  have hsum : Summable (fun n : ℕ ↦ (n : ℂ) ^ (-s)) := by
    simpa only [one_div, ← Complex.cpow_neg] using
      (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  -- `∑' n, n⁻ˢ = ζ(s)`.
  have hzeta : ∑' (n : ℕ), (n : ℂ) ^ (-s) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hsum.tsum_eq_zero_add,
      Nat.cast_zero, Complex.zero_cpow hs0, zero_add]
    exact tsum_congr fun n ↦ by rw [one_div, ← Complex.cpow_neg]; push_cast; ring_nf
  -- Limit of the left-hand finite sums.
  have hLHS : Tendsto (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) atTop
      (𝓝 ((∑' (n : ℕ), (n : ℂ) ^ (-s)) - ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s))) := by
    have htsum : Tendsto (fun R : ℕ ↦ ∑ i ∈ Finset.range (R + 1), (i : ℂ) ^ (-s)) atTop
        (𝓝 (∑' (n : ℕ), (n : ℂ) ^ (-s))) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    apply (htsum.sub_const _).congr'
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [show Finset.Icc N R = Finset.Ico N (R + 1) from by
          ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; lia,
      Finset.sum_Ico_eq_sub _ (by lia : N ≤ R + 1)]
  -- Limit of the remainder integral.
  have hsp : 1 < s.re + ((2 * M + 1 : ℕ) : ℝ) := by
    push_cast; have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith
  have hint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun (2 * M + 1) (Int.fract x) : ℂ) *
      iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) :=
    Complex.integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s (2 * M + 1) N hN hsp
  have hrem : Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)) atTop
      (𝓝 (Complex.eulerMaclaurinRemainderIoi (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))) := by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _ hint tendsto_natCast_atTop_atTop).const_mul _
  -- Limits of the vanishing `R`-power terms.
  have h1s : (1 - s).re < 0 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hns : (-s).re < 0 := by rw [Complex.neg_re]; linarith
  have hT1 : Tendsto (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)) atTop
      (𝓝 (((0 : ℂ) - (N : ℂ) ^ (1 - s)) / (1 - s))) :=
    ((Complex.tendsto_natCast_cpow_nhds_zero h1s).sub_const _).div_const _
  have hT2 : Tendsto (fun R : ℕ ↦ ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2) atTop
      (𝓝 (((N : ℂ) ^ (-s) + 0) / 2)) :=
    (Tendsto.const_add _ (Complex.tendsto_natCast_cpow_nhds_zero hns)).div_const _
  have hT3 : Tendsto (fun R : ℕ ↦ ∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))) atTop
      (𝓝 (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))) := by
    apply tendsto_finsetSum
    intro k _
    have hek : (-s - ((2 * k - 1 : ℕ) : ℂ)).re < 0 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
      have := Nat.cast_nonneg (α := ℝ) (2 * k - 1); linarith
    exact Tendsto.const_mul _ ((Complex.tendsto_natCast_cpow_nhds_zero hek).sub_const _)
  -- Assemble the limit of the right-hand side and identify it with that of the left side.
  have hRHS := (((hT1.add hT2).sub hT3).add hrem)
  have heq : (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) =ᶠ[atTop]
      (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
          + ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2
          - (∑ k ∈ Finset.Icc 1 M,
              ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                * (ascPochhammer ℂ (2 * k - 1)).eval s
                * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
          + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
              (N : ℝ) (R : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with R hR
    exact Complex.sum_cpow_eq s hsne1 M N R hN hR
  have hkey := tendsto_nhds_unique (hLHS.congr' heq) hRHS
  -- Solve for `ζ(s)` and simplify the limit.
  rw [hzeta] at hkey
  have hconv : ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s) = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hN]
    simp [Complex.zero_cpow hs0]
  have hbern : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
      = -∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
            * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne1)
  have hs1' : s - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hsne1
  rw [hconv, hbern, sub_eq_iff_eq_add] at hkey
  rw [hkey]
  field_simp
  ring

end

/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/







/-!
# Analytic continuation of the Euler–Maclaurin expansion of `ζ`

The Euler–Maclaurin expansion of `ζ` on the punctured strip `Re s > -(2M+1)`, `s ≠ 1`, carrying
the analytically continued remainder (one order-raising integration by parts past the region
`Re s > 1` of `riemannZeta_eq_of_one_lt_re`).

## Main definitions

- `zetaEMExpansion`: the analytic Euler–Maclaurin right-hand side `E_M(s,N)`, split by
  `zetaEMExpansion_eq_approximant_add_remainder` into the computed `zetaApproximant` and the
  error term `zetaRemainder`.

## Main results

- `Complex.differentiableOn_eulerMaclaurinRemainderIoi_cpow`: the order-`p` improper remainder
  `s ↦ Complex.eulerMaclaurinRemainderIoi p f_s N` is holomorphic on `{Re s > 1 - p}`.
- `analyticOnNhd_zetaEMExpansion`: `E_M(·,N)` is analytic on `{Re s > -(2M+1)} \ {1}`.
- `riemannZeta_eq`, `riemannZeta_eq_approximant_add_remainder`: the continued expansion.
- `riemannZeta_eq_order_one`: the first-order case
  `ζ(s) = 1/(s-1) + 1/2 + Complex.eulerMaclaurinRemainderIoi 1 f_s 1` on `Re s > 0`, `s ≠ 1`.
- `riemannZeta_ofReal_re_neg_of_mem_Ioo`: `Re ζ(x) < 0` for real `x ∈ (0, 1)`.
-/
section


open MeasureTheory Filter Topology
open scoped Nat

namespace Complex

/-- Closed form of the improper `ζ`-summand remainder. With `f_s y = (y : ℂ)^(-s)`,
`Complex.eulerMaclaurinRemainderIoi p f_s N = -(s)_p/p! · ∫_N^∞ B̃_p(x) · x^{-s-p} dx`. -/
theorem eulerMaclaurinRemainderIoi_cpow_eq (s : ℂ) (p N : ℕ) :
    Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = -(ascPochhammer ℂ p).eval s / (p ! : ℂ)
          * ∫ x in Set.Ioi (N : ℝ),
              (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)) := by
  rw [Complex.eulerMaclaurinRemainderIoi]
  have step1 : (∫ x in Set.Ioi (N : ℝ),
        (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x)
      = ∫ x in Set.Ioi (N : ℝ), ((-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s)
          * ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg N) (Set.mem_Ioi.mp hx)
    dsimp only
    rw [Complex.iteratedDeriv_cpow_ofReal_neg s p hx0]
    ring
  rw [step1, integral_const_mul]
  have h2 : (-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ p = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨p, by ring⟩
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  field_simp
  linear_combination ((ascPochhammer ℂ p).eval s *
    ∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) * h2

/-- Holomorphy of the order-`p` improper remainder integral. For `1 ≤ N`, the map
`s ↦ Complex.eulerMaclaurinRemainderIoi p f_s N` (with `f_s y = (y:ℂ)^(-s)`) is holomorphic on
the open half-plane `{Re s > 1 - p}`. -/
theorem differentiableOn_eulerMaclaurinRemainderIoi_cpow (p N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
      {s : ℂ | (1 : ℝ) - p < s.re} := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- The periodized Bernoulli kernel is measurable, and each complex power `x ↦ (x:ℂ)^w` is
  -- a.e.-strongly-measurable on `(N, ∞)`; both facts are reused several times below.
  have hker := Complex.measurable_bernoulliFun_fract p
  have hcpowmeas := Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N)
  -- Rewrite `eulerMaclaurinRemainderIoi p f_s N = -(s)_p/p! · G s`: the prefactor is entire, and
  -- `G` is holomorphic on the half-plane by differentiation under the integral sign.
  simp only [eulerMaclaurinRemainderIoi_cpow_eq]
  refine (((ascPochhammer ℂ p).differentiable.neg.div_const (p ! : ℂ)).differentiableOn).mul
    fun s₀ hs₀ ↦ ?_
  rw [Set.mem_ofPred_eq] at hs₀
  -- Choose `σ₁` with `1 - p < σ₁ < Re s₀`, and `ε` so that `σ₁ + p - ε > 1`.
  obtain ⟨σ₁, hσlo, hσhi⟩ : ∃ σ₁ : ℝ, (1 : ℝ) - p < σ₁ ∧ σ₁ < s₀.re :=
    ⟨((1 - p) + s₀.re) / 2, by linarith, by linarith⟩
  set ε : ℝ := (σ₁ + p - 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hexp : (1 : ℝ) < σ₁ + p - ε := by rw [hεdef]; linarith
  -- A bound `C ≥ 0` on the periodized Bernoulli kernel.
  obtain ⟨C, hC0, hC⟩ := Complex.exists_norm_bernoulliFun_fract_le p
  -- Differentiate under the integral sign on the neighbourhood `{Re s > σ₁}` of `s₀`.
  have happ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (N : ℝ)))
    (F := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))
    (F' := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ)
      * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1)))
    (x₀ := s₀) (bound := fun x ↦ C / ε * x ^ (-(σ₁ + p - ε)))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσhi)
    -- (1) measurability of `F s` near `s₀`
    (Filter.Eventually.of_forall fun s ↦ hker.aestronglyMeasurable.mul (hcpowmeas _))
    -- (2) integrability of `F s₀`
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN
      (by rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith))
    -- (3) measurability of `F' s₀`
    (hker.aestronglyMeasurable.mul
      (((hcpowmeas _).mul
        (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable).mul
          aestronglyMeasurable_const))
    -- (4) the uniform bound on `F'`
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      have hx1 : (1 : ℝ) ≤ x :=
        le_of_lt (lt_of_le_of_lt (by exact_mod_cast hN) (Set.mem_Ioi.mp hx))
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
      have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
      rw [show ‖(bernoulliFun p (Int.fract x) : ℂ)
                * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1))‖
              = ‖(bernoulliFun p (Int.fract x) : ℂ)‖ * x ^ (-s.re - p) * Real.log x from by
            rw [← Complex.ofReal_log hx0.le]
            simp only [norm_mul, norm_neg, norm_one, mul_one,
              Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs,
              Complex.sub_re, Complex.neg_re, Complex.natCast_re, abs_of_nonneg hlog]
            ring,
        show C / ε * x ^ (-(σ₁ + p - ε)) = C * x ^ (-σ₁ - p) * (x ^ ε / ε) from by
          rw [show -(σ₁ + p - ε) = -σ₁ - p + ε from by ring, Real.rpow_add hx0]; ring]
      exact mul_le_mul (mul_le_mul (hC x) (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
          (Real.rpow_nonneg hx0.le _) hC0) (Real.log_le_rpow_div hx0.le hεpos) hlog
        (mul_nonneg hC0 (Real.rpow_nonneg hx0.le _)))
    -- (5) integrability of the bound
    ((integrableOn_Ioi_rpow_of_lt (a := -(σ₁ + p - ε)) (by linarith) hN0).const_mul (C / ε))
    -- (6) the `s`-derivative
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
      have hbase : (x : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le).ne'
      exact HasDerivAt.const_mul _
        ((Complex.hasStrictDerivAt_const_cpow (Or.inl hbase)).hasDerivAt.comp s
          (by simpa using (hasDerivAt_id s).neg.sub_const (p : ℂ))))
  exact happ.2.differentiableAt.differentiableWithinAt

/-- Finite order-raising step for the `ζ`-summand remainder. For `1 ≤ N ≤ R`, the
order-`(2M+1)` remainder over `[N, R]` equals the order-`(2M+2)` one plus the Bernoulli
boundary term of index `2M+2`. -/
private theorem eulerMaclaurinRemainder_cpow_succ (s : ℂ) (M N R : ℕ) (hN : 1 ≤ N) (hNR : N ≤ R) :
    eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (R : ℝ)
              - iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
        + eulerMaclaurinRemainder (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
            (N : ℝ) (R : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNa : ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
  have hRN : ((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ) = (R : ℝ) := by push_cast [Nat.cast_sub hNR]; ring
  have hderiv : ∀ q, q < 2 * M + 2 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x :=
    fun q _ x hx ↦ Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q hx
  have hpos : Set.uIcc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hRN, hNa, Set.uIcc_of_le (by exact_mod_cast hNR)]
    exact fun x hx ↦ lt_of_lt_of_le hN0 hx.1
  have hint : ∀ q, 0 < q → q ≤ 2 * M + 2 →
      IntervalIntegrable (iteratedDeriv q f) volume ((N : ℤ) : ℝ)
        (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) :=
    fun q _ _ ↦ ContinuousOn.intervalIntegrable fun x hx ↦
      (Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q
        (hpos hx)).continuousAt.continuousWithinAt
  have h1 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 1) (by lia)
    (fun q _ x hx ↦ hderiv q (by lia) x (hpos hx)) (fun q hq0 hq ↦ hint q hq0 (by lia))
  have h2 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 2) (by lia)
    (fun q hq x hx ↦ hderiv q hq x (hpos hx)) hint
  rw [hRN, hNa, show (2 * M + 1) / 2 + 1 = M + 1 from by lia] at h1
  rw [hRN, hNa, show (2 * M + 2) / 2 + 1 = M + 1 + 1 from by lia,
    Finset.sum_Ico_succ_top (show (1 : ℕ) ≤ M + 1 by lia)] at h2
  simp only [show 2 * (M + 1) = 2 * M + 2 from by ring,
    show 2 * M + 2 - 1 = 2 * M + 1 from by lia] at h2
  linear_combination h2 - h1

/-- Order-raising on the improper `ζ`-remainder, `2M+1 → 2M+2`. For `1 ≤ N` and `Re s > -2M`
(where the order-`(2M+1)` integral still converges),
`R^∞_{2M+1}(f_s; N) = B_{2M+2}/(2M+2)! · (s)_{2M+1} · N^{-s-(2M+1)} + R^∞_{2M+2}(f_s; N)`,
the first summand being the first omitted even Bernoulli term `t_{M+1}(s, N)`. -/
theorem eulerMaclaurinRemainderIoi_succ_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M : ℝ) < s.re) :
    Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * M + 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  set c : ℂ := -s - ((2 * M + 1 : ℕ) : ℂ) with hc
  set B : ℂ := ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
  set P : ℂ := (ascPochhammer ℂ (2 * M + 1)).eval s with hP
  have hcre : c.re < 0 := by
    rw [hc, Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; linarith
  -- Both finite remainders converge to their improper counterparts.
  have hrem : ∀ q : ℕ, 1 < s.re + (q : ℝ) →
      Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder q f (N : ℝ) (R : ℝ)) atTop
        (𝓝 (Complex.eulerMaclaurinRemainderIoi q f (N : ℝ))) := fun q hq ↦ by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _
      (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s q N hN hq)
      tendsto_natCast_atTop_atTop).const_mul _
  -- The order-`(2M+1)` derivative in closed form; its value at `R` tends to `0`.
  have hcf : ∀ R : ℕ, 1 ≤ R → iteratedDeriv (2 * M + 1) f (R : ℝ) = -P * (R : ℂ) ^ c := by
    intro R hR
    rw [hf, Complex.iteratedDeriv_cpow_ofReal_neg s (2 * M + 1)
        (by exact_mod_cast hR : (0 : ℝ) < R),
      Odd.neg_one_pow ⟨M, by ring⟩, hc, hP]
    push_cast; ring
  have hbdy : Tendsto (fun R : ℕ ↦ B * (iteratedDeriv (2 * M + 1) f (R : ℝ)
        - iteratedDeriv (2 * M + 1) f (N : ℝ))) atTop (𝓝 (B * P * (N : ℂ) ^ c)) := by
    have hbase := (((tendsto_natCast_cpow_nhds_zero hcre).const_mul (-P)).sub_const
      (-P * (N : ℂ) ^ c)).const_mul B
    rw [show B * (-P * 0 - -P * (N : ℂ) ^ c) = B * P * (N : ℂ) ^ c from by ring] at hbase
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [hcf R (le_trans hN hR), hcf N hN]
  refine tendsto_nhds_unique (Tendsto.congr' ?_ (hrem (2 * M + 1) (by push_cast; linarith)))
    (hbdy.add (hrem (2 * M + 2) (by push_cast; linarith)))
  filter_upwards [eventually_ge_atTop N] with R hR
  exact eulerMaclaurinRemainder_cpow_succ s M N R hN hR

/-- The order-`1` Euler–Maclaurin remainder of `ζ` at a positive real point has norm at most
`1/2`. -/
theorem norm_eulerMaclaurinRemainderIoi_one_ofReal_le {x : ℝ} (hx0 : 0 < x) :
    ‖Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-(x : ℂ))) 1‖ ≤ 1 / 2 := by
  have h := eulerMaclaurinRemainderIoi_cpow_eq (x : ℂ) 1 1
  simp only [Nat.cast_one, ascPochhammer_one, Polynomial.eval_X, Nat.factorial_one, div_one] at h
  have hb := norm_integral_le_of_norm_le
    (f := fun y : ℝ ↦ (bernoulliFun 1 (Int.fract y) : ℂ) * (y : ℂ) ^ (-(x : ℂ) - 1))
    (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    ((integrableOn_Ioi_rpow_of_lt (show -x - 1 < -1 by linarith) one_pos).const_mul (1 / 2)) ?_
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -x - 1 + 1 = -x from by ring, neg_div_neg_eq] at hb
    rw [h, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    refine (mul_le_mul_of_nonneg_left hb hx0.le).trans_eq ?_
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := one_pos.trans hy
    have hre : (-(x : ℂ) - 1).re = -x - 1 := by simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      hre, bernoulliFun_one]
    refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [Int.fract_nonneg y], ?_⟩)
      (Real.rpow_nonneg hy0.le _)
    linarith [Int.fract_lt_one y]

end Complex

/-- The analytic Euler–Maclaurin right-hand side for `ζ`,
`E_M(s,N) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
              + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)}
              + B_{2M+2}/(2M+2)! · (s)_{2M+1} · N^{-s-(2M+1)}
              + Complex.eulerMaclaurinRemainderIoi (2M+2) f_s N`,
whose last two summands form the analytically continued remainder
`R_M(s,N) = t_{M+1}(s,N) + R^∞_{2M+2}(f_s; N)`. -/
noncomputable def zetaEMExpansion (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
    + ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)

/-- The Euler–Maclaurin approximant for `ζ`, the computed main term of the order-`M`,
cutoff-`N` expansion:
`A_M(s,N) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
              + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)}`. -/
noncomputable abbrev zetaApproximant (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))

/-- The Euler–Maclaurin remainder for `ζ`, the error term of the order-`M`, cutoff-`N`
expansion: `R_M(s,N) = t_{M+1}(s,N) + R^∞_{2M+2}(f_s; N)`, with `t_{M+1}` the leading uncomputed
Bernoulli term. It is bounded by `norm_zetaRemainder_le`. -/
noncomputable abbrev zetaRemainder (s : ℂ) (M N : ℕ) : ℂ :=
  ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
      * (ascPochhammer ℂ (2 * M + 1)).eval s
      * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)

/-- The Euler–Maclaurin right-hand side `zetaEMExpansion` splits as its approximant plus its
remainder. -/
theorem zetaEMExpansion_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) :
    zetaEMExpansion s M N = zetaApproximant s M N + zetaRemainder s M N := by
  rw [zetaEMExpansion, zetaApproximant, zetaRemainder]; ring

set_option maxHeartbeats 1600000 in
/-- Analyticity of the continued Euler–Maclaurin right-hand side. For `1 ≤ N`, the map
`s ↦ zetaEMExpansion s M N` is analytic on the punctured strip `{Re s > -(2M+1)} \ {1}`. -/
theorem analyticOnNhd_zetaEMExpansion (M N : ℕ) (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ zetaEMExpansion s M N)
      ({s : ℂ | (-(2 * M + 1 : ℝ)) < s.re} \ {1}) := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
  refine DifferentiableOn.analyticOnNhd ?_
    ((isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton)
  simp only [zetaEMExpansion]
  refine DifferentiableOn.add (DifferentiableOn.add (DifferentiableOn.add
    (DifferentiableOn.add (DifferentiableOn.add ?_ ?_) ?_) ?_) ?_) ?_
  · -- `∑_{n=1}^{N-1} n^{-s}`
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun n hn ↦ ?_)
    have : (n : ℂ) ≠ 0 := by
      rw [Finset.mem_Ico] at hn; exact_mod_cast Nat.one_le_iff_ne_zero.mp hn.1
    exact differentiable_id.neg.const_cpow (Or.inl this)
  · -- `N^{1-s}/(s-1)`
    apply DifferentiableOn.div
    · exact (((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow
        (Or.inl hNne)).differentiableOn
    · exact (differentiable_id.sub_const 1).differentiableOn
    · intro s hs; exact sub_ne_zero.mpr hs.2
  · -- `N^{-s}/2`
    exact ((differentiable_id.neg.const_cpow (Or.inl hNne)).div_const 2).differentiableOn
  · -- `∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)}`
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun k _ ↦ ?_)
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * k - 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  · -- `t_{M+1}` term
    refine Differentiable.differentiableOn ?_
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * M + 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  · -- the order-`(2M+2)` remainder
    refine (Complex.differentiableOn_eulerMaclaurinRemainderIoi_cpow (2 * M + 2) N hN).mono
      fun s hs ↦ ?_
    have hs1 : (-(2 * M + 1 : ℝ)) < s.re := hs.1
    rw [Set.mem_ofPred_eq]
    push_cast
    linarith

/-- Euler–Maclaurin expansion of `ζ` on the punctured strip `Re s > -(2M+1)`. For `1 ≤ N`,
`Re s > -(2M+1)` and `s ≠ 1`, `ζ(s) = zetaEMExpansion s M N`, i.e.
`ζ(s) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
          + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)} + R_M(s, N)`. -/
theorem riemannZeta_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = zetaEMExpansion s M N := by
  set H : Set ℂ := {z : ℂ | (-(2 * M + 1 : ℝ)) < z.re} with hHdef
  set U : Set ℂ := H \ {1} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hζ : AnalyticOnNhd ℂ riemannZeta U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hUopen
  have hE : AnalyticOnNhd ℂ (fun z ↦ zetaEMExpansion z M N) U :=
    analyticOnNhd_zetaEMExpansion M N hN
  -- Preconnectedness of the punctured half-plane, via four convex half-space pieces glued at
  -- `I`, `-I` and `2 + I`.
  have hP : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  have hcH : Convex ℝ H := convex_halfSpace_re_gt _
  have hmH : ∀ z : ℂ, 0 ≤ z.re → z ∈ H := fun z hz ↦ by
    simp only [hHdef, Set.mem_ofPred_eq]; linarith [hP]
  have hA : IsPreconnected ({z : ℂ | 0 < z.im} ∩ H) :=
    ((convex_halfSpace_im_gt 0).inter hcH).isPreconnected
  have hB : IsPreconnected ({z : ℂ | z.im < 0} ∩ H) :=
    ((convex_halfSpace_im_lt 0).inter hcH).isPreconnected
  have hC : IsPreconnected ({z : ℂ | z.re < 1} ∩ H) :=
    ((convex_halfSpace_re_lt 1).inter hcH).isPreconnected
  have hD : IsPreconnected ({z : ℂ | 1 < z.re} ∩ H) :=
    ((convex_halfSpace_re_gt 1).inter hcH).isPreconnected
  have hUconn : IsPreconnected U := by
    have hUV : U = (({z : ℂ | 0 < z.im} ∩ H) ∪ ({z : ℂ | z.re < 1} ∩ H)
          ∪ ({z : ℂ | z.im < 0} ∩ H)) ∪ ({z : ℂ | 1 < z.re} ∩ H) := by
      ext z
      simp only [hUdef, hHdef, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hre, hne⟩
        rcases lt_trichotomy z.im 0 with him | him | him
        · exact .inl (.inr ⟨him, hre⟩)
        · rcases lt_trichotomy z.re 1 with hlt | heq | hgt
          · exact .inl (.inl (.inr ⟨hlt, hre⟩))
          · exact absurd (Complex.ext (heq.trans Complex.one_re.symm)
              (him.trans Complex.one_im.symm)) hne
          · exact .inr ⟨hgt, hre⟩
        · exact .inl (.inl (.inl ⟨him, hre⟩))
      · rintro (((⟨h, hre⟩ | ⟨h, hre⟩) | ⟨h, hre⟩) | ⟨h, hre⟩) <;>
          exact ⟨hre, by rintro rfl; simp only [Complex.one_im, Complex.one_re] at h; linarith⟩
    -- glue the four convex pieces at `I`, `-I` and `2 + I`
    have mem : ∀ z : ℂ, ∀ S : Set ℂ, z ∈ S → 0 ≤ z.re → z ∈ S ∩ H := fun _ _ h hz ↦ ⟨h, hmH _ hz⟩
    rw [hUV]
    apply IsPreconnected.union (2 + Complex.I) ?_ ?_ ?_ hD
    · exact Or.inl (Or.inl (mem _ _ (by simp) (by simp)))
    · exact mem _ _ (by simp) (by simp)
    · apply IsPreconnected.union (-Complex.I) ?_ ?_ ?_ hB
      · exact Or.inr (mem _ _ (by simp) (by simp))
      · exact mem _ _ (by simp) (by simp)
      · exact IsPreconnected.union Complex.I (mem _ _ (by simp) (by simp))
          (mem _ _ (by simp) (by simp)) hA hC
  have hagree : riemannZeta =ᶠ[𝓝 (2 : ℂ)] (fun z ↦ zetaEMExpansion z M N) := by
    have hopen : IsOpen {w : ℂ | (1 : ℝ) < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (x := (2:ℂ)) (by simp)] with z hz
    have hz1 : 1 < z.re := hz
    rw [riemannZeta_eq_of_one_lt_re z hz1 M N hN]
    simp only [zetaEMExpansion]
    rw [Complex.eulerMaclaurinRemainderIoi_succ_eq z M N hN (by linarith : -(2 * M : ℝ) < z.re)]
    ring
  exact hζ.eqOn_of_preconnected_of_eventuallyEq hE hUconn ⟨hmH _ (by simp), by simp⟩ hagree
    ⟨hs, hs1⟩

/-- The Euler–Maclaurin expansion of `ζ` as approximant plus remainder. For `1 ≤ N`,
`Re s > -(2M+1)` and `s ≠ 1`, `riemannZeta s = zetaApproximant s M N + zetaRemainder s M N`. -/
theorem riemannZeta_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaApproximant s M N + zetaRemainder s M N := by
  rw [riemannZeta_eq s M N hN hs hs1, zetaEMExpansion_eq_approximant_add_remainder]

/-- The first-order Euler–Maclaurin representation of `ζ`. For `0 < Re s` and `s ≠ 1`,
`ζ(s) = 1/(s-1) + 1/2 + R₁(s)`, with the order-`1` improper remainder
`R₁(s) = Complex.eulerMaclaurinRemainderIoi 1 (y ↦ y^{-s}) 1`. -/
theorem riemannZeta_eq_order_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2
      + Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (1 : ℝ) := by
  have h2 := Complex.eulerMaclaurinRemainderIoi_succ_eq s 0 1 le_rfl (by push_cast; linarith)
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow] at h2
  rw [riemannZeta_eq s 0 1 le_rfl (by push_cast; linarith) hs1, zetaEMExpansion]
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow, Finset.Ico_self,
    Finset.sum_empty, show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by lia)]
  linear_combination -h2

/-- `Re ζ(x) < 0` for real `x ∈ (0, 1)`. -/
theorem riemannZeta_ofReal_re_neg_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hs1 : (x : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; linarith
  rw [riemannZeta_eq_order_one (by simpa using hx0) hs1, Complex.add_re, Complex.add_re,
    show (1 / ((x : ℂ) - 1)).re = 1 / (x - 1) from by
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_one,
        ← Complex.ofReal_div, Complex.ofReal_re],
    show ((1 : ℂ) / 2).re = 1 / 2 from by norm_num]
  have hRre := (Complex.re_le_norm _).trans
    (Complex.norm_eulerMaclaurinRemainderIoi_one_ofReal_le hx0)
  have hlt : 1 / (x - 1) < -1 := by
    rw [div_lt_iff_of_neg (show x - 1 < 0 by linarith)]; linarith
  linarith

end

/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/






/-!
# The Olver–Borwein error bound for the Euler–Maclaurin expansion of `ζ`

The sharp bound on the `ζ` remainder `zetaRemainder` (`thm:zeta_error_bound`), together with the
sign and Fourier properties of the centered even Bernoulli kernel `B̃_{2m} - B_{2m}` it rests on.
Here `B̃_{2m}(x) = bernoulliFun (2m) (Int.fract x)` is the periodized even Bernoulli function and
`B_{2m} = bernoulli (2m)` the Bernoulli number.

## Main results

- `bernoulliFun_sub_self_eq_tsum_cos`: the cosine–Fourier expansion
  `B̃_{2m}(x) - B_{2m} = (-1)^{m+1} A_m ∑_k (cos(2πkx) - 1)/k^{2m}`, `A_m = 2(2m)!/(2π)^{2m}`.
- `centered_kernel_mul_sign_nonneg`: the centered kernel has constant sign `(-1)^m`.
- `integral_abs_bernoulliFun_sub_self`: the period-mean
  `∫_0^1 |bernoulliFun (2m) x - B_{2m}| dx = |B_{2m}|`.
- `integral_Ioi_cos_mul_rpow_nonneg`: Pólya's positivity lemma,
  `∫_N^∞ cos(2πkx) x^{-a} dx ≥ 0` for `N ≥ 1` and `a > 1`.
- `integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le`: the weighted averaging bound.
- `zetaRemainder_eq_integral_bernoulliFun_fract_sub`: the centered-kernel representation of the
  `ζ` remainder.
- `norm_zetaRemainder_le`: the error bound `‖R_M(s,N)‖ ≤ zetaRemainderBound s M N`.
-/
section


open MeasureTheory Real Filter Topology
open scoped Nat

/-- If `0 ≤ (-1)^m * y`, the sign `(-1)^m` pulls out of the absolute value: `|y| = (-1)^m * y`. -/
private theorem abs_eq_neg_one_pow_mul {m : ℕ} {y : ℝ} (h : 0 ≤ (-1 : ℝ) ^ m * y) :
    |y| = (-1 : ℝ) ^ m * y := by
  rw [← abs_of_nonneg h, abs_mul, abs_neg_one_pow, one_mul]

/-- The even zeta value `∑_{n} 1/n^{2m} = (-1)^{m+1} (2π)^{2m} / (2·(2m)!) · B_{2m}` (mathlib's
`hasSum_zeta_nat`, with the factor `(2π)^{2m}/2` in place of `2^{2m-1} π^{2m}`). -/
private theorem hasSum_one_div_nat_pow_bernoulli (m : ℕ) (hm0 : m ≠ 0) :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m))
      ((-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)) := by
  have h2 : (2 : ℝ) ^ (2 * m - 1) * 2 = 2 ^ (2 * m) := by rw [← pow_succ]; congr 1; lia
  rw [show (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)
        = (-1 : ℝ) ^ (m + 1) * 2 ^ (2 * m - 1) * π ^ (2 * m) * (bernoulli (2 * m) : ℝ)
            / (2 * m)! from by rw [mul_pow, ← h2]; ring]
  exact hasSum_zeta_nat hm0

/-- Centered cosine–Fourier expansion of the periodized even Bernoulli kernel. For `m ≥ 1`
and all `x ∈ ℝ`, with `A_m = 2(2m)!/(2π)^{2m}`,
`bernoulliFun (2m) (Int.fract x) - B_{2m} = (-1)^{m+1} A_m ∑_k (cos(2πkx) - 1)/k^{2m}`. -/
theorem bernoulliFun_sub_self_eq_tsum_cos (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)
      = (-1 : ℝ) ^ (m + 1) * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
          * ∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m) := by
  have hm0 : m ≠ 0 := by lia
  set B : ℝ := bernoulliFun (2 * m) (Int.fract x)
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Cval : ℝ := (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! with hCval
  have hfracmem : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  -- cosine periodicity: `cos(2πn·fract x) = cos(2πnx)`.
  have hcos : ∀ n : ℕ, cos (2 * π * n * Int.fract x) = cos (2 * π * n * x) := by
    intro n
    have heq : (2 : ℝ) * π * n * x
        = 2 * π * n * Int.fract x + ((n : ℤ) * ⌊x⌋ : ℤ) * (2 * π) := by
      have := Int.floor_add_fract x
      push_cast
      linear_combination (-(2 * π * (n : ℝ))) * this
    rw [heq, Real.cos_add_int_mul_two_pi]
  -- the Fourier expansion at `fract x`, with `cos` argument unwrapped to `x`.
  have hsx : HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * m) * cos (2 * π * n * x)) (Cval * B) := by
    have h := hasSum_one_div_nat_pow_mul_cos hm0 hfracmem
    rw [show (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * m))).eval (Int.fract x)
          = B from rfl] at h
    simpa only [hcos] using h
  -- the same expansion at `x = 0`, giving the Bernoulli number.
  have hs0 : HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m)) (Cval * b) :=
    hasSum_one_div_nat_pow_bernoulli m hm0
  -- subtract and identify the tsum.
  have hdiff := hsx.sub hs0
  have key : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) = Cval * B - Cval * b := by
    rw [← hdiff.tsum_eq]; exact tsum_congr fun n ↦ by ring
  rw [key, hCval]
  -- final algebra: `(-1)^{m+1} A_m · Cval = 1`.
  set a : ℝ := (-1 : ℝ) ^ (m + 1) with ha
  have ha2 : a * a = 1 := by rw [ha, ← pow_add]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
  have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
  have hfac : ((2 * m)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hEF : a * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
      * (a * (2 * π) ^ (2 * m) / 2 / (2 * m)!) = 1 := by
    field_simp; linear_combination ha2
  linear_combination (-(B - b)) * hEF

/-- Constant sign of the centered even Bernoulli kernel. For `m ≥ 1` and all `x`,
`(-1)^m (B̃_{2m}(x) - B_{2m}) ≥ 0`. -/
theorem centered_kernel_mul_sign_nonneg (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    0 ≤ (-1 : ℝ) ^ m * (bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)) := by
  have hA : (0 : ℝ) ≤ 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) := by positivity
  have hS : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) ≤ 0 :=
    tsum_nonpos fun n ↦
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (Real.cos_le_one _)) (by positivity)
  have hs3 : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
  rw [bernoulliFun_sub_self_eq_tsum_cos m hm x, ← mul_assoc, ← mul_assoc, hs3]
  linarith [mul_nonneg hA (neg_nonneg.mpr hS)]

/-- Period-mean of the centered even Bernoulli kernel. For `m ≥ 1`,
`∫_0^1 |bernoulliFun (2m) x - B_{2m}| dx = |B_{2m}|`. The integrand uses the Bernoulli polynomial
`bernoulliFun (2m)`, which agrees on `[0,1)` with the periodized kernel `B̃_{2m}`. -/
theorem integral_abs_bernoulliFun_sub_self (m : ℕ) (hm : 1 ≤ m) :
    ∫ x in (0 : ℝ)..1, |bernoulliFun (2 * m) x - (bernoulli (2 * m) : ℝ)|
      = |(bernoulli (2 * m) : ℝ)| := by
  have hm2 : 2 * m ≠ 0 := by lia
  set b : ℝ := (bernoulli (2 * m) : ℝ) with hb
  -- pointwise constant sign on `[0,1]`.
  have hpt : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      |bernoulliFun (2 * m) x - b| = (-1) ^ m * (bernoulliFun (2 * m) x - b) := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    obtain ⟨hx0, hx1⟩ := hx
    rcases eq_or_lt_of_le hx1 with hx1' | hx1'
    · rw [hx1', bernoulliFun_endpoints_eq_of_ne_one (by lia : 2 * m ≠ 1), bernoulliFun_eval_zero,
        ← hb, sub_self, abs_zero, mul_zero]
    · have hfx : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0, hx1'⟩
      have hsign := centered_kernel_mul_sign_nonneg m hm x
      rw [hfx, ← hb] at hsign
      exact abs_eq_neg_one_pow_mul hsign
  -- evaluate the integral via the pulled-out sign.
  have hval : (∫ x in (0 : ℝ)..1, |bernoulliFun (2 * m) x - b|) = -((-1) ^ m * b) := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (intervalIntegrable_bernoulliFun (2 * m) 0 1)
        (intervalIntegrable_const),
      integral_bernoulliFun_eq_zero hm2, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, one_mul, zero_sub, mul_neg]
  have hnn : (0 : ℝ) ≤ -((-1) ^ m * b) :=
    hval ▸ intervalIntegral.integral_nonneg zero_le_one fun x _ ↦ abs_nonneg _
  rw [hval, ← abs_of_nonneg hnn, abs_neg, abs_mul, abs_neg_one_pow, one_mul]

/-- Integrability on `(N, ∞)` of a `[-1, 1]`-bounded continuous function times the weight `x ^ q`,
for `q < -1` and `0 < N`. -/
private theorem integrableOn_Ioi_of_bound_mul_rpow {f : ℝ → ℝ} (hf : Continuous f)
    (hbound : ∀ x, |f x| ≤ 1) {q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ f x * x ^ q) (Set.Ioi N) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hq hN)
    ((hf.continuousOn.mul (fun x hx ↦
      (Real.continuousAt_rpow_const x q
        (Or.inl (hN.trans (Set.mem_Ioi.mp hx)).ne')).continuousWithinAt)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hN.trans (Set.mem_Ioi.mp hx)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (hbound x)

/-- Integrability on `(N, ∞)` of `x ↦ sin (ω x) · x ^ q` for `q < -1` and `0 < N`. -/
private theorem integrableOn_Ioi_sin_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ sin (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) hq hN

/-- Integrability on `(N, ∞)` of `x ↦ cos (ω x) · x ^ q` for `q < -1` and `0 < N`. -/
private theorem integrableOn_Ioi_cos_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ cos (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) hq hN

/-- Positivity of the weighted sine integral. For `p > 1` and integers `N, k ≥ 1`,
`∫_N^∞ sin(2πkx) x^{-p} dx ≥ 0`. -/
private theorem integral_Ioi_sin_mul_rpow_nonneg {p : ℝ} (hp : 1 < p) {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (2 * π * k * x) * x ^ (-p) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  set T : ℝ := 1 / (2 * (k : ℝ)) with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hωT : ω * T = π := by rw [hω, hT]; field_simp
  set A : ℕ → ℝ := fun j ↦ (N : ℝ) + j * T with hA
  have hAsucc : ∀ j, A (j + 1) = A j + T := fun j ↦ by simp only [hA]; push_cast; ring
  have hApos : ∀ j, 0 < A j := fun j ↦ by simp only [hA]; positivity
  have hAle : ∀ j, A j ≤ A (j + 1) := fun j ↦ by rw [hAsucc]; linarith
  set g : ℝ → ℝ := fun x ↦ sin (ω * x) * x ^ (-p) with hg
  -- `c j` is the `j`-th half-period mass, written on the *shifted* window `[0, T]`.
  set c : ℕ → ℝ := fun j ↦ ∫ u in (0 : ℝ)..T, sin (ω * u) * (A j + u) ^ (-p) with hc
  have hsincont : Continuous fun x : ℝ ↦ sin (ω * x) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hrpow : ContinuousOn (fun x : ℝ ↦ x ^ (-p)) (Set.Ioi (0 : ℝ)) := fun x hx ↦
    (Real.continuousAt_rpow_const x (-p) (Or.inl (Set.mem_Ioi.mp hx).ne')).continuousWithinAt
  have hgint : ∀ j, IntervalIntegrable g volume (A j) (A (j + 1)) := fun j ↦
    (hsincont.continuousOn.mul (hrpow.mono fun x hx ↦ by
      rw [Set.uIcc_of_le (hAle j)] at hx
      exact lt_of_lt_of_le (hApos j) hx.1)).intervalIntegrable
  have hcint : ∀ j, IntervalIntegrable
      (fun u ↦ sin (ω * u) * (A j + u) ^ (-p)) volume 0 T := fun j ↦ by
    refine (hsincont.continuousOn.mul (ContinuousOn.rpow_const
      (continuous_const.add continuous_id).continuousOn fun u hu ↦ Or.inl ?_)).intervalIntegrable
    rw [Set.uIcc_of_le hT0.le] at hu
    exact (by linarith [hApos j, hu.1] : (0 : ℝ) < A j + u).ne'
  -- `sin (ω ·)` is nonnegative on the shifted window, since `ω T = π`.
  have hsinu : ∀ u ∈ Set.Icc (0 : ℝ) T, 0 ≤ sin (ω * u) := fun u hu ↦
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hω0.le hu.1)
      (by linarith [mul_le_mul_of_nonneg_left hu.2 hω0.le, hωT])
  -- antitonicity is now pointwise: the weight `(A j + u)^(-p)` decreases in `j`.
  have hcanti : Antitone c := antitone_nat_of_succ_le fun j ↦ by
    simp only [hc]
    refine intervalIntegral.integral_mono_on hT0.le (hcint (j + 1)) (hcint j) fun u hu ↦ ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
      (by linarith [hApos j, hu.1]) (by linarith [hAsucc j, hT0]) (by linarith)) (hsinu u hu)
  -- each signed piece-integral equals `(-1)^j c j`: on `[A j, A j + T]`, `sin (ω x) =
  -- (-1)^j sin (ω (x - A j))` because `ω A j = (j + 2kN) π`.
  have hpiece : ∀ j, (∫ x in A j..A (j + 1), g x) = (-1 : ℝ) ^ j * c j := fun j ↦ by
    rw [show (∫ x in A j..A (j + 1), g x) = ∫ u in (0 : ℝ)..T, g (A j + u) from by
      rw [intervalIntegral.integral_comp_add_left g (A j), add_zero, ← hAsucc j]]
    simp only [hc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    have key : sin (ω * (A j + u)) = (-1 : ℝ) ^ j * sin (ω * u) := by
      rw [show ω * (A j + u) = ω * u + ((j + 2 * k * N : ℕ) : ℝ) * π by
            simp only [hA, hω, hT]; field_simp; push_cast; ring,
        Real.sin_add_nat_mul_pi,
        show ((-1 : ℝ)) ^ (j + 2 * k * N) = (-1 : ℝ) ^ j by
          rw [pow_add, show 2 * k * N = 2 * (k * N) by ring, pow_mul]; norm_num]
    simp only [hg, key]
    ring
  -- the finite sums of the alternating series are the truncated improper integrals
  have hA0 : A 0 = (N : ℝ) := by simp [hA]
  have hpartial : ∀ n, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i = ∫ x in (N : ℝ)..A n, g x :=
    fun n ↦ by
      rw [← hA0, ← intervalIntegral.sum_integral_adjacent_intervals
        (f := g) fun k (_ : k < n) ↦ hgint k]
      exact Finset.sum_congr rfl fun i _ ↦ (hpiece i).symm
  -- the truncated integrals converge to the improper integral
  have hgintegrable : IntegrableOn g (Set.Ioi (N : ℝ)) := by
    rw [hg]; exact integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  have hAtop : Tendsto A atTop atTop :=
    (tendsto_atTop_add_const_left atTop (N : ℝ)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hT0)).congr fun _ ↦ rfl
  have htend_sum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i) atTop
      (𝓝 (∫ x in Set.Ioi (N : ℝ), g x)) :=
    (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hgintegrable hAtop).congr
      fun n ↦ (hpartial n).symm
  simpa using Antitone.alternating_series_le_tendsto htend_sum hcanti 0

/-- Pólya's positivity lemma (1918). For an integer `N ≥ 1`, a real `a > 1`, and any natural
`k`, `∫_N^∞ cos(2πkx) x^{-a} dx ≥ 0`. -/
theorem integral_Ioi_cos_mul_rpow_nonneg {a : ℝ} (ha : 1 < a) {N k : ℕ} (hN : 1 ≤ N) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), cos (2 * π * k * x) * x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine setIntegral_nonneg measurableSet_Ioi fun x hx ↦ ?_
    simpa using Real.rpow_nonneg (hN0.trans hx).le (-a)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  -- the conjugate sine integral is nonnegative (`p = a + 1 > 1`)
  have hJ : 0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (ω * x) * x ^ (-(a + 1)) := by
    rw [hω]; exact integral_Ioi_sin_mul_rpow_nonneg (p := a + 1) (by linarith) hN hk
  -- the cosine and sine tail integrands are integrable on `(N, ∞)`
  have hcoscont : Continuous fun x : ℝ ↦ cos (ω * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcosint : IntegrableOn (fun x ↦ cos (ω * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cos_mul_rpow (by linarith) hN0
  have hsinint : IntegrableOn (fun x ↦ sin (ω * x) * x ^ (-(a + 1))) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  -- the boundary value `sin (ω N)` vanishes
  have hsinN : sin (ω * N) = 0 := by
    rw [show ω * (N : ℝ) = ((2 * k * N : ℕ) : ℝ) * π by rw [hω]; push_cast; ring]
    exact Real.sin_nat_mul_pi _
  -- integration by parts: `∫_N^R cos·x^{-a} = R^{-a} sin(ωR)/ω + (a/ω) ∫_N^R sin·x^{-(a+1)}`
  have hrel : ∀ᶠ R in atTop, (∫ x in (N : ℝ)..R, cos (ω * x) * x ^ (-a))
      = R ^ (-a) * sin (ω * R) / ω
        + a / ω * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) := by
    filter_upwards [eventually_ge_atTop (N : ℝ)] with R hR
    have hne : ∀ x ∈ Set.uIcc (N : ℝ) R, x ≠ 0 := fun x hx ↦ by
      rw [Set.uIcc_of_le hR] at hx; exact (lt_of_lt_of_le hN0 hx.1).ne'
    have hu : ∀ x ∈ Set.uIcc (N : ℝ) R, HasDerivAt (fun x ↦ x ^ (-a)) (-a * x ^ (-(a + 1))) x :=
      fun x hx ↦ by
        have hd := hasDerivAt_rpow_const (x := x) (p := -a) (Or.inl (hne x hx))
        rwa [show -a - 1 = -(a + 1) by ring] at hd
    have hv : ∀ x ∈ Set.uIcc (N : ℝ) R,
        HasDerivAt (fun x ↦ sin (ω * x) / ω) (cos (ω * x)) x := fun x _ ↦ by
      have h2 : HasDerivAt (fun t ↦ sin (ω * t)) (cos (ω * x) * ω) x :=
        (Real.hasDerivAt_sin (ω * x)).comp x (by simpa using (hasDerivAt_id x).const_mul ω)
      have h3 := h2.div_const ω
      rwa [mul_div_assoc, div_self hω0.ne', mul_one] at h3
    have hu'int : IntervalIntegrable (fun x ↦ -a * x ^ (-(a + 1))) volume (N : ℝ) R :=
      (continuousOn_const.mul fun x hx ↦
        (Real.continuousAt_rpow_const x (-(a + 1))
          (Or.inl (hne x hx))).continuousWithinAt).intervalIntegrable
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int
      (hcoscont.intervalIntegrable _ _)
    rw [intervalIntegral.integral_congr fun x _ ↦ mul_comm (x ^ (-a)) (cos (ω * x))] at hibp
    rw [hibp, show (∫ x in (N : ℝ)..R, -a * x ^ (-(a + 1)) * (sin (ω * x) / ω))
          = -(a / ω) * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun x _ ↦ by ring, hsinN]
    ring
  -- pass to the limit `R → ∞`
  have hbdry : Tendsto (fun R : ℝ ↦ R ^ (-a) * sin (ω * R) / ω) atTop (𝓝 0) := by
    have hb0 : Tendsto (fun R : ℝ ↦ R ^ (-a) / ω) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < a by linarith)).div_const ω
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRa : (0 : ℝ) ≤ R ^ (-a) := Real.rpow_nonneg hR.le _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hω0, abs_mul, abs_of_nonneg hRa,
      div_le_div_iff_of_pos_right hω0]
    simpa using mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨Real.neg_one_le_sin (ω * R), Real.sin_le_one (ω * R)⟩) hRa
  have heq := tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hcosint tendsto_id).congr' hrel)
    (hbdry.add ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hsinint
      tendsto_id).const_mul (a / ω)))
  rw [heq, zero_add]
  exact mul_nonneg (div_nonneg (by linarith) hω0.le) hJ

/-- Centered-kernel representation of the `ζ` remainder. For `1 ≤ N` and `Re s > -(2M+1)`,
the remainder `zetaRemainder` is a single integral of the *centered* even Bernoulli kernel:
`R_M(s, N) = -(s)_{2M+2}/(2M+2)! · ∫_N^∞ (B̃_{2M+2}(x) - B_{2M+2}) x^{-s-(2M+2)} dx`. -/
theorem zetaRemainder_eq_integral_bernoulliFun_fract_sub (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) :
    zetaRemainder s M N
      = -((ascPochhammer ℂ (2 * M + 2)).eval s / ((2 * M + 2)! : ℂ))
          * ∫ x in Set.Ioi (N : ℝ),
              ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
                * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ)) := by
  rw [zetaRemainder, Complex.eulerMaclaurinRemainderIoi_cpow_eq s (2 * M + 2) N]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℕ := 2 * M + 2 with hp
  set w : ℂ := -s - (p : ℂ) with hw
  have hwre : w.re < -1 := by
    rw [hw, Complex.sub_re, Complex.neg_re, Complex.natCast_re, hp]; push_cast; linarith
  have hxint : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ w) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hwre hN0
  have hBint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := Complex.integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hwre
  have hsubint : IntegrableOn
      (fun x : ℝ ↦ ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) :=
    (hBint.sub (hxint.const_mul ((bernoulli p : ℝ) : ℂ))).congr
      (.of_forall fun x ↦ by simp only [Pi.sub_apply]; push_cast; ring)
  have hsplit : (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      = (∫ x in Set.Ioi (N : ℝ),
            ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
        + ((bernoulli p : ℝ) : ℂ) * ∫ x in Set.Ioi (N : ℝ), (x : ℂ) ^ w := by
    rw [show (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
          = ∫ x in Set.Ioi (N : ℝ),
              (((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w
                + ((bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w) from
        setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ by push_cast; ring),
      integral_add hsubint (hxint.const_mul ((bernoulli p : ℝ) : ℂ)), integral_const_mul]
  rw [hsplit, integral_Ioi_cpow_of_lt hwre hN0]
  have hwone : w + 1 = -s - ((2 * M + 1 : ℕ) : ℂ) := by rw [hw, hp]; push_cast; ring
  have hPp : (ascPochhammer ℂ p).eval s
      = (ascPochhammer ℂ (2 * M + 1)).eval s * (s + ((2 * M + 1 : ℕ) : ℂ)) := by
    rw [show p = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval]
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  have hden : -s - ((2 * M + 1 : ℕ) : ℂ) ≠ 0 := fun h ↦ by
    have hre : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at hre
    push_cast at hre; linarith
  rw [hwone, hPp]
  push_cast at hden hpne ⊢
  field_simp
  ring

/-- Weighted averaging bound for the centered kernel. For `m ≥ 1`, real `a > 1`, and integer
`N ≥ 1`, `∫_N^∞ |B̃_{2m}(x) - B_{2m}| x^{-a} dx ≤ |B_{2m}| ∫_N^∞ x^{-a} dx`. -/
theorem integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (m : ℕ) (hm : 1 ≤ m) {a : ℝ}
    (ha : 1 < a) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)| * x ^ (-a)
      ≤ |(bernoulli (2 * m) : ℝ)| * ∫ x in Set.Ioi (N : ℝ), x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  have hxa_neg : -a < -1 := by linarith
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Am : ℝ := 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) with hAm
  have hAm0 : 0 < Am := by rw [hAm]; positivity
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  have hweight_int : IntegrableOn (fun x : ℝ ↦ x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hxa_neg hN0
  have hcos_int : ∀ k : ℕ,
      IntegrableOn (fun x ↦ cos (2 * π * (k : ℝ) * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) := fun _ ↦
    integrableOn_Ioi_cos_mul_rpow hxa_neg hN0
  -- the family of nonnegative termwise integrands.
  set f : ℕ → ℝ → ℝ :=
    fun k x ↦ Am / (k : ℝ) ^ (2 * m) * (1 - cos (2 * π * (k : ℝ) * x)) * x ^ (-a) with hf
  have hf_int : ∀ k, IntegrableOn (f k) (Set.Ioi (N : ℝ)) := fun k ↦
    ((hweight_int.sub (hcos_int k)).const_mul (Am / (k : ℝ) ^ (2 * m))).congr <| by
      filter_upwards with x
      simp only [hf, Pi.sub_apply]; ring
  have hf_nonneg : ∀ k, ∀ x ∈ Set.Ioi (N : ℝ), 0 ≤ f k x := fun k x hx ↦ by
    simp only [hf]
    exact mul_nonneg (mul_nonneg (div_nonneg hAm0.le (by positivity))
        (by linarith [Real.cos_le_one (2 * π * (k : ℝ) * x)]))
      (Real.rpow_nonneg (lt_trans hN0 hx).le _)
  -- bound for each termwise integral: `∫ f_k = Am/k^{2m}·(W - Iᶜ) ≤ Am/k^{2m}·W`.
  have hbound : ∀ k, (∫ x in Set.Ioi (N : ℝ), f k x) ≤ Am / (k : ℝ) ^ (2 * m) * W := fun k ↦ by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x _ ↦
      show f k x = Am / (k : ℝ) ^ (2 * m) * (x ^ (-a) - cos (2 * π * (k : ℝ) * x) * x ^ (-a))
        by simp only [hf]; ring, integral_const_mul, integral_sub hweight_int (hcos_int k)]
    exact mul_le_mul_of_nonneg_left
      (by linarith [integral_Ioi_cos_mul_rpow_nonneg (a := a) (N := N) (k := k) ha hN])
      (div_nonneg hAm0.le (by positivity))
  -- summability of the bounding series `∑ Am/k^{2m} · W` and hence of `∑ ∫ f_k`.
  have hsummable_bound : Summable (fun k : ℕ ↦ Am / (k : ℝ) ^ (2 * m) * W) :=
    ((((Real.summable_one_div_nat_pow (p := 2 * m)).mpr (by lia)).mul_left Am).congr
      fun k ↦ by ring).mul_right W
  have hsummable_int : Summable (fun k : ℕ ↦ ∫ x in Set.Ioi (N : ℝ), f k x) :=
    Summable.of_nonneg_of_le
      (fun k ↦ setIntegral_nonneg measurableSet_Ioi (hf_nonneg k)) hbound hsummable_bound
  -- the centered kernel as a nonnegative cosine series.
  have habs : ∀ x : ℝ, |bernoulliFun (2 * m) (Int.fract x) - b|
      = Am * ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m) := fun x ↦ by
    rw [abs_eq_neg_one_pow_mul (centered_kernel_mul_sign_nonneg m hm x),
      bernoulliFun_sub_self_eq_tsum_cos m hm x,
      show ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)
          = -∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m) from by
        rw [← tsum_neg]; exact tsum_congr fun k ↦ by ring]
    have hsq : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
    linear_combination
      (Am * ∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m)) * hsq
  -- assemble: Tonelli, then drop the nonnegative cosine integrals.
  calc ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - b| * x ^ (-a)
      = ∫ x in Set.Ioi (N : ℝ), ∑' k : ℕ, f k x :=
        setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ by
          rw [tsum_congr fun k ↦ show f k x
                = Am * ((1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)) * x ^ (-a) by
              simp only [hf]; ring, tsum_mul_right, tsum_mul_left, ← habs x]
    _ = ∑' k : ℕ, ∫ x in Set.Ioi (N : ℝ), f k x :=
        (integral_tsum_of_summable_integral_norm hf_int (hsummable_int.congr fun k ↦
          setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
            (Real.norm_of_nonneg (hf_nonneg k x hx)).symm)).symm
    _ ≤ ∑' k : ℕ, Am / (k : ℝ) ^ (2 * m) * W :=
        hsummable_int.tsum_mono hsummable_bound hbound
    _ = |b| * W := by
        -- `Am · ζ(2m) = (-1)^{m+1} B_{2m} = |B_{2m}|`.
        have hAmζ : (∑' k : ℕ, Am / (k : ℝ) ^ (2 * m)) = (-1 : ℝ) ^ (m + 1) * b := by
          have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
          have hfac : ((2 * m)! : ℝ) ≠ 0 := by positivity
          rw [tsum_congr fun k : ℕ ↦ div_eq_mul_one_div Am ((k : ℝ) ^ (2 * m)), tsum_mul_left,
            (hasSum_one_div_nat_pow_bernoulli m (by lia)).tsum_eq, hAm]
          field_simp
          ring
        have hnn : 0 ≤ (-1 : ℝ) ^ (m + 1) * b :=
          hAmζ ▸ tsum_nonneg fun k ↦ div_nonneg hAm0.le (by positivity)
        rw [tsum_mul_right, hAmζ, ← abs_eq_neg_one_pow_mul hnn]

/-- The explicit Euler–Maclaurin remainder bound for `ζ`, `K · ‖t_{M+1}(s,N)‖`, with the
constant `K = ‖s + (2M+1)‖ / (Re s + (2M+1))` and the leading Bernoulli term
`t_{M+1}(s,N) = B_{2M+2}/(2M+2)! · (s)_{2M+1} · N^{-s-(2M+1)}`. -/
noncomputable abbrev zetaRemainderBound (s : ℂ) (M N : ℕ) : ℝ :=
  ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ / (s.re + ((2 * M + 1 : ℕ) : ℝ))
    * ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖

/-- Borwein error bound. For `1 ≤ N` and `Re s > -(2M+1)`, the Euler–Maclaurin remainder for
`ζ` is bounded by the first omitted term, scaled by `K = |s+2M+1|/(Re s+2M+1) ≥ 1`
(`thm:zeta_error_bound`). -/
theorem norm_zetaRemainder_le (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re) :
    ‖zetaRemainder s M N‖ ≤ zetaRemainderBound s M N := by
  simp only [zetaRemainderBound]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := s.re + ((2 * M + 2 : ℕ) : ℝ) with ha_def
  have ha : 1 < a := by rw [ha_def]; push_cast; linarith
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  -- real part of the complex exponent equals `-a`.
  have hwre : (-s - ((2 * M + 2 : ℕ) : ℂ)).re = -a := by
    rw [ha_def]; simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; ring
  have hre1 : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
  have hrel : -a + 1 = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by rw [ha_def]; push_cast; ring
  -- norm of the Pochhammer prefactor splits via `(s)_{2M+2} = (s)_{2M+1}(s+2M+1)`.
  have hP : ‖(ascPochhammer ℂ (2 * M + 2)).eval s‖
      = ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖ * ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ := by
    rw [show 2 * M + 2 = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval, norm_mul]
  -- norm of the first term `t_{M+1}`.
  have ht : ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖
      = |(bernoulli (2 * M + 2) : ℝ)| / ((2 * M + 2)! : ℝ)
          * ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖
          * (N : ℝ) ^ (-(s.re + ((2 * M + 1 : ℕ) : ℝ))) := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * M + 2)! : ℝ)),
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0, hre1]
  -- value of the weight integral.
  have hWval : W = -(N : ℝ) ^ (-a + 1) / (-a + 1) := by
    rw [hW]; exact integral_Ioi_rpow_of_lt (by linarith : -a < -1) hN0
  -- bound on the centered-kernel integral.
  have hInorm : ‖∫ x in Set.Ioi (N : ℝ),
        ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
          * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
      ≤ |(bernoulli (2 * M + 2) : ℝ)| * W := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
      show ‖((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
            * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
          = |bernoulliFun (2 * M + 2) (Int.fract x) - (bernoulli (2 * M + 2) : ℝ)| * x ^ (-a) by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans hN0 hx), hwre]]
    have h3 := integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (M + 1) (by lia) ha hN
    rwa [show 2 * (M + 1) = 2 * M + 2 from by ring] at h3
  rw [zetaRemainder_eq_integral_bernoulliFun_fract_sub s M N hN hs, norm_mul, norm_neg, norm_div,
    Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left hInorm (by positivity)).trans (le_of_eq ?_)
  rw [hP, ht, hWval, hrel]
  have hFacne : ((2 * M + 2)! : ℝ) ≠ 0 := by positivity
  have hDne : s.re + ((2 * M + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (by push_cast; linarith : (0 : ℝ) < s.re + ((2 * M + 1 : ℕ) : ℝ))
  field_simp

end


namespace BMORZetaHeight

open Complex

/-- The first Euler–Maclaurin approximant dominates the indicated remainder. -/
theorem model_dominates (s : ℂ) (hlo : 0 ≤ s.re) (hhi : s.re ≤ 1)
    (ht : |s.im| ≤ 2) (hp : s ≠ 1) :
    ‖s+1‖ / (s.re + 1) * (‖s‖ / 12) < ‖(1:ℂ)/(s-1) + 1/2‖ := by
  have h0 : s-1 ≠ 0 := sub_ne_zero.mpr hp
  have hplus : s+1 ≠ 0 := by
    intro h
    have z := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at z
    linarith
  have hs : 0 < ‖s-1‖ := norm_pos_iff.mpr h0
  have hsp : 0 < ‖s+1‖ := norm_pos_iff.mpr hplus
  have hσ : 0 < s.re + 1 := by linarith
  have ht' := abs_le.mp ht
  have hti : s.im^2 ≤ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht'.2) (show 0 ≤ 2 + s.im by linarith)]
  have hsq : ‖s‖^2 ≤ 5 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith [mul_nonneg hlo (sub_nonneg.mpr hhi)]
  have hdsq : ‖s-1‖^2 ≤ 5 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    nlinarith [mul_nonneg hlo (sub_nonneg.mpr hhi)]
  have hprod : ‖s‖ * ‖s-1‖ < 6 * (s.re+1) := by
    nlinarith [sq_nonneg (‖s‖ - ‖s-1‖)]
  have heq : (1:ℂ)/(s-1) + 1/2 = (s+1)/(2*(s-1)) := by
    field_simp
    ring
  rw [heq,norm_div,norm_mul]
  norm_num
  field_simp
  nlinarith only [hprod]

end BMORZetaHeight

namespace BMORZetaHeight

open Complex

/-- A uniform approximation on Re(s) > -1. The displayed estimate specializes
the zero-order Olver–Borwein bound to cutoff 1. -/
theorem riemannZeta_model_error {s : ℂ} (hlo : -1 < s.re) (hp : s ≠ 1) :
    ‖riemannZeta s - ((1:ℂ)/(s-1) + 1/2)‖ ≤
      ‖s+1‖ / (s.re+1) * (‖s‖ / 12) := by
  have hr : -(2 * (0:ℕ) + 1 : ℝ) < s.re := by simpa using hlo
  have hsum := riemannZeta_eq_approximant_add_remainder s 0 1 (by decide) hr hp
  have hrem := norm_zetaRemainder_le s 0 1 (by decide) hr
  have hmodel : zetaApproximant s 0 1 = (1:ℂ)/(s-1) + 1/2 := by
    simp [zetaApproximant]
  rw [hsum,hmodel,add_sub_cancel_left]
  refine hrem.trans_eq ?_
  unfold zetaRemainderBound
  norm_num [bernoulli_two,ascPochhammer_one,Nat.factorial,norm_mul,norm_div]
  ring_nf
  simp

/-- There are no zeros of the actual Riemann zeta function in the closed
height-two strip, with its pole omitted. -/
theorem riemannZeta_ne_zero_height_two {s : ℂ} (hlo : 0 ≤ s.re) (hhi : s.re ≤ 1)
    (ht : |s.im| ≤ 2) (hp : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hu := riemannZeta_model_error (by linarith : -1 < s.re) hp
  rw [hz,zero_sub,norm_neg] at hu
  exact (not_lt_of_ge hu) (model_dominates s hlo hhi ht hp)

/-- The third-order numerical remainder in the low rectangle. -/
theorem riemannZeta_third_order_error {s : ℂ} (hlo : 0 ≤ s.re) (hhi : s.re ≤ 1)
    (ht : |s.im| ≤ 2) (hp : s ≠ 1) :
    ‖riemannZeta s - ((1:ℂ)/(s-1) + 1/2 + s/12)‖ ≤
      ‖s*(s+1)*(s+2)‖ / (96 * (s.re+2)) := by
  have hr : -(2 * (1:ℕ) + 1 : ℝ) < s.re := by push_cast; linarith
  have hsum := riemannZeta_eq_approximant_add_remainder s 1 1 (by decide) hr hp
  have hrem := norm_zetaRemainder_le s 1 1 (by decide) hr
  have hmodel : zetaApproximant s 1 1 = (1:ℂ)/(s-1) + 1/2 + s/12 := by
    simp [zetaApproximant,bernoulli_two,ascPochhammer_one,Nat.factorial]
    norm_num
    ring
  rw [hsum,hmodel,add_sub_cancel_left]
  refine hrem.trans ?_
  have hb4 : bernoulli 4 = -(1/30) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide),bernoulli'_four]; ring
  have hpoch : (ascPochhammer ℂ 3).eval s = s*(s+1)*(s+2) := by
    rw [ascPochhammer_succ_eval 2,ascPochhammer_succ_eval 1]
    simp [ascPochhammer_one]
  have hb : zetaRemainderBound s 1 1 = ‖s+3‖/(s.re+3) * (‖s*(s+1)*(s+2)‖/720) := by
    unfold zetaRemainderBound
    norm_num [hb4,hpoch,Nat.factorial,norm_mul,norm_div]
    ring_nf
    simp
  rw [hb]
  have hsq : ‖s+3‖ ≤ 5 := by
    have h1 := abs_le.mp ht
    have h2 : s.im^2 ≤ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h1.2) (show 0 ≤ 2+s.im by linarith)]
    have h3 := Complex.sq_norm_sub_sq_re (s+3)
    norm_num at h3
    nlinarith [mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ 7+s.re by linarith)]
  have h2 : 0 < s.re+2 := by linarith
  have h3 : 0 < s.re+3 := by linarith
  have hk : ‖s+3‖ * (96*(s.re+2)) ≤ 720*(s.re+3) := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (show 0 ≤ 96*(s.re+2) by linarith)]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hk (norm_nonneg (s*(s+1)*(s+2)))]

end BMORZetaHeight
end

section
namespace BMORProgression
open Complex Set DirichletCharacter

theorem principal_low_band_nonzero {q : ℕ} [NeZero q] {s : ℂ}
    (hlo : 0<s.re) (hhi : s.re≤1) (ht : |s.im|≤2) (hp : s≠1) :
    LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := fun e =>
  BMORZetaHeight.riemannZeta_ne_zero_height_two hlo.le hhi ht hp ((principal_zero_iff_zeta hlo hp).mp e)

theorem all_mod_three_low_zeros_empty (χ : DirichletCharacter ℂ 3) : BMORModThree.lowZeros χ 2 = ∅ := by
  by_cases hχ : χ=1
  · subst χ
    apply (BMORModThree.lowZeros_empty_iff _ 2).mpr
    intro s hlo hhi ht
    exact principal_low_band_nonzero hlo hhi.le ht (fun h => by simp [h] at hhi)
  · exact BMORModThree.HeightTwo.low_zeros_empty χ hχ

theorem all_mod_three_regular_nonzero (χ : DirichletCharacter ℂ 3) {s : ℂ}
    (hs : 0<s.re) (ht : |s.im|≤2) : poleRemoved χ s ≠ 0 := by
  classical
  by_cases hr : 1≤s.re
  · exact poleRemoved_ne_zero_right χ hr
  have hl := lt_of_not_ge hr
  have lnon := (BMORModThree.lowZeros_empty_iff χ 2).mp (all_mod_three_low_zeros_empty χ) s hs hl ht
  by_cases hχ : χ=1
  · subst χ
    have h1 : s≠1 := fun h => by simp [h] at hl
    simpa only [poleRemoved,ite_true,LFunctionTrivChar₁,Function.update_of_ne h1] using
      (mul_ne_zero (sub_ne_zero.mpr h1) lnon)
  · simpa [poleRemoved,hχ] using lnon

theorem mod_three_height_two_shift (a m n : ℕ) (hm : 0<m) (hn : 0<n) {σ : ℝ} (hs : 0<σ) (hb : σ≤2) :
    let f := regularContour 3 a m n
    contourVertical f 2 2 = contourVertical f σ 2 +
      I*(contourHorizontal f σ (-2)-contourHorizontal f σ 2) := by
  exact shift_regularContour hm hn hs hb (by norm_num)
    (fun s hx ht χ => all_mod_three_regular_nonzero χ (hs.trans_le hx.1) ht)

/-- Equal totients ensure every character of the larger modulus is induced from the smaller one. -/
theorem nonzero_all_of_totient_eq {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q)
    (hc : d.totient=q.totient) {s : ℂ} (hs : 0<s.re) (h1 : s≠1)
    (hz : ∀ χ : DirichletCharacter ℂ d, LFunction χ s ≠ 0) :
    ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0 := by
  classical
  have card (m : ℕ) [NeZero m] : Fintype.card (DirichletCharacter ℂ m) = m.totient := by
    rw [←Nat.card_eq_fintype_card,card_eq_totient_of_hasEnoughRootsOfUnity]
  let lift : DirichletCharacter ℂ d → DirichletCharacter ℂ q := changeLevel hd
  have surj := ((Fintype.bijective_iff_injective_and_card lift).mpr
    ⟨changeLevel_injective hd, by rw [card,card,hc]⟩).surjective
  intro χ
  obtain ⟨ψ,rfl⟩ := surj χ
  exact fun h => hz ψ ((LFunction_changeLevel_zero_iff hd ψ hs (.inr h1)).mp h)

theorem all_mod_six_nonzero (χ : DirichletCharacter ℂ 6) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) (ht : |s.im|≤2) : LFunction χ s ≠ 0 := by
  exact nonzero_all_of_totient_eq (by decide : 3∣6) (by decide) hs (fun e => by simp [e] at hs')
    (fun ψ => (BMORModThree.lowZeros_empty_iff ψ 2).mp (all_mod_three_low_zeros_empty ψ) s hs hs' ht) χ

end BMORProgression
end

section
namespace BMORModFour
open Complex DirichletCharacter Finset MeasureTheory Set BMORModThree.Mellin

theorem partial_eq (χ : DirichletCharacter ℂ 4) (hχ : χ≠1) (n : ℕ) :
    charPartialSum χ n = if n % 4=1 ∨ n % 4=2 then 1 else 0 := by
  classical
  letI : Nontrivial (ZMod 4) := ⟨⟨0,1,by decide⟩⟩
  have red (k : ℕ) : integerRemainder χ k=charPartialSum χ k := by
    simp [integerRemainder,charMean_eq,hχ]
  have per (k : ℕ) : charPartialSum χ (k % 4)=charPartialSum χ k := by
    simpa only [red] using (integerRemainder_periodic χ).map_mod_nat k
  have nonunit : ¬ IsUnit (2 : ZMod 4) := fun h =>
    (by decide : ¬ Nat.Coprime 2 4) ((ZMod.isUnit_iff_coprime 2 4).mp h)
  have zero_two : χ (2 : ZMod 4)=0 := χ.map_nonunit nonunit
  have three : charPartialSum χ 3=0 := by
    have h := per 4
    norm_num [charPartialSum,Finset.sum_range_succ] at h ⊢
    simpa [show (4 : ZMod 4)=0 by decide,χ.map_zero] using h.symm
  rw [←per n]
  have hn := Nat.mod_lt n (by decide : 0<4)
  generalize h : n % 4 = j at *
  interval_cases j <;> norm_num [charPartialSum,Finset.sum_range_succ,zero_two] at * <;> assumption

noncomputable def masked (s : ℂ) (x : ℝ) : ℂ :=
  if ⌊x⌋₊%4 = 1 ∨ ⌊x⌋₊%4 = 2 then (x:ℂ)^(-s-1) else 0

theorem masked_formula (χ : DirichletCharacter ℂ 4) (hχ : χ≠1) (s : ℂ) (x : ℝ) :
    (x:ℂ)^(-s-1)*(charPartialSum χ ⌊x⌋₊ - (x:ℂ)*charMean χ)=masked s x := by
  classical
  rw [charMean_eq,ite_eq_right hχ,mul_zero,sub_zero,partial_eq χ hχ]
  unfold masked
  split <;> simp

theorem masked_integrable {s : ℂ} (hs : 0<s.re) : IntegrableOn (masked s) (Ioi 1) := by
  classical
  have hmeas : Measurable (fun x : ℝ => ⌊x⌋₊%4) :=
    (measurable_of_countable (fun n : ℕ => n % 4)).comp measurable_id.nat_floor
  have E i : MeasurableSet {x : ℝ | ⌊x⌋₊%4=i} := hmeas (measurableSet_singleton i)
  have hm : MeasurableSet {x : ℝ | ⌊x⌋₊%4=1 ∨ ⌊x⌋₊%4=2} := (E 1).union (E 2)
  have hp : (-s-1).re < -1 := by simp only [sub_re,neg_re,one_re]; linarith
  have hi := integrableOn_Ioi_cpow_of_lt hp zero_lt_one
  apply (hi.indicator hm).congr_fun _ measurableSet_Ioi
  intro x _
  by_cases h : ⌊x⌋₊%4=1 ∨ ⌊x⌋₊%4=2 <;> simp [masked,h]

theorem remainder_eq_masked (χ : DirichletCharacter ℂ 4) (hχ : χ≠1) (s : ℂ) :
    remainderMellin χ s = ∫ x : ℝ in Ioi 1, masked s x := by
  rw [remainderMellin_eq_integral]
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ => masked_formula χ hχ s x

theorem remainder_eq_head_add_tail (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0<s.re) :
    remainderMellin χ s = (∫ x : ℝ in Ioo 1 3, (x:ℂ)^(-s-1)) +
      ∫ x : ℝ in Ioi 5, masked s x := by
  have integ := masked_integrable hs
  have cut (a b : ℝ) (ha : 1≤a) (hb : a≤b) :
      (∫ x : ℝ in Ioi a, masked s x) = (∫ x : ℝ in Ioo a b, masked s x) +
        ∫ x : ℝ in Ioi b, masked s x := by
    simpa only [intervalIntegral.integral_of_le hb,integral_Ioc_eq_integral_Ioo] using
      (intervalIntegral.integral_interval_add_Ioi (integ.mono_set (Ioi_subset_Ioi ha))
        (integ.mono_set (Ioi_subset_Ioi (ha.trans hb)))).symm
  have head : (∫ x : ℝ in Ioo 1 3, masked s x) = ∫ x : ℝ in Ioo 1 3, (x:ℂ)^(-s-1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have lo : 1≤⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.1.le)
    have hi : ⌊x⌋₊<3 := (Nat.floor_lt (by linarith [hx.1] : 0≤x)).mpr (by exact_mod_cast hx.2)
    simp [masked,show ⌊x⌋₊%4=1 ∨ ⌊x⌋₊%4=2 by omega]
  have gap : (∫ x : ℝ in Ioo 3 5, masked s x) = 0 := by
    calc
      _ = ∫ _x : ℝ in Ioo 3 5, (0:ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        have lo : 3≤⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.1.le)
        have hi : ⌊x⌋₊<5 := (Nat.floor_lt (by linarith [hx.1] : 0≤x)).mpr (by exact_mod_cast hx.2)
        simp [masked,show ¬(⌊x⌋₊%4=1 ∨ ⌊x⌋₊%4=2) by omega]
      _ = _ := by simp
  rw [remainder_eq_masked χ hχ,cut 1 3 (by norm_num) (by norm_num),cut 3 5 (by norm_num) (by norm_num),
    head,gap,zero_add]

theorem LFunction_eq_head_add_tail (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0<s.re) :
    LFunction χ s = s*((∫ x : ℝ in Ioo 1 3, (x:ℂ)^(-s-1)) + ∫ x : ℝ in Ioi 5, masked s x) := by
  rw [LFunction_eq_remainderMellin χ hχ hs,remainder_eq_head_add_tail χ hχ hs]

end BMORModFour
end

section
noncomputable section
open MeasureTheory Set
open scoped Interval

namespace BMORModFour.Tail

/-- The modulus-four mask applied to the integrable comparison density. -/
def weight (x : ℝ) : ℝ := if ⌊x⌋₊ % 4 = 1 ∨ ⌊x⌋₊ % 4 = 2 then x ^ (-(3/2) : ℝ) else 0

theorem weight_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn weight (Ioi a) := by
  have hm : Measurable (fun x : ℝ => ⌊x⌋₊ % 4) :=
    (measurable_of_countable (fun n : ℕ => n % 4)).comp measurable_id.nat_floor
  have hs : MeasurableSet {x : ℝ | ⌊x⌋₊ % 4 = 1 ∨ ⌊x⌋₊ % 4 = 2} := (hm (measurableSet_singleton 1)).union (hm (measurableSet_singleton 2))
  have hw : weight = {x : ℝ | ⌊x⌋₊ % 4 = 1 ∨ ⌊x⌋₊ % 4 = 2}.indicator (fun x : ℝ => x ^ (-(3/2) : ℝ)) := by
    funext x
    by_cases h : ⌊x⌋₊ % 4 = 1 ∨ ⌊x⌋₊ % 4 = 2 <;> simp [weight, Set.indicator, h]
  rw [hw]
  exact
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2) : ℝ) < -1) ha).indicator hs

theorem weight_two {x : ℝ} (hx : 0 < x) :
    weight x + weight (x+2) ≤ x ^ (-(3/2) : ℝ) := by
  have hf : ⌊x+(2:ℝ)⌋₊ = ⌊x⌋₊+2 := by
    exact_mod_cast Nat.floor_add_natCast hx.le 2
  have h2 := Real.rpow_le_rpow_of_nonpos hx (show x ≤ x+2 by linarith)
    (by norm_num : (-(3/2) : ℝ) ≤ 0)
  simp only [weight, hf]
  split_ifs <;> first | omega | linarith

private theorem shifted :
    IntegrableOn (fun x => weight (x+2)) (Ioi (7:ℝ)) ∧
    ∫ x in Ioi (7:ℝ), weight (x+2) = ∫ x in Ioi (7:ℝ), weight x := by
  have hi := weight_integrable (by norm_num : (0:ℝ) < 9)
  have ht : (fun x : ℝ => x+2) ⁻¹' Ioi 9 = Ioi (7:ℝ) := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have hp := measurePreserving_add_right (volume : Measure ℝ) (2:ℝ)
  have he := measurableEmbedding_addRight (2:ℝ)
  constructor
  · simpa only [ht, Function.comp_def] using (hp.integrableOn_comp_preimage he).mpr hi
  · have hc := hp.setIntegral_preimage_emb he weight (Ioi 9)
    rw [ht] at hc
    rw [hc]
    have hzero : ∫ x in (7:ℝ)..9, weight x = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have hl : 7 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith [hx.1] : (7:ℝ) ≤ x)
      have hu : ⌊x⌋₊ < 9 := (Nat.floor_lt (by linarith [hx.1] : 0 ≤ x)).mpr hx.2
      simp [weight, show ⌊x⌋₊ % 4 ≠ 1 by omega, show ⌊x⌋₊ % 4 ≠ 2 by omega]
    simpa only [hzero, zero_add] using intervalIntegral.integral_interval_add_Ioi
      (weight_integrable (by norm_num : (0:ℝ) < 7)) hi

theorem weight_tail_seven :
    2 * (∫ x in Ioi (7:ℝ), weight x) ≤ ∫ x in Ioi (7:ℝ), x ^ (-(3/2) : ℝ) := by
  obtain ⟨h2,e2⟩ := shifted
  have hi := weight_integrable (by norm_num : (0:ℝ) < 7)
  have bound := integral_mono_ae (hi.add h2)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2) : ℝ) < -1)
      (by norm_num : (0:ℝ)<7)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact weight_two (lt_trans (by norm_num : (0:ℝ)<7) hx))
  simp only [Pi.add_apply] at bound
  rw [integral_add hi h2,e2] at bound
  linarith

private theorem density_tail {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi b, x ^ (-(3/2) : ℝ)) = 2 / Real.sqrt b := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3/2) : ℝ) < -1) hb]
  rw [show (-(3/2)+1 : ℝ) = -(1/2) by ring, Real.rpow_neg hb.le, ←Real.sqrt_eq_rpow]
  ring

theorem weight_tail_five :
    (∫ x in Ioi (5:ℝ), weight x) ≤ 2 / Real.sqrt 5 - 1 / Real.sqrt 7 := by
  let f : ℝ → ℝ := fun x => x ^ (-(3/2) : ℝ)
  have hi {b : ℝ} (hb : 0<b) : IntegrableOn f (Ioi b) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hb
  have eh := intervalIntegral.integral_interval_add_Ioi
    (weight_integrable (by norm_num : (0:ℝ)<5)) (weight_integrable (by norm_num : (0:ℝ)<7))
  have ed := intervalIntegral.integral_interval_add_Ioi (hi (by norm_num : (0:ℝ)<5))
    (hi (by norm_num : (0:ℝ)<7))
  have head : ∫ x in (5:ℝ)..7, weight x ≤ ∫ x in (5:ℝ)..7, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (5:ℝ) ≤ 7),
      intervalIntegral.integral_of_le (by norm_num : (5:ℝ) ≤ 7)]
    apply setIntegral_mono_on ((weight_integrable (by norm_num : (0:ℝ)<5)).mono_set Ioc_subset_Ioi_self)
      ((hi (by norm_num : (0:ℝ)<5)).mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
    intro x hx
    dsimp [weight, f]
    split <;> first | rfl | exact Real.rpow_nonneg (by linarith [hx.1]) _
  have tail := weight_tail_seven
  have ef5 : (∫ x in Ioi (5:ℝ), f x)=2 / Real.sqrt 5 := density_tail (by norm_num)
  have ef7 : (∫ x in Ioi (7:ℝ), f x)=2 / Real.sqrt 7 := density_tail (by norm_num)
  change 2 * (∫ x in Ioi (7:ℝ), weight x) ≤ ∫ x in Ioi (7:ℝ), f x at tail
  rw [ef5,ef7] at ed
  rw [ef7] at tail
  have hscale : (2:ℝ) / Real.sqrt 7 = 2*(1/Real.sqrt 7) := by ring
  rw [hscale] at ed tail
  linarith

theorem norm_tail_le (s : ℂ) (h : 1/2 ≤ s.re) :
    ‖∫ x in Ioi (5:ℝ), masked s x‖ ≤
      (3:ℝ)^(1/2-s.re) * (2 / Real.sqrt 5 - 1 / Real.sqrt 7) := by
  let A : ℝ := (3:ℝ)^(1/2-s.re)
  have hA : 0 ≤ A := Real.rpow_nonneg (by norm_num) _
  have hi := (weight_integrable (by norm_num : (0:ℝ)<5)).const_mul A
  calc
    _ ≤ ∫ x in Ioi (5:ℝ), A * weight x := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans (by norm_num : (0:ℝ)<5) hx
      have hx2 : 3 ≤ x := le_trans (by norm_num : (3:ℝ)≤5) hx.le
      simp only [masked, weight]
      split
      · rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.neg_re, Complex.one_re,
            show -s.re-1 = 1/2-s.re + -(3/2) by ring, Real.rpow_add hx0]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (by norm_num) hx2 (by linarith))
          (Real.rpow_nonneg hx0.le _)
      · simp
    _ = A * (∫ x in Ioi (5:ℝ), weight x) := integral_const_mul A weight
    _ ≤ _ := mul_le_mul_of_nonneg_left weight_tail_five hA

theorem tail_coefficient_lt : 2 / Real.sqrt 5 - 1 / Real.sqrt 7 < 517/1000 := by
  have hs5 : (2236/1000:ℝ) ≤ Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg (5:ℝ)]
  have hs7 : Real.sqrt 7 ≤ (26458/10000:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)]
  have ha : 2 / Real.sqrt 5 ≤ 8945/10000 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  have hb : (3779/10000:ℝ) ≤ 1 / Real.sqrt 7 := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  linarith

end BMORModFour.Tail
end
end

section
namespace BMORModFour
open MeasureTheory Set
open scoped Interval

private theorem interval_mass {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Ioc a b, x^(-3/2:ℝ)) = 2/Real.sqrt a - 2/Real.sqrt b := by
  let f := fun x : ℝ => x^(-3/2:ℝ)
  have hi {c : ℝ} (hc : 0<c) : IntegrableOn f (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  have tail {c : ℝ} (hc : 0<c) : (∫ x in Ioi c, f x)=2/Real.sqrt c := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ)< -1) hc,
      show (-3/2+1:ℝ)= -(1/2) by ring,Real.rpow_neg hc.le,←Real.sqrt_eq_rpow]
    ring
  have eq := intervalIntegral.integral_interval_add_Ioi (hi ha) (hi (ha.trans_le hab))
  rw [tail ha,tail (ha.trans_le hab),intervalIntegral.integral_of_le hab] at eq
  change (∫ x in Ioc a b, f x) = _
  linarith

theorem full_mass_gt : (84/100:ℝ)<∫ x in Ioc (1:ℝ) 3, x^(-3/2:ℝ) := by
  rw [interval_mass (by norm_num) (by norm_num),Real.sqrt_one,div_one]
  have hs : (173/100:ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have h : (2:ℝ)/Real.sqrt 3 < 116/100 := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  linarith

theorem inner_mass_gt : (49/100:ℝ)<∫ x in Ioc (5/4:ℝ) (12/5), x^(-3/2:ℝ) := by
  rw [interval_mass (by norm_num) (by norm_num)]
  have hs1 : Real.sqrt (5/4) ≤ (11181/10000:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5/4)]
  have hs2 : (15491/10000:ℝ) ≤ Real.sqrt (12/5) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤12/5),Real.sqrt_nonneg (12/5)]
  have h1 : (1788/1000:ℝ) < 2/Real.sqrt (5/4) := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  have h2 : (2:ℝ)/Real.sqrt (12/5) < 1292/1000 := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  linarith

end BMORModFour
end

section
namespace BMORModFour
open Set Complex MeasureTheory
open scoped Interval

private theorem rotated_head_point (s : ℂ) {x : ℝ} (hx : 0<x) :
    (Complex.exp ((s.im*Real.log (Real.sqrt 3):ℝ)*I) * (x:ℂ)^(-s-1)).re =
      x^(-s.re-1) * Real.cos (s.im*(Real.log (Real.sqrt 3)-Real.log x)) := by
  have nz : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero nz,←Complex.exp_add,Complex.exp_re,
    ←Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_I_re,Complex.mul_I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.sub_re,
    Complex.sub_im,Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,
    Complex.I_re,Complex.I_im,neg_zero,zero_mul,mul_zero,mul_one,zero_add,sub_zero,add_zero]
  congr 2 <;> ring

private theorem cosine_from_log_width {t x a b d : ℝ} (ht : |t|≤2) (ha : 0<a)
    (hx : x ∈ Icc a b) (hc : Real.log a+Real.log b=Real.log 3)
    (hw : Real.log b-Real.log a≤d) :
    1-d^2/2 ≤ Real.cos (t*(Real.log (Real.sqrt 3)-Real.log x)) := by
  have lx := Real.log_le_log ha hx.1
  have ly := Real.log_le_log (ha.trans_le hx.1) hx.2
  have wd : |Real.log (Real.sqrt 3)-Real.log x| ≤ (Real.log b-Real.log a)/2 := by
    rw [Real.log_sqrt (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  let u := t*(Real.log (Real.sqrt 3)-Real.log x)
  have hu : |u|≤d := by
    rw [show |u| = |t| * |Real.log (Real.sqrt 3)-Real.log x| from abs_mul _ _]
    linarith [mul_le_mul ht wd (abs_nonneg _) (by norm_num : (0:ℝ)≤2)]
  have sq := mul_self_le_mul_self (abs_nonneg u) hu
  rw [abs_mul_abs_self] at sq
  have hc' : 1-u^2/2 ≤ Real.cos u := Real.one_sub_sq_div_two_le_cos
  change 1-d^2/2 ≤ Real.cos u
  nlinarith

private theorem full_cos {t x : ℝ} (ht : |t|≤2) (hx : x ∈ Icc (1:ℝ) 3) :
    79/200 ≤ Real.cos (t*(Real.log (Real.sqrt 3)-Real.log x)) := by
  have h := cosine_from_log_width (d:=11/10) ht zero_lt_one hx (by simp)
    (by linarith [Real.log_one,Real.log_three_lt_d9])
  norm_num at h ⊢
  exact h

private theorem inner_cos {t x : ℝ} (ht : |t|≤2) (hx : x ∈ Icc (5/4:ℝ) (12/5)) :
    3911/5000 ≤ Real.cos (t*(Real.log (Real.sqrt 3)-Real.log x)) := by
  have hc : Real.log (5/4)+Real.log (12/5)=Real.log 3 := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hw : Real.log (12/5)-Real.log (5/4) ≤ 33/50 := by
    rw [←Real.log_div (by norm_num) (by norm_num),
      show (12/5:ℝ)/(5/4) = 2*(24/25) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<24/25)]
  have h := cosine_from_log_width ht (by norm_num : (0:ℝ)<5/4) hx hc hw
  norm_num at h ⊢
  exact h

theorem head_rotated_lower_from_mass
    (mFull : (84/100:ℝ)<∫ x in Ioc (1:ℝ) 3, x^(-3/2:ℝ))
    (mInner : (49/100:ℝ)<∫ x in Ioc (5/4:ℝ) (12/5), x^(-3/2:ℝ))
    {s : ℂ} (hσ : 1/2 ≤ s.re) (ht : |s.im|≤2) :
    (3:ℝ)^(1/2-s.re)*(521/1000) <
      (Complex.exp ((s.im*Real.log (Real.sqrt 3):ℝ)*I) *
        (∫ x in Ioc (1:ℝ) 3, (x:ℂ)^(-s-1))).re := by
  let A := (3:ℝ)^(1/2-s.re)
  let rot := Complex.exp ((s.im*Real.log (Real.sqrt 3):ℝ)*I)
  let G := Ioc (1:ℝ) 3
  let D := Ioc (5/4:ℝ) (12/5)
  let w := fun x : ℝ => x^(-3/2:ℝ)
  let v := fun x : ℝ => (rot*(x:ℂ)^(-s-1)).re
  have hA : 0<A := Real.rpow_pos_of_pos (by norm_num) _
  have sub : D ⊆ G := Ioc_subset_Ioc (by norm_num) (by norm_num)
  have hr : (0:ℝ) ∉ [[(1:ℝ),3]] := by norm_num [uIcc_of_le]
  have hc : IntegrableOn (fun x : ℝ => (x:ℂ)^(-s-1)) G :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ)≤3)).mp
      (intervalIntegral.intervalIntegrable_cpow (Or.inr hr))
  have hw : IntegrableOn w G :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ)≤3)).mp
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hr))
  have hi := hc.const_mul rot
  have hv : IntegrableOn v G := hi.re
  have hbase := hw.const_mul (A*(79/200))
  have hrem := hv.sub hbase
  have point {x c : ℝ} (hx : x ∈ G) (hc₀ : 0≤c)
      (hcos : c≤Real.cos (s.im*(Real.log (Real.sqrt 3)-Real.log x))) :
      (A*c)*w x ≤ v x := by
    have hp := zero_lt_one.trans hx.1
    rw [show v x = _ from rotated_head_point s hp]
    have pw : A ≤ x^(1/2-s.re) := Real.rpow_le_rpow_of_nonpos hp hx.2 (by linarith)
    have hw' : A*w x ≤ x^(-s.re-1) := by
      rw [show -s.re-1=(1/2-s.re)+(-3/2) by ring,Real.rpow_add hp]
      exact mul_le_mul_of_nonneg_right pw (Real.rpow_nonneg hp.le _)
    calc
      _ = (A*w x)*c := by ring
      _ ≤ _ := mul_le_mul hw' hcos hc₀ (Real.rpow_nonneg hp.le _)
  have base {x} (hx : x∈G) := point hx (by norm_num : (0:ℝ)≤79/200)
    (full_cos ht ⟨hx.1.le,hx.2⟩)
  have inside {x} (hx : x∈D) := point (sub hx) (by norm_num : (0:ℝ)≤3911/5000)
    (inner_cos ht ⟨hx.1.le,hx.2⟩)
  have nonnegative : 0 ≤ᵐ[volume.restrict G] (fun x => v x-(A*(79/200))*w x) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet G from measurableSet_Ioc)] with x hx
    exact sub_nonneg.mpr (base hx)
  have transfer := setIntegral_mono_set hrem nonnegative sub.eventuallySubset
  let gain : ℝ := 3911/5000-79/200
  have hd := setIntegral_mono_on ((hw.mono_set sub).const_mul (A*gain))
    (hrem.mono_set sub) (show MeasurableSet D from measurableSet_Ioc) (fun x hx => by
      change (A*gain)*w x ≤ v x-(A*(79/200))*w x
      dsimp [gain]
      linarith only [inside hx])
  have join := hd.trans transfer
  change (∫ x in D, (A*gain)*w x) ≤ ∫ x in G, v x-(A*(79/200))*w x at join
  rw [integral_const_mul, integral_sub hv hbase,integral_const_mul] at join
  change (84/100:ℝ)<∫ x in G,w x at mFull
  change (49/100:ℝ)<∫ x in D,w x at mInner
  have gf : 0<A*(79/200) := by positivity
  have gg : 0<A*gain := mul_pos hA (by norm_num [gain])
  have hF := mul_lt_mul_of_pos_left mFull gf
  have hD := mul_lt_mul_of_pos_left mInner gg
  change A*(521/1000) < (rot * (∫ x in G, (x:ℂ)^(-s-1))).re
  have req : (∫ x in G, v x) = (∫ x in G, rot*(x:ℂ)^(-s-1)).re := integral_re hi
  rw [←integral_const_mul,←req]
  change A*(521/1000) < ∫ x in G, v x
  dsimp [gain] at hD join
  linarith only [join,hD,hF,hA]

theorem head_rotated_lower {s : ℂ} (hσ : 1/2 ≤ s.re) (ht : |s.im|≤2) :
    (3:ℝ)^(1/2-s.re)*(521/1000) <
      (Complex.exp ((s.im*Real.log (Real.sqrt 3):ℝ)*I) *
        (∫ x in Ioc (1:ℝ) 3, (x:ℂ)^(-s-1))).re :=
  head_rotated_lower_from_mass full_mass_gt inner_mass_gt hσ ht

end BMORModFour
end

section
namespace BMORModFour
open Complex DirichletCharacter MeasureTheory Set

theorem primitive_of_nonprincipal {χ : DirichletCharacter ℂ 4} (hχ : χ≠1) : χ.IsPrimitive := by
  have d := χ.conductor_dvd_level
  have h2 : χ.conductor ≠ 2 := by
    intro e
    have h := χ.factorsThrough_conductor
    rw [e] at h
    obtain ⟨hd, ψ, eψ⟩ := h
    have hc : Nat.card (DirichletCharacter ℂ 2) = 1 :=
      (card_eq_totient_of_hasEnoughRootsOfUnity ℂ 2).trans (by decide)
    let _ := (Nat.card_eq_one_iff_unique.mp hc).1
    exact hχ (by rw [eψ,Subsingleton.elim ψ 1,changeLevel_one])
  have h1 : χ.conductor ≠ 1 := fun e => hχ (eq_one_iff_conductor_eq_one.mpr e)
  have hmem := Nat.mem_divisors.mpr ⟨d,by decide⟩
  rw [show (4:ℕ).divisors = {1,2,4} by decide] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  exact (hmem.resolve_left h1).resolve_left h2

theorem norm_L_lower_of_head (χ : DirichletCharacter ℂ 4) (hχ : χ≠1)
    {s : ℂ} (hσ : 1/2 ≤ s.re) (hσ' : s.re ≤ 1)
    (head : (3:ℝ)^(1/2-s.re)*(521/1000) <
      (Complex.exp ((s.im*Real.log (Real.sqrt 3):ℝ)*I) *
        (∫ x in Ioc (1:ℝ) 3, (x:ℂ)^(-s-1))).re) :
    1/1600 < ‖LFunction χ s‖ := by
  let A : ℝ := (3:ℝ)^(1/2-s.re)
  let H : ℂ := ∫ x in Ioo (1:ℝ) 3, (x:ℂ)^(-s-1)
  let T : ℂ := ∫ x in Ioi (5:ℝ), masked s x
  let R : ℂ := Complex.exp ((s.im*Real.log (Real.sqrt 3):ℝ)*I)
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hR : ‖R‖ = 1 := by simp [R,Complex.norm_exp,Complex.mul_re]
  rw [integral_Ioc_eq_integral_Ioo] at head
  change A*(521/1000) < (R*H).re at head
  have major : A*(521/1000) < ‖H‖ := by
    have bound := (le_abs_self _).trans (Complex.abs_re_le_norm (R*H))
    rw [norm_mul,hR,one_mul] at bound
    exact head.trans_le bound
  have tail : ‖T‖ ≤ A*(517/1000) :=
    (Tail.norm_tail_le s hσ).trans (mul_le_mul_of_nonneg_left Tail.tail_coefficient_lt.le hA.le)
  have triangle : ‖H‖ ≤ ‖H+T‖ + ‖T‖ := by simpa using norm_sub_le (H+T) T
  have rem : A*(4/1000) < ‖H+T‖ := by linarith
  have hs : 1/2 ≤ ‖s‖ := hσ.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have ha : 1/3 ≤ A := by
    calc
      (1/3:ℝ) = (3:ℝ)^(-1:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have lower : (1/2:ℝ)*((1/3:ℝ)*(4/1000)) ≤ ‖s‖*(A*(4/1000)) :=
    mul_le_mul hs (mul_le_mul_of_nonneg_right ha (by norm_num)) (by norm_num) (norm_nonneg _)
  rw [LFunction_eq_head_add_tail χ hχ (by linarith),norm_mul]
  exact (lt_of_lt_of_le (by norm_num : (1/1600:ℝ)<(1/2)*((1/3)*(4/1000))) lower).trans
    (mul_lt_mul_of_pos_left rem (by linarith))

def lowZeros (χ : DirichletCharacter ℂ 4) (T : ℝ) : Set ℂ :=
  {s | 0<s.re ∧ s.re<1 ∧ |s.im|≤T ∧ LFunction χ s = 0}

theorem lowZeros_empty_of_half_band {T : ℝ}
    (H : ∀ (χ : DirichletCharacter ℂ 4), χ≠1 → ∀ s : ℂ,
      1/2≤s.re → s.re<1 → |s.im|≤T → LFunction χ s ≠ 0)
    (χ : DirichletCharacter ℂ 4) (hχ : χ≠1) : lowZeros χ T=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro s ⟨hs,hu,ht,hz⟩
  by_cases h : 1/2≤s.re
  · exact H χ hχ s h hu ht hz
  · apply BMORModThree.reflect_nonvanishing χ (primitive_of_nonprincipal hχ) hs hu _ hz
    apply H χ⁻¹ (fun e => hχ (inv_eq_one.mp e))
    · simp only [sub_re,one_re]; linarith
    · simp only [sub_re,one_re]; linarith
    · simpa only [sub_im,one_im,zero_sub,abs_neg] using ht

end BMORModFour
end

section
namespace BMORModFour.HeightTwo
open Complex DirichletCharacter Set

theorem norm_L_lower (χ : DirichletCharacter ℂ 4) (hχ : χ≠1)
    {s : ℂ} (hσ : 1/2≤s.re) (hu : s.re≤1) (ht : |s.im|≤2) :
    1/1600 < ‖LFunction χ s‖ :=
  norm_L_lower_of_head χ hχ hσ hu (head_rotated_lower hσ ht)

theorem low_zeros_empty (χ : DirichletCharacter ℂ 4) (hχ : χ≠1) : lowZeros χ 2=∅ := by
  apply lowZeros_empty_of_half_band _ χ hχ
  intro ψ hψ s hs hu ht
  exact norm_pos_iff.mp (lt_trans (by norm_num) (norm_L_lower ψ hψ hs hu.le ht))

theorem low_zero_count (χ : DirichletCharacter ℂ 4) (hχ : χ≠1) :
    Nat.card (lowZeros χ 2)=0 := by
  rw [low_zeros_empty χ hχ]
  simp

theorem low_zero_weighted_sum (χ : DirichletCharacter ℂ 4) (hχ : χ≠1)
    (multiplicity : ℂ → ℕ) :
    (∑ᶠ z : lowZeros χ 2, (multiplicity z : ℝ) /
      Real.sqrt ((z : ℂ).im ^ 2 + 1/4)) = 0 := by
  have : IsEmpty (lowZeros χ 2) :=
    ⟨fun z => (Set.eq_empty_iff_forall_notMem.mp (low_zeros_empty χ hχ)) z.val z.property⟩
  exact finsum_of_isEmpty _

end BMORModFour.HeightTwo
end

section
namespace BMORProgression
open Complex Set DirichletCharacter

theorem all_mod_four_low_zeros_empty (χ : DirichletCharacter ℂ 4) : BMORModFour.lowZeros χ 2 = ∅ := by
  by_cases hχ : χ=1
  · subst χ
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨hs,hu,ht,hz⟩
    exact principal_low_band_nonzero hs hu.le ht (fun e => by simp [e] at hu) hz
  · exact BMORModFour.HeightTwo.low_zeros_empty χ hχ

/-- The full character family is zero-free through height two for each listed modulus. -/
theorem height_two_small_moduli {q : ℕ} [NeZero q] (hq : q=3 ∨ q=4 ∨ q=6)
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0<s.re) (hu : s.re<1) (ht : |s.im|≤2) :
    LFunction χ s ≠ 0 := by
  rcases hq with rfl | rfl | rfl
  · exact (BMORModThree.lowZeros_empty_iff χ 2).mp (all_mod_three_low_zeros_empty χ) s hs hu ht
  · intro hz
    have h : s∈BMORModFour.lowZeros χ 2 := ⟨hs,hu,ht,hz⟩
    rw [all_mod_four_low_zeros_empty χ] at h
    exact h
  · exact all_mod_six_nonzero χ hs hu ht

end BMORProgression
end

section
namespace BMORLowMassCounts
open Finset Complex DirichletCharacter

/-- The contribution of a finite list of zeros, with multiplicities, is bounded
from the counts on either side of height one. The inequality includes the endpoints. -/
theorem weighted_bound (Z : Finset ℂ) (multiplicity : ℂ → ℕ) :
    (∑ z ∈ Z, (multiplicity z : ℝ)/Real.sqrt (z.im^2+1/4)) ≤
      (2-2/Real.sqrt 5)*(∑ z ∈ Z.filter (fun z => |z.im|≤1), (multiplicity z:ℝ)) +
        (2/Real.sqrt 5)*(∑ z ∈ Z, (multiplicity z:ℝ)) := by
  classical
  have pos5 : 0<Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have point (z : ℂ) : (multiplicity z:ℝ)/Real.sqrt (z.im^2+1/4) ≤
      (if |z.im|≤1 then (2-2/Real.sqrt 5)*(multiplicity z:ℝ) else 0)+
        (2/Real.sqrt 5)*(multiplicity z:ℝ) := by
    have hr : 0≤z.im^2+1/4 := by positivity
    have hpos : 0<Real.sqrt (z.im^2+1/4) := Real.sqrt_pos.mpr (by positivity)
    have sq := Real.sq_sqrt hr
    have lower : (1/2:ℝ)≤Real.sqrt (z.im^2+1/4) := by nlinarith [sq_nonneg z.im]
    have m0 : (0:ℝ)≤multiplicity z := by positivity
    by_cases hin : |z.im|≤1
    · rw [ite_eq_left hin,show ∀ b m : ℝ, (2-b)*m+b*m=2*m by intros; ring]
      calc
        _ ≤ (multiplicity z:ℝ)/(1/2) := div_le_div_of_nonneg_left m0 (by norm_num) lower
        _ = _ := by ring
    · rw [ite_eq_right hin,zero_add]
      have hz : (1:ℝ)≤z.im^2 := by
        have e := mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) (le_of_lt (lt_of_not_ge hin))
        rw [abs_mul_abs_self] at e
        nlinarith
      have low : Real.sqrt 5 / 2 ≤ Real.sqrt (z.im^2+1/4) := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
      calc
        _ ≤ (multiplicity z:ℝ)/(Real.sqrt 5/2) := div_le_div_of_nonneg_left m0 (by positivity) low
        _ = _ := by ring
  calc
    _ ≤ ∑ z ∈ Z, ((if |z.im|≤1 then (2-2/Real.sqrt 5)*(multiplicity z:ℝ) else 0)+
      (2/Real.sqrt 5)*(multiplicity z:ℝ)) := sum_le_sum (fun z _ => point z)
    _ = _ := by rw [sum_add_distrib,←sum_filter,←mul_sum,←mul_sum]

theorem LFunction_weighted_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : Finset ℂ) (N₁ N₂ : ℝ)
    (h₁ : (∑ z ∈ Z.filter (fun z => |z.im|≤1), (analyticOrderNatAt (LFunction χ) z : ℝ)) ≤ N₁)
    (h₂ : (∑ z ∈ Z, (analyticOrderNatAt (LFunction χ) z : ℝ)) ≤ N₂) :
    (∑ z ∈ Z, (analyticOrderNatAt (LFunction χ) z:ℝ)/Real.sqrt (z.im^2+1/4)) ≤
      (2-2/Real.sqrt 5)*N₁ + (2/Real.sqrt 5)*N₂ := by
  apply (weighted_bound Z (analyticOrderNatAt (LFunction χ))).trans
  have hp : (0:ℝ)<Real.sqrt 5 := by positivity
  have hl : (1:ℝ)≤Real.sqrt 5 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
  have h : 0≤2-2/Real.sqrt 5 := sub_nonneg.mpr ((div_le_iff₀ hp).mpr (by linarith))
  exact add_le_add (mul_le_mul_of_nonneg_left h₁ h) (mul_le_mul_of_nonneg_left h₂ (by positivity))

noncomputable def heightWeight (y : ℝ) : ℝ := 1/Real.sqrt (y^2+1/4)

private theorem heightWeight_antitone {u v : ℝ} (hu : 0≤u) (hv : u≤v) : heightWeight v ≤ heightWeight u := by
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
  exact Real.sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ hu hv 2) (le_refl _))

private theorem weight_majorant (t : ℕ → ℝ) (h0 : t 0 = 0) (hm : Monotone t) {y : ℝ} (hy : 0≤y) (r : ℕ) :
    heightWeight y ≤ heightWeight (t r) +
      ∑ j ∈ range r, (if y≤t (j+1) then heightWeight (t j)-heightWeight (t (j+1)) else 0) := by
  have tp (i : ℕ) : 0≤t i := h0 ▸ hm (Nat.zero_le i)
  induction r with
  | zero => simpa [h0] using (heightWeight_antitone (le_refl 0) hy)
  | succ r ih =>
    rw [sum_range_succ]
    by_cases hin : y≤t (r+1)
    · rw [ite_eq_left hin]
      linarith
    · have vanish : ∀ j ∈ range r, ¬ y ≤ t (j+1) := fun j hj h =>
        hin (h.trans (hm (by have := mem_range.mp hj; omega)))
      have hsum : (∑ j ∈ range r, (if y≤t (j+1) then heightWeight (t j)-heightWeight (t (j+1)) else 0)) = 0 :=
        sum_eq_zero fun j hj => ite_eq_right (vanish j hj)
      rw [ite_eq_right hin,hsum,zero_add,add_zero]
      exact heightWeight_antitone (tp _) (le_of_lt (lt_of_not_ge hin))

/-- Upper counts at nested heights bound the weighted contribution, without enumerating the heights of individual zeros. -/
theorem weighted_bound_at_cuts (Z : Finset ℂ) (multiplicity : ℂ → ℕ) (t : ℕ → ℝ)
    (h0 : t 0 = 0) (hm : Monotone t) (r : ℕ) :
    (∑ z ∈ Z, (multiplicity z:ℝ)*heightWeight |z.im|) ≤
      heightWeight (t r)*(∑ z ∈ Z, (multiplicity z:ℝ)) +
      ∑ j ∈ range r, (heightWeight (t j)-heightWeight (t (j+1))) *
        (∑ z ∈ Z.filter (fun z => |z.im|≤t (j+1)), (multiplicity z:ℝ)) := by
  classical
  calc
    _ ≤ ∑ z ∈ Z, (multiplicity z:ℝ) * (heightWeight (t r) +
          ∑ j ∈ range r, (if |z.im|≤t (j+1) then heightWeight (t j)-heightWeight (t (j+1)) else 0)) :=
      sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (weight_majorant t h0 hm (abs_nonneg _) r) (by positivity)
    _ = _ := by
      simp_rw [mul_add,mul_sum,sum_add_distrib]
      rw [sum_comm (s := Z) (t := range r)]
      congr 1
      · apply sum_congr rfl
        intro z _
        ring
      · apply sum_congr rfl
        intro j _
        rw [sum_filter]
        apply sum_congr rfl
        intro z _
        split_ifs <;> ring

end BMORLowMassCounts
end

section
/-! A bound for the two positive tail integrals in the BMOR height-two comparison. -/

namespace BMORHeightTwoLoss

open MeasureTheory Filter Set
open scoped Topology

/-- Exact affine logarithmic moments on a ray, including absolute integrability. -/
theorem affine_log_moment (k : ℕ) {A B d T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : 1 ≤ d) (hT : 1 ≤ T) :
    IntegrableOn (fun t : ℝ => (A * Real.log (d*t) + B)/t^(k+2)) (Ioi T) ∧
    ∫ t in Ioi T, (A * Real.log (d*t) + B)/t^(k+2) =
      (A * Real.log (d*T) + B + A/(k+1:ℝ))/((k+1:ℝ)*T^(k+1)) := by
  let r : ℝ := k+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hd0 : 0 < d := by linarith
  let g := fun t : ℝ => -((A*Real.log (d*t)+B+A/r)/(r*t^(k+1)))
  let f := fun t : ℝ => (A*Real.log (d*t)+B)/t^(k+2)
  have hder (x : ℝ) (hx : x ∈ Ici T) : HasDerivAt g (f x) x := by
    have hx0 : 0<x := lt_of_lt_of_le (by linarith : 0<T) hx
    have hl := (((hasDerivAt_id x).const_mul d).log (mul_ne_zero hd0.ne' hx0.ne'))
    have hdv := (((hl.const_mul A).add_const B).add_const (A/r)).div
      ((hasDerivAt_pow (k+1) x).const_mul r) (mul_ne_zero hr.ne' (pow_ne_zero _ hx0.ne'))
    convert hdv.neg using 1
    · rfl
    · simp only [f,id_eq,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,show (k:ℝ)+1 = r by rfl,pow_succ]
      field_simp [hx0.ne',hd0.ne',hr.ne',pow_ne_zero k hx0.ne']
      ring
  have hnonneg (x : ℝ) (hx : x ∈ Ioi T) : 0 ≤ f x := by
    have hx1 : 1 ≤ x := hT.trans hx.le
    have hlog := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hx1)
    dsimp [f]
    positivity
  have hi : Tendsto (fun x : ℝ => (x^(k+1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (Nat.succ_ne_zero k))
  have hl : Tendsto (fun x : ℝ => Real.log x / x^(k+1)) atTop (𝓝 0) := by
    have hk : 0 < ((k+1:ℕ):ℝ) := by positivity
    simpa only [Real.rpow_natCast] using (isLittleO_log_rpow_atTop hk).tendsto_div_nhds_zero
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hv := (((hi.const_mul (A*Real.log d+B+A/r)).add (hl.const_mul A)).div_const r).neg
    simp only [mul_zero,add_zero,zero_div,neg_zero] at hv
    apply hv.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    dsimp [g]
    rw [Real.log_mul hd0.ne' hx.ne']
    ring
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hder hnonneg hlim, ?_⟩
  simpa only [f,g,r,zero_sub,neg_neg] using integral_Ioi_of_hasDerivAt_of_nonneg' hder hnonneg hlim

/-- The error 0.399 log(dt) + 5.338 in the tail integral. -/
noncomputable def E (d t : ℝ) := 399/1000 * Real.log (d*t) + 5338/1000

theorem two_integrals {d T : ℝ} (hd : 1 ≤ d) (hT : 1 ≤ T) :
    2*(∫ t in Ioi T, E d t/t^2) +
        (3/8)*(∫ t in Ioi T, ((t/3)*Real.log (d*t)+E d t)/t^4) =
    2*((399/1000)*(Real.log (d*T)+1)+5338/1000)/T +
      ((Real.log (d*T)+1/2)/(2*T^2) +
        ((399/1000)*(Real.log (d*T)+1/3)+5338/1000)/T^3)/8 := by
  have h0 := affine_log_moment 0 (A:=399/1000) (B:=5338/1000) (by norm_num) (by norm_num) hd hT
  have h1 := affine_log_moment 1 (A:=1/3) (B:=0) (by norm_num) (by norm_num) hd hT
  have h2 := affine_log_moment 2 (A:=399/1000) (B:=5338/1000) (by norm_num) (by norm_num) hd hT
  have hs : (∫ t in Ioi T, ((t/3)*Real.log (d*t)+E d t)/t^4) =
      (∫ t in Ioi T, ((1/3)*Real.log (d*t)+0)/t^3) + (∫ t in Ioi T, E d t/t^4) := by
    unfold E
    rw [← integral_add h1.1 h2.1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0<t := by linarith [show T<t from ht]
    field_simp
    ring
  rw [hs]
  unfold E
  rw [h0.2,h1.2,h2.2]
  norm_num
  ring

private theorem log_210_lt : Real.log 210 < 27/5 := by
  have he : (271/100:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hp : (210:ℝ)^5 < (Real.exp 1)^27 := calc
    (210:ℝ)^5 < (271/100:ℝ)^27 := by norm_num
    _ < (Real.exp 1)^27 := by gcongr
  have hl := Real.log_lt_log (by norm_num : (0:ℝ) < 210^5) hp
  rw [Real.log_pow, Real.log_pow, Real.log_exp] at hl
  norm_num at hl
  linarith

/-- Numerical tail loss at the lower height 2, uniformly for conductor 1 through 105. -/
theorem height_two_loss_sharp (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 105) :
    2*(∫ t in Ioi (2:ℝ), E d t/t^2) +
        (3/8)*(∫ t in Ioi (2:ℝ), ((t/3)*Real.log ((d:ℝ)*t)+E d t)/t^4) < 129647/16000 := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hd105 : (d:ℝ) ≤ 105 := by exact_mod_cast hd'
  have hlog : Real.log ((d:ℝ)*2) < 27/5 :=
    (Real.log_le_log (by positivity) (by linarith : (d:ℝ)*2 ≤ 210)).trans_lt log_210_lt
  rw [two_integrals hd1 (by norm_num)]
  linarith


/-- The same two integrals decrease when the truncation height increases.
The stated constant follows from the strict bound log(210) < 27/5. -/
theorem height_tail_loss_sharp (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 105)
    {T : ℝ} (hT : 2 ≤ T) :
    2*(∫ t in Ioi T, E d t/t^2) +
        (3/8)*(∫ t in Ioi T, ((t/3)*Real.log ((d:ℝ)*t)+E d t)/t^4) < 129647/16000 := by
  have h1d : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hs : Ioi T ⊆ Ioi (2:ℝ) := Ioi_subset_Ioi hT
  have h0 := (affine_log_moment 0 (A:=399/1000) (B:=5338/1000) (by norm_num) (by norm_num) h1d
    (by norm_num : (1:ℝ)≤2)).1
  have h1 := (affine_log_moment 1 (A:=1/3) (B:=0) (by norm_num) (by norm_num) h1d
    (by norm_num : (1:ℝ)≤2)).1
  have h2 := (affine_log_moment 2 (A:=399/1000) (B:=5338/1000) (by norm_num) (by norm_num) h1d
    (by norm_num : (1:ℝ)≤2)).1
  have hrest : IntegrableOn (fun t : ℝ => ((t/3)*Real.log ((d:ℝ)*t)+E d t)/t^4) (Ioi (2:ℝ)) := by
    apply (h1.add h2).congr_fun _ measurableSet_Ioi
    intro t ht
    have ht0 : 0<t := by linarith [show 2<t from ht]
    simp only [Pi.add_apply,E]
    field_simp
    ring
  have hp (t : ℝ) (ht : t ∈ Ioi (2:ℝ)) : 0 ≤ Real.log ((d:ℝ)*t) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le h1d (by linarith [show 2<t from ht]))
  have hL : (∫ t in Ioi T, E d t/t^2) ≤ ∫ t in Ioi (2:ℝ), E d t/t^2 := by
    apply setIntegral_mono_set h0 _ (Filter.Eventually.of_forall hs)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hlog := hp t ht
    dsimp [E]
    positivity
  have hR : (∫ t in Ioi T, ((t/3)*Real.log ((d:ℝ)*t)+E d t)/t^4) ≤
      ∫ t in Ioi (2:ℝ), ((t/3)*Real.log ((d:ℝ)*t)+E d t)/t^4 := by
    apply setIntegral_mono_set hrest _ (Filter.Eventually.of_forall hs)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hlog := hp t ht
    have ht0 : 0<t := by linarith [show 2<t from ht]
    dsimp [E]
    positivity
  exact (add_le_add (mul_le_mul_of_nonneg_left hL (by norm_num))
    (mul_le_mul_of_nonneg_left hR (by norm_num))).trans_lt (height_two_loss_sharp d hd hd')

theorem height_two_loss (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 105) :
    2*(∫ t in Ioi (2:ℝ), E d t/t^2) +
        (3/8)*(∫ t in Ioi (2:ℝ), ((t/3)*Real.log ((d:ℝ)*t)+E d t)/t^4) < 41/5 :=
  (height_two_loss_sharp d hd hd').trans (by norm_num)

end BMORHeightTwoLoss
end

section
/-! Finiteness and multiplicities for zeros of the actual Dirichlet L-function
in the critical strip, including both height endpoints. -/
namespace BMORStripZeroCount

open Set Complex DirichletCharacter BMORProgression MeromorphicOn
open scoped Topology

private theorem analytic_poleRemoved {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (poleRemoved χ) univ := by
  classical
  by_cases h : χ=1
  · subst χ
    intro z _
    simpa only [poleRemoved,ite_true] using (differentiable_LFunctionTrivChar₁ q).analyticAt z
  · intro z _
    simpa only [poleRemoved,ite_eq_right h] using (differentiable_LFunction h).analyticAt z

private theorem regular_order_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    analyticOrderAt (poleRemoved χ) s ≠ ⊤ := by
  have ha := analytic_poleRemoved χ
  have hx : analyticOrderAt (poleRemoved χ) (2:ℂ) = 0 :=
    (ha 2 (mem_univ _)).analyticOrderAt_eq_zero.mpr (poleRemoved_ne_zero_right χ (by norm_num))
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2:ℂ)) (mem_univ s) (by rw [hx]; exact ENat.zero_ne_top)

/-- Regularizing the principal pole at 1 preserves the analytic multiplicity
of every zero away from 1. -/
theorem order_poleRemoved_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt (poleRemoved χ) s = analyticOrderAt (LFunction χ) s := by
  classical
  by_cases h : χ=1
  · subst χ
    let g := fun z : ℂ => z-1
    have hg : AnalyticAt ℂ g s := analyticAt_id.sub analyticAt_const
    have hL : DifferentiableOn ℂ (LFunction (1 : DirichletCharacter ℂ q)) ({1}ᶜ : Set ℂ) :=
      fun z hz => (differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt
    have hLa : AnalyticAt ℂ (LFunction (1 : DirichletCharacter ℂ q)) s :=
      (hL.analyticOnNhd isOpen_compl_singleton) s hs
    have ev : poleRemoved (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
        g * LFunction (1 : DirichletCharacter ℂ q) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with z hz
      simp only [poleRemoved,ite_true,LFunctionTrivChar₁,Function.update_of_ne hz,Pi.mul_apply,g]
    rw [analyticOrderAt_congr ev,analyticOrderAt_mul hg hLa,
      hg.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs),zero_add]
  · simp [poleRemoved,h]

/-- Actual zeros have strictly positive analytic multiplicity, with no exceptional
infinite-order case. -/
theorem LFunction_order_pos_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) : 0 < analyticOrderNatAt (LFunction χ) s ↔ LFunction χ s = 0 := by
  have hf : analyticOrderAt (LFunction χ) s ≠ ⊤ :=
    (order_poleRemoved_eq χ hs) ▸ regular_order_finite χ s
  have hL : DifferentiableOn ℂ (LFunction χ) ({1}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have ha := (hL.analyticOnNhd isOpen_compl_singleton) s (show s ∈ ({1}ᶜ : Set ℂ) from hs)
  constructor
  · exact fun h => apply_eq_zero_of_analyticOrderNatAt_ne_zero h.ne'
  · intro h
    apply Nat.pos_of_ne_zero
    intro he
    apply ha.analyticOrderAt_ne_zero.mpr h
    rw [← Nat.cast_analyticOrderNatAt hf,he,Nat.cast_zero]

theorem stripZeros_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ LFunction χ z = 0}.Finite := by
  classical
  let rectangle := Icc (0:ℝ) 1 ×ℂ Icc (-T) T
  have hc : IsCompact rectangle := isCompact_Icc.reProdIm isCompact_Icc
  apply ((divisor (poleRemoved χ) rectangle).finiteSupport hc).subset
  intro z hz
  obtain ⟨hlo,hhi,ht,hzero⟩ := hz
  have hn : z ≠ 1 := fun h => by simp [h] at hhi
  have hmem : z ∈ rectangle := ⟨⟨hlo.le,hhi.le⟩,abs_le.mp ht⟩
  have hdiv := ((analytic_poleRemoved χ).mono (subset_univ rectangle)).divisor_apply hmem
  change divisor (poleRemoved χ) rectangle z ≠ 0
  rw [hdiv,order_poleRemoved_eq χ hn,← Nat.cast_analyticOrderNatAt
    (show analyticOrderAt (LFunction χ) z ≠ ⊤ from (order_poleRemoved_eq χ hn) ▸ regular_order_finite χ z),
    ENat.map_natCast,WithTop.untop₀_coe]
  exact_mod_cast ((LFunction_order_pos_iff χ hn).mpr hzero).ne'

noncomputable def zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ :=
  (stripZeros_finite χ T).toFinset

@[simp] theorem mem_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) (z : ℂ) :
    z ∈ zeros χ T ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ LFunction χ z = 0 :=
  (stripZeros_finite χ T).mem_toFinset

theorem filter_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u T : ℝ} (h : u ≤ T) :
    (zeros χ T).filter (fun z => |z.im| ≤ u) = zeros χ u := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_zeros]
  grind

/-- Number of critical-strip zeros of height at most T, counting analytic
multiplicities and both positive and negative imaginary parts. -/
noncomputable def count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  ∑ z ∈ zeros χ T, analyticOrderNatAt (LFunction χ) z

theorem count_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Monotone (count χ) := by
  classical
  intro u T h
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro z hz
  obtain ⟨hs,hu,ht,hz0⟩ := (mem_zeros χ u z).mp hz
  exact (mem_zeros χ T z).mpr ⟨hs,hu,ht.trans h,hz0⟩

theorem weighted_count_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {T : ℝ} (hT : 1 ≤ T) :
    (∑ z ∈ zeros χ T, (analyticOrderNatAt (LFunction χ) z:ℝ)/Real.sqrt (z.im^2+1/4)) ≤
      (2-2/Real.sqrt 5)*(count χ 1:ℝ) + (2/Real.sqrt 5)*(count χ T:ℝ) := by
  classical
  apply BMORLowMassCounts.LFunction_weighted_bound
  · rw [filter_zeros χ hT]
    simp [count]
  · simp [count]

/-- Upper counts at any nested list of height cuts, now for the actual
Dirichlet zeros and their true analytic multiplicities. -/
theorem weighted_count_at_cuts {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℕ → ℝ) (h0 : t 0=0) (hm : Monotone t) (r : ℕ) :
    (∑ z ∈ zeros χ (t r), (analyticOrderNatAt (LFunction χ) z:ℝ) *
        BMORLowMassCounts.heightWeight |z.im|) ≤
    BMORLowMassCounts.heightWeight (t r)*(count χ (t r):ℝ) +
      ∑ j ∈ Finset.range r, (BMORLowMassCounts.heightWeight (t j) -
        BMORLowMassCounts.heightWeight (t (j+1)))*(count χ (t (j+1)):ℝ) := by
  classical
  have h := BMORLowMassCounts.weighted_bound_at_cuts
    (zeros χ (t r)) (analyticOrderNatAt (LFunction χ)) t h0 hm r
  refine h.trans_eq ?_
  unfold count
  simp only [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [filter_zeros χ (hm (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))]

end BMORStripZeroCount
end

section
/-! Critical-strip zero sets and their analytic multiplicities are unchanged
by inflating a Dirichlet character from its conductor. -/
namespace BMORPrimitiveStripCount

open Complex DirichletCharacter BMORStripZeroCount BMORProgression

theorem changeLevel_zeros_eq {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) (T : ℝ) :
    zeros (changeLevel hd χ) T = zeros χ T := by
  classical
  ext s
  simp only [mem_zeros]
  by_cases h : 0 < s.re ∧ s.re < 1
  · have hp : s ≠ 1 := fun e => by simp [e] at h
    rw [LFunction_changeLevel_zero_iff hd χ h.1 (Or.inr hp)]
  · tauto

theorem changeLevel_multiplicity_eq {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) {s : ℂ} (hL : 0 < s.re) (hR : s.re < 1) :
    analyticOrderNatAt (LFunction (changeLevel hd χ)) s = analyticOrderNatAt (LFunction χ) s := by
  have hp : s ≠ 1 := fun e => by simp [e] at hR
  exact congrArg ENat.toNat (LFunction_changeLevel_order hd χ hL hp)

theorem changeLevel_count_eq {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) (T : ℝ) :
    count (changeLevel hd χ) T = count χ T := by
  classical
  unfold count
  rw [changeLevel_zeros_eq]
  apply Finset.sum_congr rfl
  intro s hs
  have hz := (mem_zeros χ T s).mp hs
  exact changeLevel_multiplicity_eq hd χ hz.1 hz.2.1

theorem primitive_zeros_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    zeros χ T = zeros χ.primitiveCharacter T := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [changeLevel_primitiveCharacter] using
    changeLevel_zeros_eq χ.conductor_dvd_level χ.primitiveCharacter T

theorem primitive_count_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    count χ T = count χ.primitiveCharacter T := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [changeLevel_primitiveCharacter] using
    changeLevel_count_eq χ.conductor_dvd_level χ.primitiveCharacter T

/-- Any real weight, with the actual analytic multiplicities, is preserved. -/
theorem primitive_weighted_sum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (w : ℂ → ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ∑ s ∈ zeros χ T, (analyticOrderNatAt (LFunction χ) s : ℝ) * w s =
      ∑ s ∈ zeros χ.primitiveCharacter T, (analyticOrderNatAt (LFunction χ.primitiveCharacter) s : ℝ) * w s := by
  classical
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [primitive_zeros_eq χ T]
  apply Finset.sum_congr rfl
  intro s hs
  have hz := (mem_zeros χ.primitiveCharacter T s).mp hs
  have hp : s ≠ 1 := fun e => by have h := hz.2.1; simp [e] at h
  rw [primitive_order_eq χ hz.1 hp]

end BMORPrimitiveStripCount
end

section
namespace BMORConductorParity
open Finset DirichletCharacter
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def sign (odd : Bool) : ℂ := if odd then -1 else 1

def family (q : ℕ) (odd : Bool) : Finset (DirichletCharacter ℂ q) :=
  univ.filter (fun χ => χ (-1) = sign odd)

def count (q d : ℕ) (odd : Bool) : ℕ :=
  ((family q odd).filter (fun χ => χ.conductor = d)).card

theorem parity_card (q : ℕ) [NeZero q] (odd : Bool) :
    (2:ℂ) * (family q odd).card =
      (q.totient:ℂ) + sign odd * (if (-1 : ZMod q) = 1 then (q.totient:ℂ) else 0) := by
  classical
  have hχ (χ : DirichletCharacter ℂ q) :
      (if χ (-1) = sign odd then (2 : ℂ) else 0) = 1 + sign odd * χ (-1) := by
    rcases χ.even_or_odd with h | h <;> change χ (-1) = _ at h <;>
      cases odd <;> norm_num [sign,h]
  have h := Finset.sum_congr (s₁ := (univ : Finset (DirichletCharacter ℂ q))) rfl (fun χ _ => hχ χ)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity,
    sum_characters_eq] at h
  rw [← h]
  simp [family, Finset.sum_ite, mul_comm]

private theorem lift_sign {q d : ℕ} (hd : d ∣ q) (χ : DirichletCharacter ℂ d) :
    changeLevel hd χ (-1) = χ (-1) := by
  simpa using changeLevel_eq_cast_of_dvd' χ hd (a := (-1:ℤ)) ⟨-1,0,by ring⟩

theorem count_divisors {q d : ℕ} [NeZero q] [NeZero d] (hd : d ∣ q) (odd : Bool) :
    ∑ k ∈ d.divisors, count q k odd = (family d odd).card := by
  classical
  unfold count
  rw [sum_card_fiberwise_eq_card_filter]
  symm
  apply Finset.card_bij (fun χ _ => changeLevel hd χ)
  · intro χ hχ
    simp only [mem_filter, family, mem_univ, true_and] at hχ ⊢
    exact ⟨(lift_sign hd χ).trans hχ, Nat.mem_divisors.mpr
      ⟨by rw [conductor_changeLevel]; exact conductor_dvd_level χ, NeZero.ne d⟩⟩
  · intro χ _ ψ _ h
    exact changeLevel_injective hd h
  · intro χ hχ
    simp only [mem_filter, family, mem_univ, true_and] at hχ
    obtain ⟨_,ψ,hψ⟩ := (mem_conductorSet_iff_conductor_dvd χ hd).mpr (Nat.mem_divisors.mp hχ.2).1
    exact ⟨ψ, by simpa [family, hψ, lift_sign] using hχ.1, hψ.symm⟩
theorem profile104 (odd : Bool) :
    count 104 1 odd = (if odd then 0 else 1) ∧
    count 104 2 odd = 0 ∧
    count 104 4 odd = (if odd then 1 else 0) ∧
    count 104 8 odd = 1 ∧
    count 104 13 odd = (if odd then 6 else 5) ∧
    count 104 26 odd = 0 ∧
    count 104 52 odd = (if odd then 5 else 6) ∧
    count 104 104 odd = 11 := by
  have h1 := count_divisors (q := 104) (d := 1) (by decide) odd
  rw [show (1:ℕ).divisors = {1} by decide] at h1
  norm_num [Finset.sum_insert] at h1
  have n1 : (family 1 odd).card = (if odd then 0 else 1) := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (1:ℕ).totient = 1 by decide, ite_eq_left (by decide : ((-1:ZMod 1) = 1))]
    cases odd <;> norm_num [sign]
  have h2 := count_divisors (q := 104) (d := 2) (by decide) odd
  rw [show (2:ℕ).divisors = {1,2} by decide] at h2
  norm_num [Finset.sum_insert] at h2
  have n2 : (family 2 odd).card = (if odd then 0 else 1) := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (2:ℕ).totient = 1 by decide, ite_eq_left (by decide : ((-1:ZMod 2) = 1))]
    cases odd <;> norm_num [sign]
  have h4 := count_divisors (q := 104) (d := 4) (by decide) odd
  rw [show (4:ℕ).divisors = {1,2,4} by decide] at h4
  norm_num [Finset.sum_insert] at h4
  have n4 : (family 4 odd).card = 1 := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (4:ℕ).totient = 2 by decide, ite_eq_right (by decide : ¬ ((-1:ZMod 4) = 1))]
    cases odd <;> norm_num [sign]
  have h8 := count_divisors (q := 104) (d := 8) (by decide) odd
  rw [show (8:ℕ).divisors = {1,2,4,8} by decide] at h8
  norm_num [Finset.sum_insert] at h8
  have n8 : (family 8 odd).card = 2 := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (8:ℕ).totient = 4 by decide, ite_eq_right (by decide : ¬ ((-1:ZMod 8) = 1))]
    cases odd <;> norm_num [sign]
  have h13 := count_divisors (q := 104) (d := 13) (by decide) odd
  rw [show (13:ℕ).divisors = {1,13} by decide] at h13
  norm_num [Finset.sum_insert] at h13
  have n13 : (family 13 odd).card = 6 := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (13:ℕ).totient = 12 by decide, ite_eq_right (by decide : ¬ ((-1:ZMod 13) = 1))]
    cases odd <;> norm_num [sign]
  have h26 := count_divisors (q := 104) (d := 26) (by decide) odd
  rw [show (26:ℕ).divisors = {1,2,13,26} by decide] at h26
  norm_num [Finset.sum_insert] at h26
  have n26 : (family 26 odd).card = 6 := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (26:ℕ).totient = 12 by decide, ite_eq_right (by decide : ¬ ((-1:ZMod 26) = 1))]
    cases odd <;> norm_num [sign]
  have h52 := count_divisors (q := 104) (d := 52) (by decide) odd
  rw [show (52:ℕ).divisors = {1,2,4,13,26,52} by decide] at h52
  norm_num [Finset.sum_insert] at h52
  have n52 : (family 52 odd).card = 12 := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (52:ℕ).totient = 24 by decide, ite_eq_right (by decide : ¬ ((-1:ZMod 52) = 1))]
    cases odd <;> norm_num [sign]
  have h104 := count_divisors (q := 104) (d := 104) (by decide) odd
  rw [show (104:ℕ).divisors = {1,2,4,8,13,26,52,104} by decide] at h104
  norm_num [Finset.sum_insert] at h104
  have n104 : (family 104 odd).card = 24 := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    rw [parity_card, show (104:ℕ).totient = 48 by decide, ite_eq_right (by decide : ¬ ((-1:ZMod 104) = 1))]
    cases odd <;> norm_num [sign]
  cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
/-- The caps in BMOR (2021), Table 1 at height 2, restricted to conductors ≤ 104.
This definition records the numbers, without assuming that they bound any zeros. -/
def cap (odd : Bool) (d : ℕ) : ℕ :=
  if odd then (if d ≤ 10 then 0 else if d ≤ 18 then 1 else if d ≤ 64 then 2 else 3)
  else (if d ≤ 16 then 0 else if d ≤ 28 then 1 else 2)

theorem cap_sum104 (odd : Bool) :
    ∑ χ ∈ family 104 odd, cap odd χ.conductor = (if odd then 49 else 34) := by
  classical
  have hm (χ : DirichletCharacter ℂ 104) (_ : χ ∈ family 104 odd) :
      χ.conductor ∈ (104:ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, by decide⟩
  have h := sum_fiberwise_of_maps_to' hm (cap odd)
  simp only [sum_const, nsmul_eq_mul] at h
  rw [← h]
  change ∑ d ∈ (104:ℕ).divisors, count 104 d odd * cap odd d = _
  rw [show (104:ℕ).divisors = {1,2,4,8,13,26,52,104} by decide]
  obtain ⟨h1,h2,h4,h8,h13,h26,h52,h104⟩ := profile104 odd
  cases odd <;> norm_num [Finset.sum_insert, cap, *]

theorem sum_split104 (F : DirichletCharacter ℂ 104 → ℕ) :
    ∑ χ, F χ = (∑ χ ∈ family 104 false, F χ) + ∑ χ ∈ family 104 true, F χ := by
  classical
  unfold family
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro χ _
  rcases χ.even_or_odd with h | h <;> change χ (-1) = _ at h <;> norm_num [sign,h]

theorem total_le_of_caps104 (F : DirichletCharacter ℂ 104 → ℕ)
    (h : ∀ b, ∀ χ ∈ family 104 b, F χ ≤ cap b χ.conductor) :
    ∑ χ, F χ ≤ 83 := by
  rw [sum_split104 F]
  have hb (b : Bool) := (sum_le_sum (h b)).trans_eq (cap_sum104 b)
  exact (add_le_add (hb false) (hb true) : _ ≤ 34+49)
end
end BMORConductorParity
end

section
namespace BMORHeightTwo104
open Finset DirichletCharacter BMORConductorParity

/-- Only primitive characters of divisors of 104 are needed in the counting hypothesis. -/
theorem count_total
    (h : ∀ (d : ℕ) [NeZero d], d ∣ 104 → ∀ (ψ : DirichletCharacter ℂ d),
      ψ.IsPrimitive → ∀ b, ψ (-1) = sign b → BMORStripZeroCount.count ψ 2 ≤ cap b d) :
    ∑ χ : DirichletCharacter ℂ 104, BMORStripZeroCount.count χ 2 ≤ 83 := by
  apply total_le_of_caps104
  intro b χ hχ
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [BMORPrimitiveStripCount.primitive_count_eq χ]
  apply h χ.conductor χ.conductor_dvd_level χ.primitiveCharacter χ.primitiveCharacter_isPrimitive b
  have hsign : χ.primitiveCharacter (-1) = χ (-1) := by
    simpa using χ.primitiveCharacter_apply_of_isCoprime (a := (-1:ℤ)) ⟨-1,0,by ring⟩
  exact hsign.trans (Finset.mem_filter.mp hχ).2

/-- Net height-two term: each zero contributes its reciprocal weight minus 1/2.
Multiplicity is the actual analytic multiplicity of its L-function. -/
theorem net_weight (χ : DirichletCharacter ℂ 104) :
    (∑ z ∈ BMORStripZeroCount.zeros χ 2,
      (analyticOrderNatAt (LFunction χ) z:ℝ) / Real.sqrt (z.im^2+1/4)) -
      (BMORStripZeroCount.count χ 2:ℝ)/2 ≤ (3/2:ℝ) * BMORStripZeroCount.count χ 2 := by
  have h := BMORStripZeroCount.weighted_count_bound χ (T:=2) (by norm_num)
  have hc : (BMORStripZeroCount.count χ 1:ℝ) ≤ BMORStripZeroCount.count χ 2 := by
    exact_mod_cast (BMORStripZeroCount.count_mono χ (by norm_num : (1:ℝ)≤2))
  have p : (0:ℝ)<Real.sqrt 5 := by positivity
  have r : (1:ℝ) ≤ Real.sqrt 5 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  have hcoeff : (0:ℝ) ≤ 2-2/Real.sqrt 5 := sub_nonneg.mpr ((div_le_iff₀ p).mpr (by linarith))
  linarith [mul_le_mul_of_nonneg_left hc hcoeff]

theorem average_net_weight
    (h : ∀ (d : ℕ) [NeZero d], d ∣ 104 → ∀ (ψ : DirichletCharacter ℂ d),
      ψ.IsPrimitive → ∀ b, ψ (-1) = sign b → BMORStripZeroCount.count ψ 2 ≤ cap b d) :
    (∑ χ : DirichletCharacter ℂ 104, ((∑ z ∈ BMORStripZeroCount.zeros χ 2,
      (analyticOrderNatAt (LFunction χ) z:ℝ) / Real.sqrt (z.im^2+1/4)) -
      (BMORStripZeroCount.count χ 2:ℝ)/2)) / 48 ≤ 83/32 := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun χ _ => net_weight χ)
  rw [← Finset.mul_sum] at hsum
  have hc : (∑ χ : DirichletCharacter ℂ 104, (BMORStripZeroCount.count χ 2:ℝ)) ≤ 83 := by
    exact_mod_cast count_total h
  linarith
/-- For this modulus the table is needed only at four conductors. The
conductor-one and conductor-four cases follow from previously proved zero-free
strips. The character profile rules out primitive conductors two and 26. -/
theorem four_conductor_reduction
    (h : ∀ (d : ℕ) [NeZero d], d ∈ ({8,13,52,104} : Finset ℕ) →
      ∀ (ψ : DirichletCharacter ℂ d), ψ.IsPrimitive → ∀ b,
      ψ (-1) = sign b → BMORStripZeroCount.count ψ 2 ≤ cap b d) :
    ∀ (d : ℕ) [NeZero d], d ∣ 104 → ∀ (ψ : DirichletCharacter ℂ d),
      ψ.IsPrimitive → ∀ b, ψ (-1) = sign b → BMORStripZeroCount.count ψ 2 ≤ cap b d := by
  classical
  intro d _ hd ψ hprim b hb
  by_cases hrest : d ∈ ({8,13,52,104} : Finset ℕ)
  · exact h d hrest ψ hprim b hb
  have hdvd : d ∈ (104:ℕ).divisors := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show (104:ℕ).divisors = {1,2,4,8,13,26,52,104} by decide] at hdvd
  simp only [mem_insert,mem_singleton] at hdvd hrest
  have hbad (hh : d = 2 ∨ d = 26) : False := by
    let χ := changeLevel hd ψ
    have hc : χ.conductor = d := (conductor_changeLevel ψ hd).trans hprim
    have ha : χ (-1) = sign b := by
      have eqv := changeLevel_eq_cast_of_dvd' ψ hd (a := (-1:ℤ)) ⟨-1,0,by ring⟩
      exact (by simpa [χ] using eqv : χ (-1) = ψ (-1)).trans hb
    have hp : 0 < count 104 d b := Finset.card_pos.mpr
      ⟨χ, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ha⟩,hc⟩⟩
    obtain ⟨_,h2,_,_,_,h26,_,_⟩ := profile104 b
    rcases hh with rfl | rfl <;> omega
  have hsmall : d = 1 ∨ d = 4 := by tauto
  suffices nz : ∀ s ∈ BMORStripZeroCount.zeros ψ 2, False by
    rw [BMORStripZeroCount.count, Finset.eq_empty_iff_forall_notMem.mpr nz, Finset.sum_empty]
    exact Nat.zero_le _
  intro s hs
  obtain ⟨hl,hu,ht,hz⟩ := (BMORStripZeroCount.mem_zeros ψ 2 s).mp hs
  rcases hsmall with rfl | rfl
  · have hone : ψ = 1 := eq_one_iff_conductor_eq_one.mpr hprim
    rw [hone] at hz
    exact BMORProgression.principal_low_band_nonzero hl hu.le ht (fun e => by simp [e] at hu) hz
  · exact BMORProgression.height_two_small_moduli (Or.inr (Or.inl rfl)) ψ hl hu ht hz

end BMORHeightTwo104
end

section
namespace BMORCountBoxes
open Finset DirichletCharacter BMORStripZeroCount

/-- A derivative enclosed in a disk missing zero gives injectivity on a convex box. -/
theorem injOn_of_deriv_disk {f : ℂ → ℂ} {S : Set ℂ} (hs : Convex ℝ S)
    {a : ℂ} {r : ℝ} (hr : r < ‖a‖) (hf : ∀ z ∈ S, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ S, ‖deriv f z - a‖ ≤ r) : Set.InjOn f S := by
  intro x hx y hy hxy
  by_contra hn
  have hp : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hn))
  have hg (z : ℂ) (hz : z ∈ S) : HasDerivWithinAt (fun w => f w-a*w) (deriv f z-a) S z := by
    change HasDerivWithinAt (f - fun w : ℂ => a*w) (deriv f z-a) S z
    simpa using ((hf z hz).hasDerivAt.sub ((hasDerivAt_id z).const_mul a)).hasDerivWithinAt
  have hm := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hg hd hx hy
  have eqv : (f y-a*y)-(f x-a*x) = -(a*(y-x)) := by rw [hxy]; ring
  rw [eqv,norm_neg,norm_mul] at hm
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hr hp)) hm

theorem count_of_cover {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    {k : ℕ} (box : Fin k → Set ℂ) (a : Fin k → ℂ) (r : Fin k → ℝ)
    (hcover : ∀ z ∈ zeros χ T, ∃ i, z ∈ box i)
    (hc : ∀ i, Convex ℝ (box i)) (hr : ∀ i, r i < ‖a i‖)
    (ha : ∀ i z, z ∈ box i → AnalyticAt ℂ (LFunction χ) z)
    (hd : ∀ i z, z ∈ box i → ‖deriv (LFunction χ) z - a i‖ ≤ r i) :
    count χ T ≤ k := by
  classical
  have uniq (i : Fin k) := injOn_of_deriv_disk (hc i) (hr i)
    (fun z hz => (ha i z hz).differentiableAt) (hd i)
  have simple (z : ℂ) (hz : z ∈ zeros χ T) : analyticOrderNatAt (LFunction χ) z = 1 := by
    obtain ⟨i,hi⟩ := hcover z hz
    have hne : deriv (LFunction χ) z ≠ 0 := by
      intro h
      have bad := hd i z hi
      rw [h,zero_sub,norm_neg] at bad
      exact (hr i).not_ge bad
    have ord := (ha i z hi).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      ((mem_zeros χ T z).mp hz).2.2.2 hne
    simp [analyticOrderNatAt, ord]
  have hinj : Function.Injective (fun z : ↥(zeros χ T) => (hcover z z.property).choose) := by
    intro x y he
    apply Subtype.ext
    have hx := (hcover x x.property).choose_spec
    have hy := (hcover y y.property).choose_spec
    change (hcover x x.property).choose = (hcover y y.property).choose at he
    rw [← he] at hy
    exact uniq _ hx hy (((mem_zeros χ T x).mp x.property).2.2.2.trans
      ((mem_zeros χ T y).mp y.property).2.2.2.symm)
  calc
    count χ T = (zeros χ T).card := by
      unfold count
      rw [Finset.sum_congr rfl simple]
      simp
    _ ≤ k := by simpa using Fintype.card_le_of_injective _ hinj

end BMORCountBoxes
end

section
namespace BMORModEight
open Complex DirichletCharacter Finset MeasureTheory Set BMORModThree.Mellin

def intChar (odd : Bool) : MulChar (ZMod 8) ℤ := if odd then ZMod.χ₈' else ZMod.χ₈

noncomputable def character (odd : Bool) : DirichletCharacter ℂ 8 :=
  (intChar odd).ringHomComp (Int.castRingHom ℂ)

def block (odd : Bool) (n : ℕ) : ℤ :=
  let k := n % 8
  if k=1 ∨ k=2 then 1 else
  if k=5 ∨ k=6 then (if odd then 1 else -1) else
  if k=3 ∨ k=4 then (if odd then 2 else 0) else 0

theorem char_apply (odd : Bool) (a : ZMod 8) : character odd a=((intChar odd a:ℤ):ℂ) := rfl

theorem char_five (odd : Bool) : character odd 5 = -1 := by
  have h : ∀ b : Bool, intChar b 5 = -1 := by decide
  rw [char_apply,h]; norm_num

theorem character_nonprincipal (odd : Bool) : character odd ≠ 1 := by
  intro h
  have hc := char_five odd
  have unit : IsUnit (5 : ZMod 8) := (ZMod.isUnit_iff_coprime 5 8).mpr (by decide)
  rw [h,MulChar.one_apply unit] at hc
  norm_num at hc

theorem lifted_at_five (χ : DirichletCharacter ℂ 4) :
    changeLevel (show 4 ∣ 8 by decide) χ (5 : ZMod 8)=1 := by
  have h := changeLevel_eq_cast_of_dvd χ (show 4 ∣ 8 by decide)
    (ZMod.unitOfCoprime 5 (show Nat.Coprime 5 8 by decide))
  rw [ZMod.coe_unitOfCoprime,ZMod.cast_natCast (show 4∣8 by decide)] at h
  simpa [show (5:ZMod 4)=1 by decide] using h

theorem char_primitive (odd : Bool) : (character odd).IsPrimitive := by
  let χ := character odd
  have no4 : ¬χ.FactorsThrough 4 := by
    rintro ⟨hd,ψ,he⟩
    have eq := congrArg (fun f : DirichletCharacter ℂ 8 => f (5:ZMod 8)) he
    change character odd 5 = changeLevel hd ψ 5 at eq
    rw [char_five,lifted_at_five] at eq
    norm_num at eq
  have hd := χ.conductor_dvd_level
  have hm := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  rw [show (8:ℕ).divisors={1,2,4,8} by decide] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  by_contra hn
  change χ.conductor ≠ 8 at hn
  have hd4 : χ.conductor ∣ 4 := by
    rcases hm with e|e|e|e <;> first | (rw [e] <;> decide) | contradiction
  exact no4 (χ.factorsThrough_conductor.mono χ hd4 (by decide))

private theorem short_blocks :
    ∀ (odd : Bool) (k : Fin 8), (∑ j ∈ range k.val, intChar odd ((j+1:ℕ):ZMod 8))=block odd k.val := by
  decide +kernel

theorem partial_eq (odd : Bool) (n : ℕ) :
    charPartialSum (character odd) n = (block odd n:ℂ) := by
  classical
  let χ := character odd
  have hn : χ≠1 := character_nonprincipal odd
  have reduce (j : ℕ) : integerRemainder χ j=charPartialSum χ j := by
    simp [integerRemainder,charMean_eq,hn]
  have per (k : ℕ) : charPartialSum χ (k%8)=charPartialSum χ k := by
    simpa only [reduce] using (integerRemainder_periodic χ).map_mod_nat k
  rw [←per n]
  have hs := congrArg (fun i : ℤ => (i:ℂ)) (short_blocks odd ⟨n%8,Nat.mod_lt _ (by decide)⟩)
  simpa only [charPartialSum,χ,char_apply,Int.cast_sum,block,Nat.mod_mod] using hs

noncomputable def masked (odd : Bool) (s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^(-s-1)*(block odd ⌊x⌋₊:ℂ)

theorem LFunction_eq_integral (odd : Bool) {s : ℂ} (hs : 0<s.re) :
    LFunction (character odd) s = s * ∫ x : ℝ in Ioi 1, masked odd s x := by
  rw [LFunction_eq_remainderMellin _ (character_nonprincipal odd) hs,remainderMellin_eq_integral]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  classical
  change (x:ℂ)^(-s-1)*(charPartialSum (character odd) ⌊x⌋₊-(x:ℂ)*charMean (character odd)) = masked odd s x
  rw [charMean_eq,ite_eq_right (character_nonprincipal odd),mul_zero,sub_zero,partial_eq]
  rfl

end BMORModEight
end

section
namespace BMORModEight
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- Abel summation for a bounded measurable coefficient, obtained by swapping two absolute integrals. -/
theorem abel_integral {a : ℝ→ℂ} {N : ℝ} (hN : 0<N) {s : ℂ} (hs : 0<s.re)
    (ha : Measurable a) (C : ℝ) (hc : 0≤C) (hbound : ∀ x ∈ Ioi N, ‖a x‖≤C) :
    (∫ x : ℝ in Ioi N, (x:ℂ)^(-s-1)*a x) =
      (s+1)*∫ x : ℝ in Ioi N, (x:ℂ)^(-s-2)*(∫ u in N..x, a u) := by
  let μ := volume.restrict (Ioi N)
  let K := fun p : ℝ×ℝ => if p.2<p.1 then (p.1:ℂ)^(-s-2)*a p.2 else 0
  let e := -s.re/2-1
  have he : e< -1 := by dsimp [e]; linarith
  have hi : Integrable (fun x : ℝ => x^e) μ := integrableOn_Ioi_rpow_of_lt he hN
  have mpow : Measurable (fun x : ℝ => (x:ℂ)^(-s-2)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    exact (continuousAt_ofReal_cpow_const x _ (.inr hx)).continuousWithinAt
  have hK : Measurable K := by
    unfold K
    exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
      ((mpow.comp measurable_fst).mul
        (ha.comp measurable_snd)) measurable_const
  have aeN : ∀ᵐ x ∂μ, x∈Ioi N := ae_restrict_mem measurableSet_Ioi
  have ae2 : ∀ᵐ p ∂μ.prod μ, p.1∈Ioi N ∧ p.2∈Ioi N := by
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst |>.inter
      (measurableSet_Ioi.preimage measurable_snd))).mpr (aeN.mono fun _ hx => aeN.mono fun _ hu => ⟨hx,hu⟩)
  have hKint : Integrable K (μ.prod μ) := by
    apply (hi.mul_prod (hi.const_mul C)).mono' hK.aestronglyMeasurable
    filter_upwards [ae2] with p hp
    obtain ⟨x,u⟩ := p
    have hx : 0<x := hN.trans hp.1
    have hu : 0<u := hN.trans hp.2
    change ‖if u<x then (x:ℂ)^(-s-2)*a u else 0‖ ≤ x^e*(C*u^e)
    split
    · rename_i hux
      rw [norm_mul,norm_cpow_eq_rpow_re_of_pos hx,sub_re,neg_re,show (2:ℂ).re=2 by norm_num,
        show -s.re-2=e+e by dsimp [e]; ring,Real.rpow_add hx]
      have pwr := Real.rpow_le_rpow_of_nonpos hu hux.le (he.le.trans (by norm_num : (-1:ℝ)≤0))
      calc
        _ ≤ (x^e*u^e)*C := mul_le_mul
          (mul_le_mul_of_nonneg_left pwr (Real.rpow_nonneg hx.le _)) (hbound u hp.2)
          (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hu.le _))
        _ = _ := by ring
    · rw [norm_zero]; positivity
  have left (x : ℝ) (hx : N<x) :
      (∫ u, K (x,u) ∂μ)=(x:ℂ)^(-s-2)*(∫ u in N..x, a u) := by
    calc
      _ = ∫ u in Iio x, (x:ℂ)^(-s-2)*a u ∂μ := by
        rw [←integral_indicator measurableSet_Iio]
        apply integral_congr_ae
        exact Eventually.of_forall fun u => by by_cases h : u<x <;> simp [K,h,Set.indicator_apply]
      _ = _ := by
        rw [integral_const_mul,intervalIntegral.integral_of_le hx.le,integral_Ioc_eq_integral_Ioo]
        dsimp [μ]
        rw [Measure.restrict_restrict measurableSet_Iio]
        rw [show Iio x ∩ Ioi N = Ioo N x by ext u; simp [and_comm]]
  have right (u : ℝ) (hu : N<u) :
      (s+1)*(∫ x, K (x,u) ∂μ)=(u:ℂ)^(-s-1)*a u := by
    have cut : (∫ x, K (x,u) ∂μ)= (∫ x : ℝ in Ioi u, (x:ℂ)^(-s-2))*a u := by
      calc
        _ = ∫ x in Ioi u, (x:ℂ)^(-s-2)*a u ∂μ := by
          rw [←integral_indicator (μ:=μ) (f:=fun x:ℝ => (x:ℂ)^(-s-2)*a u) measurableSet_Ioi]
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by by_cases h : u<x <;> simp [K,h,Set.indicator_apply]
        _ = _ := by
          rw [integral_mul_const]
          dsimp [μ]
          rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hu.le)]
    rw [cut,integral_Ioi_cpow_of_lt (by simp; linarith : (-s-2).re < -1) (hN.trans hu),
      show -s-2+1=-s-1 by ring]
    have hn : s+1≠0 := by
      intro eq
      have := congrArg Complex.re eq
      simp only [add_re,one_re,zero_re] at this
      linarith
    have eq : -s-1=-(s+1) := by ring
    rw [eq]
    field_simp [hn] <;> ring
  have fub := integral_integral_swap (f := fun x u => K (x,u)) hKint
  change (∫ x, (x:ℂ)^(-s-1)*a x ∂μ) = (s+1)*∫ x, (x:ℂ)^(-s-2)*(∫ u in N..x, a u) ∂μ
  calc
    _ = ∫ u, (s+1)*(∫ x, K (x,u) ∂μ) ∂μ :=
      integral_congr_ae (aeN.mono fun u hu => (right u hu).symm)
    _ = (s+1)*∫ x, (∫ u, K (x,u) ∂μ) ∂μ := by rw [integral_const_mul,fub]
    _ = _ := by congr 1; exact integral_congr_ae (aeN.mono left)

end
end BMORModEight
end

section
noncomputable section
namespace BMORModEight
open Set MeasureTheory
open scoped Interval

def oddSlope (x : ℝ) : ℝ := (block true ⌊x⌋₊ : ℝ)-1
def oddSecond (x : ℝ) : ℝ := ∫ y in (3:ℝ)..x, oddSlope y

private def vertex (n : ℕ) : ℤ :=
  if n%8=0 ∨ n%8=4 then 1 else if n%8=5 ∨ n%8=6 ∨ n%8=7 then 2 else 0

private theorem vertex_step (n : ℕ) :
    vertex (n+1)=vertex n+block true n-1 := by
  have h : ∀ k : Fin 8, vertex (k.val+1)=vertex k.val+block true k.val-1 := by decide
  simpa only [vertex,block,Nat.add_mod,Nat.mod_mod] using h ⟨n%8,Nat.mod_lt _ (by decide)⟩

private theorem vertex_bounds (n : ℕ) : (0:ℝ)≤vertex n ∧ (vertex n:ℝ)≤2 := by
  unfold vertex
  split_ifs <;> norm_num

theorem oddSlope_bound (x : ℝ) : |oddSlope x|≤1 := by
  have h : ∀ k : Fin 8, -1≤block true k.val-1 ∧ block true k.val-1≤1 := by decide
  have e := h ⟨⌊x⌋₊%8,Nat.mod_lt _ (by decide)⟩
  change -1≤block true (⌊x⌋₊%8)-1 ∧ block true (⌊x⌋₊%8)-1≤1 at e
  have eq : block true (⌊x⌋₊%8)=block true ⌊x⌋₊ := by simp [block]
  rw [eq] at e
  apply abs_le.mpr
  unfold oddSlope
  exact_mod_cast e

theorem oddSlope_intervalIntegrable {a b : ℝ} (hab : a≤b) :
    IntervalIntegrable oddSlope volume a b := by
  have hm : Measurable oddSlope := (measurable_of_countable
    (fun n : ℕ => (block true n : ℝ)-1)).comp measurable_id.nat_floor
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => oddSlope_bound y)

private theorem one_interval (k : ℕ) {x : ℝ} (hl : (k:ℝ)≤x) (hu : x≤k+1) :
    (∫ y in (k:ℝ)..x, oddSlope y)=(x-k)*((block true k:ℝ)-1) := by
  calc
    _ = ∫ _y in (k:ℝ)..x, ((block true k:ℝ)-1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hl
      intro y hy
      have lower := Nat.le_floor hy.1.le
      have upper : ⌊y⌋₊<k+1 := (Nat.floor_lt (by linarith [hy.1,Nat.cast_nonneg (α:=ℝ) k])).mpr
        (by exact_mod_cast hy.2.trans_le hu)
      simp only [oddSlope,show ⌊y⌋₊=k by omega]
    _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]

private theorem endpoints (k : ℕ) (hk : 3≤k) : oddSecond k=(vertex k : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [oddSecond,vertex]
  | succ k hk ih =>
    have hk' : (3:ℝ)≤k := by exact_mod_cast hk
    have hstep := one_interval k (x:=(k:ℝ)+1) (by linarith) le_rfl
    have eq := intervalIntegral.integral_add_adjacent_intervals
      (oddSlope_intervalIntegrable hk') (oddSlope_intervalIntegrable (by linarith : (k:ℝ)≤k+1))
    change (∫ y in (3:ℝ)..(k:ℝ), oddSlope y)=(vertex k:ℝ) at ih
    rw [ih,hstep] at eq
    simp only [oddSecond,Nat.cast_add,Nat.cast_one,vertex_step,Int.cast_sub,Int.cast_add,Int.cast_one]
    linarith

theorem oddSecond_bounds (x : ℝ) (hx : 3≤x) : 0≤oddSecond x ∧ oddSecond x≤2 := by
  let k := ⌊x⌋₊
  have hk : 3≤k := Nat.le_floor hx
  have lower : (k:ℝ)≤x := Nat.floor_le (by linarith)
  have upper : x≤(k:ℝ)+1 := (Nat.lt_floor_add_one x).le
  have k3 : (3:ℝ)≤k := by exact_mod_cast hk
  have eq := intervalIntegral.integral_add_adjacent_intervals
    (oddSlope_intervalIntegrable k3) (oddSlope_intervalIntegrable lower)
  change oddSecond k + _ = oddSecond x at eq
  rw [endpoints k hk,one_interval k lower upper] at eq
  have vs : (vertex (k+1):ℝ)=(vertex k:ℝ)+(block true k:ℝ)-1 := by exact_mod_cast vertex_step k
  have conv : oddSecond x = (1-(x-k))*(vertex k:ℝ)+(x-k)*(vertex (k+1):ℝ) := by
    rw [←eq,vs]; ring
  have t0 := sub_nonneg.mpr lower
  have t1 : 0≤1-(x-k) := by linarith
  rw [conv]
  refine ⟨add_nonneg (mul_nonneg t1 (vertex_bounds k).1) (mul_nonneg t0 (vertex_bounds (k+1)).1),?_⟩
  calc
    _ ≤ (1-(x-k))*2+(x-k)*2 := add_le_add (mul_le_mul_of_nonneg_left (vertex_bounds k).2 t1)
      (mul_le_mul_of_nonneg_left (vertex_bounds (k+1)).2 t0)
    _ = _ := by ring

theorem oddSecond_nonnegative (x : ℝ) (hx : 3≤x) : 0≤oddSecond x := (oddSecond_bounds x hx).1

theorem oddSecond_le (x : ℝ) (hx : 3≤x) : oddSecond x≤min 2 (x-3) := by
  apply le_min (oddSecond_bounds x hx).2
  have h := intervalIntegral.integral_mono_on hx (oddSlope_intervalIntegrable hx)
    (intervalIntegrable_const (c:=(1:ℝ))) (fun y _ => (abs_le.mp (oddSlope_bound y)).2)
  simpa only [oddSecond,intervalIntegral.integral_const,smul_eq_mul,mul_one] using h

end BMORModEight
end
end

section
noncomputable section
namespace BMORModEight
open MeasureTheory Set

private def ramp (a x : ℝ) := x^(-3/2:ℝ)-a*x^(-5/2:ℝ)

private theorem ramp_eq (a : ℝ) {x : ℝ} (hx : 0<x) :
    ramp a x = (x-a)*x^(-5/2:ℝ) := by
  unfold ramp
  rw [show (-3/2:ℝ)=1+(-5/2) by ring, Real.rpow_add hx,Real.rpow_one]
  ring

private theorem ramp_integrable (a : ℝ) {b : ℝ} (hb : 0<b) :
    IntegrableOn (ramp a) (Ioi b) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ)< -1) hb).sub
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-5/2:ℝ)< -1) hb).const_mul a)

private theorem ramp_integral (a : ℝ) (ha : 0<a) :
    (∫ x in Ioi a, ramp a x) = (4/3)/Real.sqrt a := by
  unfold ramp
  rw [integral_sub (integrableOn_Ioi_rpow_of_lt (by norm_num) ha)
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) ha).const_mul a),integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) ha, integral_Ioi_rpow_of_lt (by norm_num) ha]
  rw [show (-3/2+1:ℝ)=-(1/2) by ring,show (-5/2+1:ℝ)=-(1/2)+(-1) by ring,
    Real.rpow_add ha,Real.rpow_neg_one, Real.rpow_neg ha.le,←Real.sqrt_eq_rpow]
  field_simp [ha.ne', (Real.sqrt_pos.mpr ha).ne']
  ring

private def envelope (x : ℝ) := ramp 3 x-(Ioi (5:ℝ)).indicator (ramp 5) x

private theorem envelope_integrable : IntegrableOn envelope (Ioi (3:ℝ)) :=
  (ramp_integrable 3 (by norm_num : (0:ℝ)<3)).sub
    ((ramp_integrable 5 (by norm_num : (0:ℝ)<3)).indicator measurableSet_Ioi)

private theorem envelope_eq {x : ℝ} (hx : 3<x) : envelope x = min 2 (x-3)*x^(-5/2:ℝ) := by
  have hp : 0<x := by linarith
  by_cases h : 5<x
  · simp only [envelope,Set.indicator_of_mem (show x∈Ioi (5:ℝ) from h),
      min_eq_left (by linarith : 2≤x-3),ramp_eq _ hp]
    ring
  · simp only [envelope,Set.indicator_of_notMem (show x∉Ioi (5:ℝ) from h),
      min_eq_right (by linarith : x-3≤2),sub_zero,ramp_eq _ hp]

private theorem envelope_mass : (∫ x in Ioi (3:ℝ), envelope x) < 7/40 := by
  rw [show envelope = fun x => ramp 3 x-(Ioi (5:ℝ)).indicator (ramp 5) x by rfl]
  rw [integral_sub (ramp_integrable 3 (by norm_num : (0:ℝ)<3))
      ((ramp_integrable 5 (by norm_num : (0:ℝ)<3)).indicator measurableSet_Ioi),
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (show Ioi (5:ℝ) ⊆ Ioi 3 from Ioi_subset_Ioi (by norm_num)),
    ramp_integral 3 (by norm_num),ramp_integral 5 (by norm_num)]
  have hs3 : (1732/1000:ℝ)≤Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hs5 : Real.sqrt 5≤(2237/1000:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
  have h1 : (4/3:ℝ)/Real.sqrt 3 < 77/100 := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  have h2 : (595/1000:ℝ)< (4/3)/Real.sqrt 5 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  linarith

private theorem prod_bound (s : ℂ) (u C : ℝ) (hs : 0≤s.re) (hu : s.re≤u)
    (ht : |s.im|≤2) (hC : 0≤C) (hnum : (u^2+4)*((u+1)^2+4)≤C^2) :
    ‖s‖*‖s+1‖≤C := by
  have im : s.im^2≤2^2 := sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2
  have re : s.re^2≤u^2 := sq_le_sq' (by linarith) hu
  have re1 : (s.re+1)^2≤(u+1)^2 := sq_le_sq' (by linarith) (by linarith)
  have a : ‖s‖^2 ≤ u^2+4 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith
  have a1 : ‖s+1‖^2 ≤ (u+1)^2+4 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,add_zero]
    nlinarith
  have both := (mul_le_mul a a1 (sq_nonneg _) (by positivity)).trans hnum
  rw [←mul_pow] at both
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC).mp both

private theorem third_root_decay {x : ℝ} (hx : 3≤x) : x^(-(1/6):ℝ)≤5/6 := by
  have hp : 0<x := by linarith
  have p : 6/5 ≤ x^(1/6:ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) hp.le (by norm_num : (0:ℝ)<6)).mpr
    norm_num
    linarith
  rw [Real.rpow_neg hp.le,show (5/6:ℝ)=(6/5:ℝ)⁻¹ by norm_num]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hp _) (by norm_num : (0:ℝ)<6/5)).mpr p

private theorem integral_bound {s : ℂ} (B : ℝ → ℝ) (hB : ∀ x, 3<x → 0≤B x ∧ B x≤min 2 (x-3))
    (w : ℝ) (hw : 0<w) (weight : ∀ x, 3<x → x^(1/2-s.re)≤w) :
    ‖∫ x in Ioi (3:ℝ), (B x:ℂ)*(x:ℂ)^(-s-2)‖ < w*(7/40) := by
  have hi := envelope_integrable.const_mul w
  have bd : ‖∫ x in Ioi (3:ℝ), (B x:ℂ)*(x:ℂ)^(-s-2)‖ ≤
      ∫ x in Ioi (3:ℝ), w*envelope x := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp : 0<x := by linarith [show 3<x from hx]
    obtain ⟨b0,bu⟩ := hB x hx
    rw [envelope_eq hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg b0,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.sub_re,Complex.neg_re,show (2:ℂ).re=2 by norm_num]
    rw [show -s.re-2=(1/2-s.re)+(-5/2) by ring,Real.rpow_add hp,←mul_assoc,←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
    rw [mul_comm (B x) _]
    exact mul_le_mul (weight x hx) bu b0 hw.le
  rw [integral_const_mul] at bd
  exact bd.trans_lt (mul_lt_mul_of_pos_left envelope_mass hw)

theorem odd_norm_lower_of_integral {s z : ℂ} (hs : 1/2≤s.re) (hu : s.re≤1) (ht : |s.im|≤2)
    (B : ℝ→ℝ) (hB : ∀ x, 3<x → 0≤B x ∧ B x≤min 2 (x-3))
    (hz : z-1 = s*(s+1)*(∫ x in Ioi (3:ℝ), (B x:ℂ)*(x:ℂ)^(-s-2))) :
    3/80 < ‖z‖ := by
  have hsn : 0<s.re := by linarith
  have hsp : 0<‖s‖*‖s+1‖ := by
    apply mul_pos (norm_pos_iff.mpr (fun e => by simp [e] at hsn))
    apply norm_pos_iff.mpr
    intro e
    have := congrArg Complex.re e
    simp at this
    linarith
  have goal : ‖z-1‖ < 77/80 := by
    rw [hz,norm_mul,norm_mul]
    by_cases h : s.re≤2/3
    · have A := prod_bound s (2/3) (11/2) hsn.le h ht (by norm_num) (by norm_num)
      have B' := integral_bound (s:=s) B hB 1 (by norm_num) (fun x hx =>
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith))
      have q := (mul_lt_mul_of_pos_left B' hsp).trans_le (mul_le_mul_of_nonneg_right A (by norm_num))
      nlinarith
    · have A := prod_bound s 1 (13/2) hsn.le hu ht (by norm_num) (by norm_num)
      have B' := integral_bound (s:=s) B hB (5/6) (by norm_num) (fun x hx =>
        (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤x)
          (by linarith : 1/2-s.re≤ -(1/6))).trans (third_root_decay hx.le))
      have q := (mul_lt_mul_of_pos_left B' hsp).trans_le (mul_le_mul_of_nonneg_right A (by norm_num))
      nlinarith
  have triangle := norm_sub_le z (z-1)
  rw [sub_sub_cancel,norm_one] at triangle
  linarith

end BMORModEight
end
end

section
namespace BMORModEight
open Complex DirichletCharacter MeasureTheory Set Filter
noncomputable section

theorem odd_L_sub_one {s : ℂ} (hs : 0<s.re) :
    LFunction (character true) s - 1 =
      s*(s+1)*∫ x in Ioi (3:ℝ), (oddSecond x:ℂ)*(x:ℂ)^(-s-2) := by
  let a : ℝ → ℂ := fun x => (oddSlope x:ℂ)
  let w : ℝ → ℂ := fun x => (x:ℂ)^(-s-1)
  have ham : Measurable a := by
    exact Complex.continuous_ofReal.measurable.comp
      ((measurable_of_countable (fun n : ℕ => (block true n:ℝ)-1)).comp measurable_id.nat_floor)
  have hwm : Measurable w := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    exact (continuousAt_ofReal_cpow_const x _ (.inr hx)).continuousWithinAt
  have hab (x : ℝ) : ‖a x‖≤1 := by
    simpa only [a,Complex.norm_real,Real.norm_eq_abs] using oddSlope_bound x
  have hp : (-s-1).re < -1 := by simp; linarith
  have hwi : IntegrableOn w (Ioi 1) := integrableOn_Ioi_cpow_of_lt hp zero_lt_one
  have hwa : IntegrableOn (fun x => w x*a x) (Ioi 1) := by
    apply hwi.norm.mono' (hwm.mul ham).aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    change ‖w x * a x‖ ≤ ‖w x‖
    simpa only [norm_mul,mul_one] using
      (mul_le_mul_of_nonneg_left (hab x) (norm_nonneg (w x)))
  have initial : LFunction (character true) s =
      s*((∫ x in Ioi (1:ℝ), w x*a x)+(∫ x in Ioi (1:ℝ), w x)) := by
    rw [LFunction_eq_integral true hs,←integral_add hwa hwi]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    change (x:ℂ)^(-s-1)*(block true ⌊x⌋₊:ℂ) =
      (x:ℂ)^(-s-1)*((oddSlope x:ℝ):ℂ)+(x:ℂ)^(-s-1)
    simp only [oddSlope,Complex.ofReal_sub,Complex.ofReal_intCast,Complex.ofReal_one]
    ring
  have constant : s*(∫ x in Ioi (1:ℝ), w x)=1 := by
    change s*(∫ x : ℝ in Ioi 1, (x:ℂ)^(-s-1))=1
    rw [integral_Ioi_cpow_of_lt hp zero_lt_one,show -s-1+1 = -s by ring]
    have hn : s ≠ 0 := fun e => by simp [e] at hs
    simp [hn]
  have gap : (∫ x in Ioc (1:ℝ) 3, w x*a x)=0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    calc
      _ = ∫ _x : ℝ in Ioo 1 3, (0:ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        have lo : 1≤⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.1.le)
        have hi : ⌊x⌋₊<3 := (Nat.floor_lt (by linarith [hx.1] : 0≤x)).mpr (by exact_mod_cast hx.2)
        have hm : ⌊x⌋₊%8=1 ∨ ⌊x⌋₊%8=2 := by omega
        simp [a,oddSlope,block,hm]
      _ = _ := by simp
  have split := intervalIntegral.integral_interval_add_Ioi hwa
    (hwa.mono_set (Ioi_subset_Ioi (by norm_num : (1:ℝ)≤3)))
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤3),gap,zero_add] at split
  have main := abel_integral (a:=a) (by norm_num : (0:ℝ)<3) hs ham 1 zero_le_one
    (fun x _ => hab x)
  have swap : (∫ x in Ioi (3:ℝ), (x:ℂ)^(-s-2)*(∫ u in (3:ℝ)..x, a u)) =
      ∫ x in Ioi (3:ℝ), (oddSecond x:ℂ)*(x:ℂ)^(-s-2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    change _ * (∫ u in (3:ℝ)..x, (oddSlope u:ℂ)) = _
    rw [intervalIntegral.integral_ofReal]
    exact mul_comm _ _
  rw [swap] at main
  change (∫ x : ℝ in Ioi 3, w x*a x) = _ at main
  rw [initial,mul_add,constant,add_sub_cancel_right,←split,main,mul_assoc]

theorem odd_height_two {s : ℂ} (hs : 1/2≤s.re) (hu : s.re≤1) (ht : |s.im|≤2) :
    3/80 < ‖LFunction (character true) s‖ :=
  odd_norm_lower_of_integral hs hu ht oddSecond (fun x hx => ⟨oddSecond_nonnegative x hx.le,oddSecond_le x hx.le⟩)
    (odd_L_sub_one (by linarith))

end
end BMORModEight
end

section
namespace BMORModEight
open Complex DirichletCharacter Set

theorem character_self_inverse (odd : Bool) : (character odd)⁻¹=character odd := by
  apply MulChar.IsQuadratic.inv
  have h : (intChar odd).IsQuadratic := by
    cases odd
    · exact ZMod.isQuadratic_χ₈
    · exact ZMod.isQuadratic_χ₈'
  intro k
  rw [char_apply]
  rcases h k with e|e|e <;> simp [e]

def lowZeros (odd : Bool) (T : ℝ) : Set ℂ :=
  {s | 0<s.re ∧ s.re<1 ∧ |s.im|≤T ∧ LFunction (character odd) s=0}

theorem lowZeros_empty_of_half_band (odd : Bool) {T : ℝ}
    (H : ∀ s : ℂ, 1/2≤s.re → s.re<1 → |s.im|≤T → LFunction (character odd) s≠0) :
    lowZeros odd T=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro s ⟨hs,hu,ht,hz⟩
  by_cases h : 1/2≤s.re
  · exact H s h hu ht hz
  · apply BMORModThree.reflect_nonvanishing _ (char_primitive odd) hs hu _ hz
    rw [character_self_inverse]
    apply H
    · simp only [sub_re,one_re]; linarith
    · simp only [sub_re,one_re]; linarith
    · simpa only [sub_im,one_im,zero_sub,abs_neg] using ht

end BMORModEight
end

section
namespace BMORModEight
open Complex DirichletCharacter Set

theorem odd_low_zeros_empty : lowZeros true 2 = ∅ := by
  apply lowZeros_empty_of_half_band
  intro s hs hu ht
  exact norm_pos_iff.mp (lt_trans (by norm_num) (odd_height_two hs hu.le ht))

theorem odd_low_zero_count : Nat.card (lowZeros true 2) = 0 := by
  rw [odd_low_zeros_empty]
  simp

theorem odd_low_zero_weighted_sum (multiplicity : ℂ → ℕ) :
    (∑ᶠ z : lowZeros true 2, (multiplicity z : ℝ) /
      Real.sqrt ((z : ℂ).im ^ 2 + 1/4)) = 0 := by
  have : IsEmpty (lowZeros true 2) :=
    ⟨fun z => (Set.eq_empty_iff_forall_notMem.mp odd_low_zeros_empty) z.val z.property⟩
  exact finsum_of_isEmpty _

end BMORModEight
end

section
namespace BMORModEight
open Complex Real Set

private noncomputable def loss (t k : ℝ) := 1-Real.cos (t*Real.log k)

private theorem loss_nonneg (t k : ℝ) : 0≤loss t k :=
  sub_nonneg.mpr (Real.cos_le_one _)

private theorem loss_bound (k c : ℝ) (hk : 1≤k) (hk' : k≤7) (hc : 0≤c)
    (hr : c*Real.log 7≤Real.log k) {t : ℝ} (ht : |t|≤2) :
    c^2*loss t 7 ≤ loss t k := by
  let R := Real.log k/Real.log 7
  let u := |t| * Real.log 7/2
  have l7 : 0<Real.log 7 := Real.log_pos (by norm_num)
  have ru : c≤R := (le_div_iff₀ l7).mpr hr
  have r0 : 0≤R := hc.trans ru
  have r1 : R≤1 := (div_le_one l7).mpr (Real.log_le_log (by linarith) hk')
  have h7 : Real.log 7≤2 := by
    have h' : 7 < Real.exp 2 := by
      rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
      nlinarith [Real.exp_one_gt_d9,Real.exp_pos 1]
    exact ((Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<7)).mpr h').le
  have u0 : 0≤u := by dsimp [u]; positivity
  have uπ : u≤Real.pi := by
    dsimp [u]
    linarith [mul_le_mul_of_nonneg_right ht l7.le, Real.two_le_pi]
  have hs := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show u∈Icc 0 Real.pi from ⟨u0,uπ⟩) (by linarith : 0≤1-R) r0 (by ring)
  simp only [smul_eq_mul,Real.sin_zero,mul_zero,zero_add] at hs
  have aux := (mul_le_mul_of_nonneg_right ru (Real.sin_nonneg_of_nonneg_of_le_pi u0 uπ)).trans hs
  have sq := mul_self_le_mul_self (mul_nonneg hc (Real.sin_nonneg_of_nonneg_of_le_pi u0 uπ)) aux
  have uv : 2*(R*u)=|t| * Real.log k := by dsimp [R,u]; field_simp
  have uz : 2*u=|t| * Real.log 7 := by dsimp [u]; ring
  have form (b : ℝ) : loss t b = 1-Real.cos (|t| * Real.log b) := by
    rcases le_or_gt 0 t with h|h
    · simp [loss,abs_of_nonneg h]
    · simp [loss,abs_of_neg h,neg_mul]
  rw [form 7,form k,←uv,←uz,Real.cos_two_mul_eq_one_sub,Real.cos_two_mul_eq_one_sub]
  nlinarith only [sq]

private theorem weights (σ : ℝ) (hσ : 1/2≤σ) :
    (3/2:ℝ)*7^(-σ) ≤ 3^(-σ) := by
  have h : (3/2:ℝ) ≤ (7/3:ℝ)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤7/3), Real.sqrt_nonneg (7/3:ℝ)]
  have hh := h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤7/3) hσ)
  rw [Real.div_rpow (by norm_num) (by norm_num)] at hh
  have p : 0<(3:ℝ)^σ := Real.rpow_pos_of_pos (by norm_num) _
  have q : 0<(7:ℝ)^σ := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤7),Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
  rw [le_div_iff₀ p] at hh
  field_simp
  linarith

private theorem cos_comparison {σ t : ℝ} (hs : 1/2≤σ) (ht : |t|≤2) :
    (7:ℝ)^(-σ)*loss t 7 ≤ (3:ℝ)^(-σ)*loss t 3+(5:ℝ)^(-σ)*loss t 5 := by
  have h3 : (1/2:ℝ)*Real.log 7 ≤ Real.log 3 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<7) (by norm_num : (7:ℝ)≤3^2)
    rw [Real.log_pow] at h; norm_num at h; linarith
  have h5 : (4/5:ℝ)*Real.log 7 ≤ Real.log 5 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<7^4) (by norm_num : (7:ℝ)^4≤5^5)
    rw [Real.log_pow,Real.log_pow] at h; norm_num at h; linarith
  have a := loss_bound 3 (1/2) (by norm_num) (by norm_num) (by norm_num) h3 ht
  have b := loss_bound 5 (4/5) (by norm_num) (by norm_num) (by norm_num) h5 ht
  have c := weights σ hs
  have d := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<5) (by norm_num : (5:ℝ)≤7) (by linarith : -σ≤0)
  have a' := mul_le_mul c a (mul_nonneg (sq_nonneg _) (loss_nonneg _ _)) (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) (-σ))
  have b' := mul_le_mul d b (mul_nonneg (sq_nonneg _) (loss_nonneg _ _)) (Real.rpow_nonneg (by norm_num : (0:ℝ)≤5) (-σ))
  nlinarith only [a',b',mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤7) (-σ)) (loss_nonneg t 7)]

private theorem anchor (σ : ℝ) (hs : 1/2≤σ) :
    1/3 < 1-(3:ℝ)^(-σ)-(5:ℝ)^(-σ)+(7:ℝ)^(-σ) := by
  let A := fun k : ℝ => k^(-(1/2):ℝ)
  let X := fun k : ℝ => k^(1/2-σ)
  have split {k : ℝ} (hk : 0<k) : k^(-σ)=A k*X k := by
    rw [←Real.rpow_add hk]; congr 1; ring
  have a {k : ℝ} (hk : 1≤k) : X k≤1 := Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith)
  have h3 : A 7≤A 3 := Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
  have h5 : A 7≤A 5 := Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
  have hab : X 3*X 5≤X 7 := by
    dsimp [X]; rw [←Real.mul_rpow (by norm_num) (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by linarith)
  have up (k b : ℝ) (hk : 0<k) (hb : 0<b) (he : 1<b^2*k) : A k<b := by
    dsimp [A]; rw [Real.rpow_neg hk.le,←Real.sqrt_eq_rpow]
    apply (inv_lt_comm₀ (Real.sqrt_pos.mpr hk) hb).mpr
    rw [inv_eq_one_div,div_lt_iff₀ hb]
    by_contra! bad
    have sq := mul_self_le_mul_self (mul_nonneg (Real.sqrt_nonneg k) hb.le) bad
    nlinarith [Real.sq_sqrt hk.le,show (Real.sqrt k*b)*(Real.sqrt k*b)=k*b^2 by
      rw [show (Real.sqrt k*b)*(Real.sqrt k*b)=(Real.sqrt k)^2*b^2 by ring,Real.sq_sqrt hk.le]]
  have lo : 3/8<A 7 := by
    dsimp [A]; rw [Real.rpow_neg (by norm_num : (0:ℝ)≤7),←Real.sqrt_eq_rpow]
    rw [inv_eq_one_div,lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤7),Real.sqrt_nonneg (7:ℝ)]
  have hA : 0≤A 7 := Real.rpow_nonneg (by norm_num) _
  rw [split (by norm_num : (0:ℝ)<3),split (by norm_num : (0:ℝ)<5),split (by norm_num : (0:ℝ)<7)]
  have ax := sub_nonneg.mpr (a (by norm_num : (1:ℝ)≤3))
  have bx := sub_nonneg.mpr (a (by norm_num : (1:ℝ)≤5))
  nlinarith only [up 3 (7/12) (by norm_num) (by norm_num) (by norm_num),
    up 5 (9/20) (by norm_num) (by norm_num) (by norm_num),lo,
    mul_nonneg (sub_nonneg.mpr h3) ax, mul_nonneg (sub_nonneg.mpr h5) bx,
    mul_nonneg hA (mul_nonneg ax bx),mul_le_mul_of_nonneg_left hab hA]

private theorem term_re (k : ℝ) (hk : 0<k) (s : ℂ) :
    ((k:ℂ)^(-s)).re = k^(-s.re)*Real.cos (s.im*Real.log k) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne'),←Complex.ofReal_log hk.le,
    Complex.exp_re,Real.rpow_def_of_pos hk]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,zero_mul,sub_zero,mul_neg,Real.cos_neg]
  ring_nf

theorem even_head_lower {s : ℂ} (hs : 1/2≤s.re) (ht : |s.im|≤2) :
    1/3 < (1-(3:ℂ)^(-s)-(5:ℂ)^(-s)+(7:ℂ)^(-s)).re := by
  have h := cos_comparison hs ht
  have b := anchor s.re hs
  dsimp [loss] at h
  simp only [Complex.add_re,Complex.sub_re,Complex.one_re]
  rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,term_re _ (by norm_num) s,
    show (5:ℂ)=((5:ℝ):ℂ) by norm_num,term_re _ (by norm_num) s,
    show (7:ℂ)=((7:ℝ):ℂ) by norm_num,term_re _ (by norm_num) s]
  linarith only [h,b]
end BMORModEight
end

section
noncomputable section

open MeasureTheory Set Complex Filter
open scoped Topology
open BMORModThree.Mellin

namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

/-- Periodic extension to the full real line of the ordinary partial sums. -/
def step (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  charPartialSum χ ((⌊x⌋ : ZMod q).val)

theorem step_periodic (χ : DirichletCharacter ℂ q) : Function.Periodic (step χ) (q : ℝ) := by
  intro x
  simp [step, Int.floor_add_natCast]

theorem step_eq (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) {x : ℝ} (hx : 0 ≤ x) :
    step χ x = charPartialSum χ ⌊x⌋₊ := by
  rw [step, ← Int.natCast_floor_eq_floor hx, Int.cast_natCast, ZMod.val_natCast]
  simpa [integerRemainder, charMean_eq, hn] using (integerRemainder_periodic χ).map_mod_nat ⌊x⌋₊

theorem norm_step (χ : DirichletCharacter ℂ q) (x : ℝ) : ‖step χ x‖ ≤ (q : ℝ) := by
  apply (norm_charPartialSum_le χ _).trans
  exact_mod_cast (ZMod.val_lt (⌊x⌋ : ZMod q)).le

theorem measurable_step (χ : DirichletCharacter ℂ q) : Measurable (step χ) :=
  (measurable_of_countable (fun z : ℤ => charPartialSum χ ((z : ZMod q).val))).comp
    measurable_id.floor

theorem step_intervalIntegrable (χ : DirichletCharacter ℂ q) (a b : ℝ) :
    IntervalIntegrable (step χ) volume a b :=
  (intervalIntegrable_const (c := (q : ℝ))).mono_fun' (measurable_step χ).aestronglyMeasurable
    (Eventually.of_forall (norm_step χ))

/-- Average of the partial sums on one period. -/
def mean (χ : DirichletCharacter ℂ q) : ℂ := (∫ x in 0..(q : ℝ), step χ x) / (q : ℂ)

theorem norm_mean (χ : DirichletCharacter ℂ q) : ‖mean χ‖ ≤ (q : ℝ) := by
  rw [mean, norm_div, Complex.norm_natCast, div_le_iff₀ (by exact_mod_cast q.pos_of_neZero)]
  simpa [abs_of_nonneg] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (q:ℝ)) (fun x _ => norm_step χ x)

def centered (χ : DirichletCharacter ℂ q) (x : ℝ) := step χ x - mean χ
def primitive (χ : DirichletCharacter ℂ q) (N x : ℝ) := ∫ y in N..x, centered χ y

theorem centered_periodic (χ : DirichletCharacter ℂ q) :
    Function.Periodic (centered χ) (q : ℝ) := fun x => by simp [centered, step_periodic χ x]

theorem centered_intervalIntegrable (χ : DirichletCharacter ℂ q) (a b : ℝ) :
    IntervalIntegrable (centered χ) volume a b :=
  (step_intervalIntegrable χ a b).sub intervalIntegrable_const

theorem centered_bound (χ : DirichletCharacter ℂ q) (x : ℝ) : ‖centered χ x‖ ≤ 2 * q :=
  (norm_sub_le _ _).trans (by linarith [norm_step χ x, norm_mean χ])

theorem integral_centered_period (χ : DirichletCharacter ℂ q) (a : ℝ) :
    (∫ x in a..a+(q:ℝ), centered χ x) = 0 := by
  rw [(centered_periodic χ).intervalIntegral_add_eq a 0, zero_add]
  simp only [centered, intervalIntegral.integral_sub (step_intervalIntegrable χ _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, Complex.real_smul, Complex.ofReal_natCast, mean]
  field_simp [NeZero.ne (q:ℂ)]; ring

theorem primitive_periodic (χ : DirichletCharacter ℂ q) (N : ℝ) :
    Function.Periodic (primitive χ N) (q : ℝ) := by
  intro x
  simp [primitive, (centered_periodic χ).intervalIntegral_add_eq_add N x
    (centered_intervalIntegrable χ), integral_centered_period]

/-- Uniform bound for the centered second primitive. It is valid for arbitrary
cutoffs, independently of the distance between the two endpoints. -/
theorem norm_primitive (χ : DirichletCharacter ℂ q) (N x : ℝ) :
    ‖primitive χ N x‖ ≤ 2 * (q : ℝ)^2 := by
  let Q := (q : ℝ)
  have hp : 0 < Q := by dsimp [Q]; exact_mod_cast q.pos_of_neZero
  let ε := Int.fract ((x-N)/Q)*Q
  have he : ε ∈ Ico 0 Q := Int.fract_div_mul_self_mem_Ico _ _ hp
  have hx : (N+ε) + ⌊(x-N)/Q⌋ • Q = x := by
    calc
      _ = N+(ε + ⌊(x-N)/Q⌋ • Q) := add_assoc ..
      _ = x := by rw [show ε + ⌊(x-N)/Q⌋ • Q = x-N from
                    Int.fract_div_mul_self_add_zsmul_eq _ _ hp.ne']; ring
  rw [← hx, (primitive_periodic χ N).zsmul ⌊(x-N)/Q⌋ (N+ε)]
  calc
    _ ≤ (2*Q)*|(N+ε)-N| := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y _ => centered_bound χ y)
    _ ≤ _ := by rw [add_sub_cancel_left, abs_of_nonneg he.1]; dsimp [Q] at *; nlinarith [mul_le_mul_of_nonneg_left he.2.le hp.le]

end BMORPeriodicTail

namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

/-- Exact one-period computation of the centering constant. -/
theorem mean_eq_finite (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) :
    mean χ = (∑ k ∈ Finset.range q, charPartialSum χ k) / (q : ℂ) := by
  have cell (k : ℕ) : (∫ x in (k : ℝ)..((k+1:ℕ):ℝ), step χ x) = charPartialSum χ k := by
    have hk : (k:ℝ) ≤ ((k+1:ℕ):ℝ) := by norm_num
    have hh : (∫ x in (k : ℝ)..((k+1:ℕ):ℝ), step χ x) =
        ∫ _x in (k : ℝ)..((k+1:ℕ):ℝ), charPartialSum χ k := by
      rw [intervalIntegral.integral_of_le hk, intervalIntegral.integral_of_le hk,
        ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      rw [step_eq χ hn (k.cast_nonneg.trans hx.1)]
      congr 1
      exact Nat.floor_eq_iff (k.cast_nonneg.trans hx.1) |>.2 ⟨hx.1, by exact_mod_cast hx.2⟩
    rw [hh, intervalIntegral.integral_const]
    simp
  unfold mean
  congr 1
  simpa only [Nat.cast_zero, cell] using
    (intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (n := q) (fun k _ => step_intervalIntegrable χ _ _)).symm

private def coeff (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ (n : ZMod q)

private theorem coeff_sum (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, coeff χ k) = charPartialSum χ n := by
  rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
  simp [coeff, charPartialSum]

/-- Dirichlet polynomial truncated after its Nth positive term. -/
def head (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) :=
  ∑ k ∈ Finset.range N, ((k+1:ℕ):ℂ) ^ (-s) * χ ((k+1:ℕ):ZMod q)

theorem head_eq (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    head χ N s = (N : ℂ)^(-s) * charPartialSum χ N +
      s * ∫ x in Set.Ioc (1:ℝ) N, (x:ℂ)^(-s-1) * step χ x := by
  let f : ℝ → ℂ := fun x => (x:ℂ)^(-s)
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hd : ∀ x ∈ Set.Icc (1:ℝ) N, DifferentiableAt ℝ f x := fun x hx =>
    (hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le hx.1).ne' (neg_ne_zero.mpr hs0)).differentiableAt
  have hi : IntegrableOn (deriv f) (Set.Icc (1:ℝ) N) :=
    (integrableOn_Ioi_deriv_ofReal_cpow (t := (1/2:ℝ)) (by norm_num) (s := -s) (by simpa)).mono_set
      (fun x hx => (by norm_num : (1/2:ℝ)<1).trans_le hx.1)
  have he := sum_mul_eq_sub_integral_mul₀' (coeff χ) (by simp [coeff]) N hd hi
  have hleft : head χ N s = ∑ k ∈ Finset.Icc 0 N, f k * coeff χ k := by
    rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
    simp [head, coeff, f]
  rw [hleft, he, coeff_sum]
  simp_rw [coeff_sum]
  have hfun : (∫ x in Set.Ioc (1:ℝ) N, deriv f x * charPartialSum χ ⌊x⌋₊) =
      ∫ x in Set.Ioc (1:ℝ) N, -s * ((x:ℂ)^(-s-1) * step χ x) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    have hx0 := zero_lt_one.trans hx.1
    simp [f, deriv_ofReal_cpow_const (-s) hx0.ne', step_eq χ hn hx0.le, mul_assoc]
  rw [hfun, integral_const_mul]
  simp [f]

end BMORPeriodicTail

namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

theorem integrable_weighted {r : ℂ} (hr : r.re < -1) {a : ℝ} (ha : 0 < a)
    {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hb : ∀ x, ‖g x‖ ≤ C) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^r * g x) (Ioi a) := by
  refine ((integrableOn_Ioi_rpow_of_lt hr ha).mul_const C).mono' ?_ ?_
  · have hc : ContinuousOn (fun x : ℝ => (x:ℂ)^r) (Ioi a) :=
      fun x hx => (continuousAt_ofReal_cpow_const x _ (Or.inr (ha.trans hx).ne')).continuousWithinAt
    exact (hc.aestronglyMeasurable measurableSet_Ioi).mul hg.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (ha.trans hx)]
    exact mul_le_mul_of_nonneg_left (hb x) (Real.rpow_nonneg (ha.trans hx).le _)

/-- Exact error after subtracting the cutoff phase and mean of the partial sum. -/
theorem L_sub_corrected_head (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s - head χ N s -
        (mean χ - charPartialSum χ N)*(N:ℂ)^(-s) =
      s * ∫ x in Ioi (N:ℝ), (x:ℂ)^(-s-1) * centered χ x := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans_le hNr
  have hr : (-s-1).re < -1 := by simp; linarith
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  let w := fun x : ℝ => (x:ℂ)^(-s-1)
  have hw1 := integrable_weighted hr zero_lt_one (measurable_step χ) (norm_step χ)
  have hwN := integrable_weighted hr hN0 (measurable_step χ) (norm_step χ)
  have hl : DirichletCharacter.LFunction χ s =
      s * ∫ x in Ioi (1:ℝ), w x * step χ x := by
    rw [LFunction_eq_remainderMellin χ hn hs, remainderMellin_eq_integral]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [w, charMean_eq, hn, step_eq χ hn (zero_lt_one.trans hx).le]
  have hsplit := intervalIntegral.integral_interval_add_Ioi hw1 hwN
  rw [intervalIntegral.integral_of_le hNr] at hsplit
  have hcent : IntegrableOn (fun x : ℝ => w x * centered χ x) (Ioi (N:ℝ)) :=
    integrable_weighted hr hN0 ((measurable_step χ).sub_const _) (centered_bound χ)
  have hmean : IntegrableOn (fun x : ℝ => w x * mean χ) (Ioi (N:ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt hr hN0).mul_const _
  have hadd : (∫ x in Ioi (N:ℝ), w x * step χ x) =
      (∫ x in Ioi (N:ℝ), w x * centered χ x) +
      ∫ x in Ioi (N:ℝ), w x * mean χ := by
    rw [← integral_add hcent hmean]
    congr 1; ext x; dsimp [centered]; ring
  have hval : s*(∫ x in Ioi (N:ℝ), w x * mean χ) = (mean χ)*(N:ℂ)^(-s) := by
    rw [integral_mul_const, show (∫ x in Ioi (N:ℝ), w x) = _ from integral_Ioi_cpow_of_lt hr hN0]
    simp only [sub_add_cancel, ofReal_natCast, neg_div_neg_eq]
    field_simp [hs0]
  rw [hl, head_eq χ hn N hs]
  change s * (∫ x in Ioi (1:ℝ), w x * step χ x) -
    ((N:ℂ)^(-s)*charPartialSum χ N+s*∫ x in Ioc (1:ℝ) N, w x * step χ x) -
    (mean χ-charPartialSum χ N)*(N:ℂ)^(-s) = _
  rw [← hsplit, hadd]
  linear_combination hval

end BMORPeriodicTail
end
end

section
noncomputable section
open MeasureTheory Set Complex
open BMORModThree.Mellin
namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

/-- Computable-in-principle cumulative sum of the centered staircase. -/
def knots (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, (charPartialSum χ k - mean χ)

private theorem integral_cell (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) {k : ℕ} {x : ℝ}
    (hk : (k:ℝ) ≤ x) (hx : x ≤ (k:ℝ)+1) :
    (∫ y in (k:ℝ)..x, centered χ y) = (x-(k:ℝ)) • (charPartialSum χ k - mean χ) := by
  rw [← intervalIntegral.integral_const]
  rw [intervalIntegral.integral_of_le hk, intervalIntegral.integral_of_le hk,
    ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  simp only [centered, step_eq χ hn (k.cast_nonneg.trans ht.1)]
  rw [(Nat.floor_eq_iff (k.cast_nonneg.trans ht.1)).2 ⟨ht.1, ht.2.trans_le hx⟩]

theorem primitive_nat (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) (n : ℕ) :
    primitive χ 0 n = knots χ n := by
  induction n with
  | zero => simp [primitive, knots]
  | succ n ih =>
    have h := intervalIntegral.integral_add_adjacent_intervals (centered_intervalIntegrable χ 0 (n:ℝ))
      (centered_intervalIntegrable χ (n:ℝ) ((n:ℝ)+1))
    rw [primitive, Nat.cast_succ, ← h,
      integral_cell χ hn (k := n) (by linarith) le_rfl, add_sub_cancel_left, one_smul]
    rw [← primitive, ih, knots, knots, Finset.sum_range_succ]

private theorem primitive_sub (χ : DirichletCharacter ℂ q) (a x : ℝ) :
    primitive χ a x = primitive χ 0 x - primitive χ 0 a := by
  unfold primitive
  rw [intervalIntegral.integral_interval_sub_left (centered_intervalIntegrable χ _ _)
    (centered_intervalIntegrable χ _ _)]

/-- The sharp radius can be certified entirely at the q+1 integer knots. -/
theorem norm_primitive_le_of_knots (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) (N : ℕ) {C : ℝ}
    (hC : ∀ k : ℕ, k ≤ q → ‖knots χ k - knots χ N‖ ≤ C) (x : ℝ) :
    ‖primitive χ N x‖ ≤ C := by
  let Q := (q : ℝ)
  have hq : 0<Q := by dsimp [Q]; exact_mod_cast q.pos_of_neZero
  let ε := Int.fract (x/Q)*Q
  have he : ε ∈ Ico 0 Q := Int.fract_div_mul_self_mem_Ico _ _ hq
  rw [← show ε+⌊x/Q⌋ • Q = x from Int.fract_div_mul_self_add_zsmul_eq _ _ hq.ne',
    (primitive_periodic χ N).zsmul ⌊x/Q⌋ ε]
  let k := ⌊ε⌋₊
  have hk : (k:ℝ) ≤ ε := Nat.floor_le he.1
  have hxk : ε < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkq : k<q := by exact_mod_cast (hk.trans_lt he.2 : (k:ℝ)<(q:ℝ))
  let t := ε-(k:ℝ)
  have ht : 0≤t := sub_nonneg.mpr hk
  have ht' : t≤1 := by dsimp [t]; linarith
  have hsum := intervalIntegral.integral_add_adjacent_intervals (centered_intervalIntegrable χ 0 (k:ℝ))
      (centered_intervalIntegrable χ (k:ℝ) ε)
  have hε : primitive χ 0 ε = knots χ k + t • (charPartialSum χ k - mean χ) := by
    rw [primitive, ← hsum, ← primitive, primitive_nat χ hn, integral_cell χ hn hk hxk.le]
  have hF : primitive χ N ε = (1-t) • (knots χ k-knots χ N) +
      t • (knots χ (k+1)-knots χ N) := by
    rw [primitive_sub, hε, primitive_nat χ hn, show knots χ (k+1) =
      knots χ k + (charPartialSum χ k-mean χ) by simp only [knots, Finset.sum_range_succ]]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [hF]
  calc
    _ ≤ ‖(1-t) • (knots χ k-knots χ N)‖ + ‖t • (knots χ (k+1)-knots χ N)‖ := norm_add_le _ _
    _ ≤ (1-t)*C+t*C := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht')]
      exact add_le_add (mul_le_mul_of_nonneg_left (hC k hkq.le) (sub_nonneg.mpr ht'))
        (mul_le_mul_of_nonneg_left (hC _ hkq) ht)
    _ = C := by ring

end BMORPeriodicTail
end
end

section
noncomputable section
open Complex MeasureTheory Set Filter
open BMORModThree.Mellin
namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

/-- Any pointwise bound for the actual primitive gives an explicit improper-integral bound. -/
theorem norm_weighted_primitive {s : ℂ} (hs : 0 < s.re) {N : ℝ} (hN : 0 < N)
    {g : ℝ → ℂ} {C : ℝ} (hb : ∀ x ∈ Ioi N, ‖g x‖ ≤ C) :
    ‖∫ x in Ioi N, (x:ℂ)^(-s-2) * g x‖ ≤ C * N^(-s.re-1)/(s.re+1) := by
  have he : -s.re-2 < -1 := by linarith
  refine (norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt he hN).const_mul C) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hN.trans hx)]
    have h : (-s-2).re = -s.re-2 := by simp
    rw [h, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hb x hx) (Real.rpow_nonneg (hN.trans hx).le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt he hN,
      show -s.re-2+1 = -(s.re+1) by ring, neg_div_neg_eq,
      show -(s.re+1) = -s.re-1 by ring]
    ring

/-- A low-strip specialization that retains the pointwise radius supplied by one period. -/
theorem low_strip_factor {s : ℂ} (hlo : 1/2 ≤ s.re) (hhi : s.re ≤ 1) (ht : |s.im| ≤ 2) :
    ‖s‖*‖s+1‖ ≤ (15/4)*(s.re+1) := by
  have ht' := abs_le.mp ht
  have him : s.im ^ 2 ≤ 4 := by nlinarith [(mul_nonneg (by linarith : 0 ≤ 2-s.im)
    (by linarith : 0 ≤ 2+s.im))]
  have hs1 : ‖s‖^2 ≤ 5 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg s.re, mul_nonneg (by linarith : 0 ≤ 1-s.re) (by linarith : 0 ≤ 1+s.re)]
  have hs2 : ‖s‖ ≤ 9/4 := by nlinarith [norm_nonneg s]
  have hs' : ‖s+1‖^2 = (s.re+1)^2+s.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hs3 : ‖s+1‖ ≤ (5/3)*(s.re+1) := by
    nlinarith [sq_nonneg (s.re-1/2), norm_nonneg (s+1),
      mul_nonneg (by linarith : 0 ≤ s.re-1/2) (by linarith : 0 ≤ s.re+5/2),
      sq_nonneg (‖s+1‖-(5/3)*(s.re+1))]
  calc
    _ ≤ (9/4)*((5/3)*(s.re+1)) := mul_le_mul hs2 hs3 (norm_nonneg _) (by norm_num)
    _ = _ := by ring

end BMORPeriodicTail
end
end

section
noncomputable section
open MeasureTheory Set Complex
open BMORModThree.Mellin
namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

/-- A finite expression for the corrected Dirichlet polynomial at the cutoff. -/
def corrected (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) :=
  head χ N s + (mean χ - charPartialSum χ N) * (N:ℂ)^(-s)

/-- Second Abel summation for the actual Dirichlet L-function. -/
theorem L_sub_corrected (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) {N : ℕ} (hN : 1≤N)
    {s : ℂ} (hs : 0<s.re) :
    DirichletCharacter.LFunction χ s - corrected χ N s =
      (s*(s+1)) * ∫ x in Ioi (N:ℝ), (x:ℂ)^(-s-2)*primitive χ N x := by
  unfold corrected
  rw [← sub_sub, L_sub_corrected_head χ hn hN hs]
  have hN0 : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  rw [BMORModEight.abel_integral (a := centered χ) hN0 hs ((measurable_step χ).sub_const (mean χ))
    (2*(q:ℝ)) (by positivity) (fun x _ => centered_bound χ x)]
  unfold primitive
  ring

/-- At any cutoff and any point in the open right half-plane the true remainder is
O(N^(-1-Re(s))). A supplied one-period radius may replace the uniform 2q². -/
theorem error_bound (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) {N : ℕ} (hN : 1≤N)
    {s : ℂ} (hs : 0<s.re) {C : ℝ} (hC : ∀ x ∈ Ioi (N:ℝ), ‖primitive χ N x‖ ≤ C) :
    ‖DirichletCharacter.LFunction χ s - corrected χ N s‖ ≤
      (‖s‖*‖s+1‖)*(C*(N:ℝ)^(-s.re-1)/(s.re+1)) := by
  rw [L_sub_corrected χ hn hN hs, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_weighted_primitive hs (by exact_mod_cast (by omega : 0<N)) hC)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Uniform error for every nonprincipal character through the height-two strip. -/
theorem height_two_uniform (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) {N : ℕ} (hN : 1≤N)
    {s : ℂ} (hlo : 1/2 ≤ s.re) (hhi : s.re ≤ 1) (ht : |s.im| ≤ 2) :
    ‖DirichletCharacter.LFunction χ s - corrected χ N s‖ ≤
      (15/2)*(q:ℝ)^2*(N:ℝ)^(-s.re-1) := by
  have hs : 0<s.re := by linarith
  have h := error_bound χ hn hN hs (fun x _ => norm_primitive χ N x)
  refine h.trans ((mul_le_mul_of_nonneg_right (low_strip_factor hlo hhi ht) (by positivity)).trans_eq ?_)
  field_simp [show s.re+1≠0 by linarith]
  ring

/-- Fully finite posterior certificate for avoiding zero on the height-two strip. -/
theorem ne_zero_of_knots (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) {N : ℕ} (hN : 1≤N)
    {s : ℂ} (hs : 0<s.re) {C : ℝ}
    (hC : ∀ k : ℕ, k≤q → ‖knots χ k - knots χ N‖ ≤ C)
    (hh : (‖s‖*‖s+1‖)*(C*(N:ℝ)^(-s.re-1)/(s.re+1)) < ‖corrected χ N s‖) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h
  have he := error_bound χ hn hN hs (fun x _ => norm_primitive_le_of_knots χ hn N hC x)
  simpa [h] using he.trans_lt hh

end BMORPeriodicTail
end
end

section
noncomputable section
namespace BMORModEight
open MeasureTheory Complex Set Finset BMORModThree.Mellin BMORPeriodicTail

private theorem even_mean : mean (character false) = 0 := by
  rw [mean_eq_finite _ (character_nonprincipal false)]
  simp_rw [partial_eq]
  rw [← Int.cast_sum]
  have h : ∑ k ∈ range 8, block false k = 0 := by decide +kernel
  simp [h]

private theorem knots_even (k : ℕ) :
    knots (character false) k = (∑ n ∈ range k, block false n : ℤ) := by
  simp [knots, partial_eq, even_mean]

private theorem even_radius (k : ℕ) (hk : k≤8) : ‖knots (character false) k - knots (character false) 9‖ ≤ 2 := by
  have hb : ∀ j : Fin 9, |(∑ n ∈ range j.val, block false n) - ∑ n ∈ range 9, block false n| ≤ 2 := by
    decide +kernel
  rw [knots_even, knots_even, ← Int.cast_sub, Complex.norm_intCast]
  exact_mod_cast hb ⟨k, by omega⟩

def evenPolynomial (s : ℂ) := 1-(3:ℂ)^(-s)-(5:ℂ)^(-s)+(7:ℂ)^(-s)

theorem even_corrected_nine (s : ℂ) :
    corrected (character false) 9 s = evenPolynomial s := by
  have hc (k : ℕ) (hk : k<10) : character false (k: ZMod 8) =
      (if k=1 ∨ k=7 ∨ k=9 then 1 else if k=3 ∨ k=5 then -1 else 0 : ℂ) := by
    have v : ∀ j : Fin 10, intChar false (j.val : ZMod 8) =
      (if j.val=1 ∨ j.val=7 ∨ j.val=9 then 1 else if j.val=3 ∨ j.val=5 then -1 else 0 : ℤ) := by decide +kernel
    rw [char_apply, v ⟨k,hk⟩]
    push_cast
    rfl
  have hb : block false 9 = 1 := by decide
  simp only [corrected, even_mean, partial_eq, hb, Int.cast_one, head, evenPolynomial,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  norm_num [hc, show character false 1 = 1 by simpa using hc 1 (by decide),
    show character false 2 = 0 by simpa using hc 2 (by decide),
    show character false 3 = -1 by simpa using hc 3 (by decide),
    show character false 4 = 0 by simpa using hc 4 (by decide),
    show character false 5 = -1 by simpa using hc 5 (by decide),
    show character false 6 = 0 by simpa using hc 6 (by decide),
    show character false 7 = 1 by simpa using hc 7 (by decide),
    show character false 8 = 0 by simpa using hc 8 (by decide),
    show character false 9 = 1 by simpa using hc 9 (by decide)]
  ring

/-- Quantitative approximation by the four-term polynomial throughout the height-two strip. -/
theorem even_polynomial_error {s : ℂ} (hlo : 1/2 ≤ s.re) (hhi : s.re≤1) (ht : |s.im| ≤ 2) :
    ‖DirichletCharacter.LFunction (character false) s - evenPolynomial s‖ ≤ 5/18 := by
  rw [← even_corrected_nine]
  have hs : 0<s.re := by linarith
  have h := error_bound (character false) (character_nonprincipal false) (N:=9) (by decide) hs
    (fun x _ => norm_primitive_le_of_knots _ (character_nonprincipal false) 9 even_radius x)
  have hp : (9:ℝ)^(-s.re-1) ≤ 1/27 := by
    calc
      _ ≤ (9:ℝ)^(-(3/2):ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1/27 := by rw [Real.rpow_neg (by norm_num)]; norm_num [show (3/2:ℝ)=(1/2:ℝ)*3 by ring,
                     Real.rpow_mul (by norm_num : (0:ℝ)≤9), ← Real.sqrt_eq_rpow]
  norm_num only [Nat.cast_ofNat] at h
  refine h.trans ((mul_le_mul_of_nonneg_right (low_strip_factor hlo hhi ht) (by positivity)).trans ?_)
  calc
    _ = (15/2)*(9:ℝ)^(-s.re-1) := by field_simp [show s.re+1≠0 by linarith]; ring
    _ ≤ 5/18 := by linarith

end BMORModEight
end
end

section
namespace BMORModEight
open DirichletCharacter Finset

noncomputable def fromFour : DirichletCharacter ℂ 8 :=
  changeLevel (show 4∣8 by decide) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))

private def signature (χ : DirichletCharacter ℂ 8) : ℂ × ℂ := (χ 3,χ 5)

private theorem sig_one : signature 1=(1,1) := by
  have h3 : IsUnit (3:ZMod 8) := (ZMod.isUnit_iff_coprime 3 8).mpr (by decide)
  have h5 : IsUnit (5:ZMod 8) := (ZMod.isUnit_iff_coprime 5 8).mpr (by decide)
  exact Prod.ext (MulChar.one_apply h3) (MulChar.one_apply h5)

private theorem sig_fromFour : signature fromFour=(-1,1) := by
  let ψ := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  apply Prod.ext
  · have h := changeLevel_eq_cast_of_dvd ψ (show 4∣8 by decide)
      (ZMod.unitOfCoprime 3 (show Nat.Coprime 3 8 by decide))
    rw [ZMod.coe_unitOfCoprime,ZMod.cast_natCast (show 4∣8 by decide)] at h
    change changeLevel (show 4∣8 by decide) ψ 3 = -1
    refine h.trans ?_
    change ((ZMod.χ₄ 3 : ℤ):ℂ) = -1
    norm_num [show ZMod.χ₄ 3= -1 by decide]
  · exact lifted_at_five _

private theorem sig_even : signature (character false)=(-1,-1) := by
  apply Prod.ext _ (char_five _)
  change character false 3 = -1
  rw [char_apply,show intChar false 3= -1 by decide]; norm_num

private theorem sig_odd : signature (character true)=(1,-1) := by
  apply Prod.ext _ (char_five _)
  change character true 3 = 1
  rw [char_apply,show intChar true 3=1 by decide]; norm_num

theorem all_characters (χ : DirichletCharacter ℂ 8) :
    χ=1 ∨ χ=fromFour ∨ χ=character false ∨ χ=character true := by
  classical
  have ab : (1 : DirichletCharacter ℂ 8) ≠ fromFour := by
    intro h; have eq := congrArg signature h; norm_num [sig_one,sig_fromFour] at eq
  have ac : (1 : DirichletCharacter ℂ 8) ≠ character false := (character_nonprincipal _).symm
  have ad : (1 : DirichletCharacter ℂ 8) ≠ character true := (character_nonprincipal _).symm
  have bc : fromFour ≠ character false := by
    intro h; have eq := congrArg signature h; norm_num [sig_fromFour,sig_even] at eq
  have bd : fromFour ≠ character true := by
    intro h; have eq := congrArg signature h; norm_num [sig_fromFour,sig_odd] at eq
  have cd : character false ≠ character true := by
    intro h; have eq := congrArg signature h; norm_num [sig_even,sig_odd] at eq
  let cands : Finset (DirichletCharacter ℂ 8) := {1,fromFour,character false,character true}
  have hc : cands.card=4 := by
    simp [cands,Finset.card_insert_of_notMem,ab,ac,ad,bc,bd,cd]
  have size : Fintype.card (DirichletCharacter ℂ 8)=4 := by
    simpa only [Nat.card_eq_fintype_card] using
      (card_eq_totient_of_hasEnoughRootsOfUnity ℂ 8).trans (by decide : (8:ℕ).totient=4)
  have hu := cands.eq_univ_of_card (hc.trans size.symm)
  have mem : χ∈cands := hu ▸ mem_univ χ
  simpa only [cands,mem_insert,mem_singleton] using mem

theorem primitive_iff (χ : DirichletCharacter ℂ 8) :
    χ.IsPrimitive ↔ χ=character false ∨ χ=character true := by
  constructor
  · intro h
    rcases all_characters χ with rfl|rfl|h|h
    · simpa [IsPrimitive,conductor_one] using h
    · have small : fromFour.conductor ∣ 4 := fromFour.conductor_dvd_of_mem_conductorSet
        (changeLevel_factorsThrough _ _)
      rw [show fromFour.conductor=8 from h] at small
      exact (show ¬(8:ℕ)∣4 by decide) small |>.elim
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl|rfl) <;> exact char_primitive _
end BMORModEight
end

section
namespace BMORModEight
open Complex DirichletCharacter Set

theorem even_height_two {s : ℂ} (hs : 1/2 ≤ s.re) (hu : s.re ≤ 1) (ht : |s.im| ≤ 2) :
    1/18 < ‖LFunction (character false) s‖ := by
  have head : (1/3 : ℝ) < (evenPolynomial s).re := even_head_lower hs ht
  have tail := even_polynomial_error hs hu ht
  have left := (abs_le.mp (Complex.abs_re_le_norm (LFunction (character false) s - evenPolynomial s))).1
  rw [sub_re] at left
  have right := (le_abs_self _).trans (Complex.abs_re_le_norm (LFunction (character false) s))
  linarith

theorem even_low_zeros_empty : lowZeros false 2 = ∅ := by
  apply lowZeros_empty_of_half_band
  intro s hs hu ht
  exact norm_pos_iff.mp (lt_trans (by norm_num) (even_height_two hs hu.le ht))

theorem primitive_zeros_empty (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : T ≤ 2) : BMORStripZeroCount.zeros χ T = ∅ := by
  have empty (b : Bool) : lowZeros b 2 = ∅ := by
    cases b
    · exact even_low_zeros_empty
    · exact odd_low_zeros_empty
  have separate (b : Bool) : BMORStripZeroCount.zeros (character b) T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hs,hu,ht,hz⟩ := (BMORStripZeroCount.mem_zeros _ _ _).mp hz
    have h : z ∈ lowZeros b 2 := ⟨hs,hu,ht.trans hT,hz⟩
    rw [empty] at h
    exact h
  rcases (primitive_iff χ).mp hχ with rfl|rfl
  · exact separate false
  · exact separate true

theorem primitive_zero_count (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : T ≤ 2) : BMORStripZeroCount.count χ T = 0 := by
  simp [BMORStripZeroCount.count, primitive_zeros_empty χ hχ hT]

theorem primitive_zero_weighted_sum (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : T ≤ 2) (weight : ℂ → ℝ) :
    (∑ z ∈ BMORStripZeroCount.zeros χ T,
      (analyticOrderNatAt (LFunction χ) z : ℝ) * weight z) = 0 := by
  simp [primitive_zeros_empty χ hχ hT]

end BMORModEight
end

section
namespace BMORHeightTwo104
open Finset DirichletCharacter BMORConductorParity

/-- The conductor-eight cases are discharged unconditionally. Only the
primitive conductors 13, 52 and 104 remain in the height-two count at 104. -/
theorem average_from_three_conductors
    (h : ∀ (d : ℕ) [NeZero d], d ∈ ({13,52,104} : Finset ℕ) →
      ∀ (ψ : DirichletCharacter ℂ d), ψ.IsPrimitive → ∀ b,
      ψ (-1) = sign b → BMORStripZeroCount.count ψ 2 ≤ cap b d) :
    (∑ χ : DirichletCharacter ℂ 104, ((∑ z ∈ BMORStripZeroCount.zeros χ 2,
      (analyticOrderNatAt (LFunction χ) z:ℝ) / Real.sqrt (z.im^2+1/4)) -
      (BMORStripZeroCount.count χ 2:ℝ)/2)) / 48 ≤ 83/32 := by
  apply average_net_weight
  apply four_conductor_reduction
  intro d _ hd ψ hp b hb
  rcases Finset.mem_insert.mp hd with rfl | hd'
  · rw [BMORModEight.primitive_zero_count ψ hp le_rfl]
    exact Nat.zero_le _
  · exact h d hd' ψ hp b hb
end BMORHeightTwo104
end

section
namespace BMORModEight
open Complex DirichletCharacter BMORProgression

theorem all_low_nonzero (χ : DirichletCharacter ℂ 8) {s : ℂ}
    (hs : 0<s.re) (hu : s.re<1) (ht : |s.im|≤2) : LFunction χ s ≠ 0 := by
  have h1 : s ≠ 1 := fun e => by simp [e] at hu
  have prim (b : Bool) : LFunction (character b) s ≠ 0 := by
    intro h
    have mem := (BMORStripZeroCount.mem_zeros (character b) 2 s).mpr ⟨hs,hu,ht,h⟩
    rw [primitive_zeros_empty _ (char_primitive b) le_rfl] at mem
    exact Finset.notMem_empty s mem
  rcases all_characters χ with rfl|rfl|rfl|rfl
  · exact principal_low_band_nonzero hs hu.le ht h1
  · intro h
    apply height_two_small_moduli (q:=4) (Or.inr (Or.inl rfl)) _ hs hu ht
    exact (LFunction_changeLevel_zero_iff (show 4∣8 by decide) _ hs (Or.inr h1)).mp h
  · exact prim false
  · exact prim true

theorem all_zeros_empty (χ : DirichletCharacter ℂ 8) {T : ℝ} (hT : T≤2) :
    BMORStripZeroCount.zeros χ T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hs,hu,ht,hz⟩ := (BMORStripZeroCount.mem_zeros χ T z).mp hz
  exact all_low_nonzero χ hs hu (ht.trans hT) hz

theorem all_zero_count (χ : DirichletCharacter ℂ 8) {T : ℝ} (hT : T≤2) :
    BMORStripZeroCount.count χ T = 0 := by
  simp [BMORStripZeroCount.count, all_zeros_empty χ hT]

theorem total_zero_count {T : ℝ} (hT : T≤2) :
    (∑ χ : DirichletCharacter ℂ 8, BMORStripZeroCount.count χ T) = 0 := by
  simp [all_zero_count _ hT]

end BMORModEight
end

section
noncomputable section
open Finset Complex
open BMORModThree.Mellin
namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

private def twiceSum (χ : DirichletCharacter ℂ q) (n : ℕ) :=
  ∑ k ∈ range n, charPartialSum χ k

private theorem double_sum (χ : DirichletCharacter ℂ q) {k : ℕ} (hk : k≤q) :
    twiceSum χ k = ∑ j ∈ range q, ((k-(j+1):ℕ):ℂ)*χ ((j+1:ℕ):ZMod q) := by
  induction k with
  | zero => simp [twiceSum]
  | succ k ih =>
    have hk' : k≤q := by omega
    have hsum : (∑ j ∈ range q, if j<k then χ ((j+1:ℕ):ZMod q) else 0) = charPartialSum χ k := by
      rw [← Finset.sum_filter]
      have hset : (range q).filter (fun j => j<k) = range k := by ext j; simp; omega
      rw [hset, charPartialSum]
    rw [twiceSum, Finset.sum_range_succ, ← twiceSum, ih hk', ← hsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j<k
    · rw [ite_eq_left hj, show k+1-(j+1) = k-(j+1)+1 by omega]; push_cast
      ring
    · simp [hj, show k-(j+1)=0 by omega, show k+1-(j+1)=0 by omega]

private theorem full_zero (χ : DirichletCharacter ℂ q) (hn : χ≠1) :
    charPartialSum χ q = 0 := by
  have h := (integerRemainder_periodic χ).map_mod_nat q
  simpa [integerRemainder, charMean_eq, hn, charPartialSum] using h.symm

/-- Twice q times the coefficient of a single character value in a centered knot,
shifted by one constant across the entire period. -/
def triangleWeight (q k j : ℕ) : ℤ :=
  2*((q:ℤ)*((k-(j+1):ℕ):ℤ) - (k:ℤ)*((q-(j+1):ℕ):ℤ)) + (k:ℤ)*((q:ℤ)-k)

theorem weighted_knot (χ : DirichletCharacter ℂ q) (hn : χ≠1) {k : ℕ} (hk : k≤q) :
    ((2:ℂ)*q) * knots χ k =
      ∑ j ∈ range q, (triangleWeight q k j : ℂ)*χ ((j+1:ℕ):ZMod q) := by
  have hknot : knots χ k = twiceSum χ k - (k:ℂ)*mean χ := by simp [knots, twiceSum]
  have hm : (q:ℂ)*mean χ = twiceSum χ q := by
    rw [mean_eq_finite χ hn]; unfold twiceSum; field_simp [NeZero.ne (q:ℂ)]
  have hz : (∑ j ∈ range q, χ ((j+1:ℕ):ZMod q)) = 0 := full_zero χ hn
  calc
    _ = 2*((q:ℂ)*twiceSum χ k - (k:ℂ)*((q:ℂ)*mean χ)) := by rw [hknot]; ring
    _ = 2*((q:ℂ)*twiceSum χ k - (k:ℂ)*twiceSum χ q) +
          ((k:ℂ)*((q:ℂ)-k))*(∑ j ∈ range q, χ ((j+1:ℕ):ZMod q)) := by rw [hm, hz]; ring
    _ = _ := by
      rw [double_sum χ hk, double_sum χ (le_refl q)]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast [triangleWeight]; ring

end BMORPeriodicTail

namespace BMORPeriodicTail
open Finset Complex
variable {q : ℕ} [NeZero q]

/-- Character-independent integer arithmetic using only unit residue classes. -/
def radiusCost (q k : ℕ) : ℕ := ∑ j ∈ range q,
  if (j+1).Coprime q then (triangleWeight q k j).natAbs else 0

theorem norm_knot_from_cost (χ : DirichletCharacter ℂ q) (hn : χ≠1) {k B : ℕ} (hk : k≤q)
    (hB : radiusCost q k ≤ 2*q*B) : ‖knots χ k‖ ≤ B := by
  have hsum : ‖∑ j ∈ range q, (triangleWeight q k j : ℂ)*χ ((j+1:ℕ):ZMod q)‖ ≤
      (radiusCost q k:ℝ) := by
    unfold radiusCost
    push_cast
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    split
    next hj =>
      rw [norm_mul]
      have hnw : ‖(triangleWeight q k j:ℂ)‖ = ((triangleWeight q k j).natAbs:ℝ) := by
        rw [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
      rw [hnw]
      exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (by positivity)).trans_eq (mul_one _)
    next hj =>
      have hz : χ ((j+1:ℕ):ZMod q) = 0 := χ.map_nonunit (fun h => hj ((ZMod.isUnit_iff_coprime _ _).mp h))
      have hz' : χ ((j:ZMod q)+1) = 0 := by simpa using hz
      simp [hz']
  rw [← weighted_knot χ hn hk, norm_mul, norm_mul, Complex.norm_natCast] at hsum
  have hscale : 0<(2:ℝ)*q := mul_pos (by norm_num) (by exact_mod_cast q.pos_of_neZero)
  apply (mul_le_mul_iff_right₀ hscale).mp
  refine (by simpa using hsum : (2:ℝ)*q*‖knots χ k‖ ≤ radiusCost q k).trans ?_
  exact_mod_cast hB

def UnitRadius (q B : ℕ) := ∀ k : Fin (q+1), radiusCost q k ≤ 2*q*B

instance (q B : ℕ) : Decidable (UnitRadius q B) := inferInstanceAs
  (Decidable (∀ k : Fin (q+1), radiusCost q k ≤ 2*q*B))

theorem radius8 : UnitRadius 8 2 := by decide +kernel
theorem radius13 : UnitRadius 13 9 := by decide +kernel
theorem radius52 : UnitRadius 52 84 := by decide +kernel
set_option maxHeartbeats 2000000 in
theorem radius104 : UnitRadius 104 312 := by decide +kernel

private theorem knots_periodic (χ : DirichletCharacter ℂ q) (hn : χ≠1) :
    Function.Periodic (knots χ) q := by
  intro n
  rw [← primitive_nat χ hn, ← primitive_nat χ hn, Nat.cast_add, primitive_periodic χ 0 n]

/-- For a cutoff divisible by the modulus, the all-character bound follows from
the q+1 rational inequalities without enumeration of the characters. -/
theorem uniform_radius_at_multiple (χ : DirichletCharacter ℂ q) (hn : χ≠1) {N B : ℕ}
    (hN : q∣N) (hb : UnitRadius q B) (x : ℝ) : ‖primitive χ N x‖ ≤ B := by
  apply norm_primitive_le_of_knots χ hn N _ x
  intro k hk
  have hz : knots χ N = 0 := by
    rw [← (knots_periodic χ hn).map_mod_nat N, Nat.mod_eq_zero_of_dvd hN]; simp [knots]
  rw [hz, sub_zero]
  exact norm_knot_from_cost χ hn hk (hb ⟨k, by omega⟩)

end BMORPeriodicTail
end
end

section
noncomputable section
open Complex
namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

/-- A rational bound for heights at most two, using a natural lower bound for sqrt(N).
All hypotheses except the strip position are finite arithmetic in naturals. -/
theorem error_at_multiple (χ : DirichletCharacter ℂ q) (hn : χ≠1) {N B m : ℕ}
    (ha : q∣N) (hb : UnitRadius q B) (hN : 1≤N) (hm : 1≤m) (hsq : m^2≤N)
    {s : ℂ} (hlo : 1/2≤s.re) (hhi : s.re≤1) (ht : |s.im|≤2) :
    ‖DirichletCharacter.LFunction χ s-corrected χ N s‖ ≤
      (15*(B:ℝ))/(4*N*m) := by
  have hs : 0<s.re := by linarith
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  have hpos : 0<(N:ℝ) := by linarith
  have hmpos : 0<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
  have hsqr : (m:ℝ)^2≤N := by exact_mod_cast hsq
  have hroot : (m:ℝ)≤Real.sqrt N := by
    nlinarith [Real.sq_sqrt hpos.le, Real.sqrt_nonneg (N:ℝ)]
  have hp : (N:ℝ)^(-s.re-1) ≤ 1/((N:ℝ)*m) := by
    calc
      _ ≤ (N:ℝ)^(-(1+1/2):ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = 1/((N:ℝ)*Real.sqrt N) := by
        rw [Real.rpow_neg hpos.le, Real.rpow_add hpos, Real.rpow_one,
          ← Real.sqrt_eq_rpow, one_div]
      _ ≤ _ := one_div_le_one_div_of_le (mul_pos hpos hmpos)
        (mul_le_mul_of_nonneg_left hroot hpos.le)
  have he := error_bound χ hn hN hs (fun x _ => uniform_radius_at_multiple χ hn ha hb x)
  refine he.trans ((mul_le_mul_of_nonneg_right (low_strip_factor hlo hhi ht) (by positivity)).trans ?_)
  calc
    _ = ((15/4)*(B:ℝ))*(N:ℝ)^(-s.re-1) := by
      field_simp [show s.re+1≠0 by linarith]
    _ ≤ ((15/4)*(B:ℝ))*(1/((N:ℝ)*m)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- One common 1/10 certificate for each of the four target moduli; the cutoffs
24, 52, 260 and 624 were chosen to keep both the proof and the polynomial small. -/
theorem error_moduli {s : ℂ} (hlo : 1/2≤s.re) (hhi : s.re≤1) (ht : |s.im|≤2) :
  (∀ χ : DirichletCharacter ℂ 8, χ≠1 → ‖DirichletCharacter.LFunction χ s-corrected χ 24 s‖ < 1/10) ∧
  (∀ χ : DirichletCharacter ℂ 13, χ≠1 → ‖DirichletCharacter.LFunction χ s-corrected χ 52 s‖ < 1/10) ∧
  (∀ χ : DirichletCharacter ℂ 52, χ≠1 → ‖DirichletCharacter.LFunction χ s-corrected χ 260 s‖ < 1/10) ∧
   ∀ χ : DirichletCharacter ℂ 104, χ≠1 → ‖DirichletCharacter.LFunction χ s-corrected χ 624 s‖ < 1/10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro χ hn
  · exact (error_at_multiple χ hn (by decide) radius8 (N:=24) (m:=4) (by decide) (by decide)
      (by decide) hlo hhi ht).trans_lt (by norm_num)
  · exact (error_at_multiple χ hn (by decide) radius13 (N:=52) (m:=7) (by decide) (by decide)
      (by decide) hlo hhi ht).trans_lt (by norm_num)
  · exact (error_at_multiple χ hn (by decide) radius52 (N:=260) (m:=16) (by decide) (by decide)
      (by decide) hlo hhi ht).trans_lt (by norm_num)
  · exact (error_at_multiple χ hn (by decide) radius104 (N:=624) (m:=24) (by decide) (by decide)
      (by decide) hlo hhi ht).trans_lt (by norm_num)

end BMORPeriodicTail
end
end

section
noncomputable section
open Complex Filter Finset
open BMORModThree.Mellin
namespace BMORPeriodicTail
variable {q : ℕ} [NeZero q]

/-- The explicit log-weighted corrected polynomial, suitable for interval evaluation. -/
def correctedPrime (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  (∑ k ∈ range N, -(((k+1:ℕ):ℂ)^(-s)*Complex.log (k+1:ℕ)) * χ ((k+1:ℕ):ZMod q)) +
  (mean χ - charPartialSum χ N)*(-((N:ℂ)^(-s)*Complex.log N))

theorem hasDerivAt_corrected (χ : DirichletCharacter ℂ q) {N : ℕ} (hN : 0<N) (s : ℂ) :
    HasDerivAt (corrected χ N) (correctedPrime χ N s) s := by
  have ht (n : ℕ) (hn : 0<n) : HasDerivAt (fun t : ℂ => (n:ℂ)^(-t))
      (-((n:ℂ)^(-s)*Complex.log n)) s := by
    have h := (hasDerivAt_id s).neg.const_cpow (c := (n:ℂ)) (.inl (by exact_mod_cast hn.ne'))
    simpa using h
  apply HasDerivAt.add
  · exact HasDerivAt.fun_sum (u := range N) (fun k _ => (ht (k+1) (by omega)).mul_const (χ ((k+1:ℕ):ZMod q)))
  · exact (ht N hN).const_mul _

theorem deriv_corrected_eq (χ : DirichletCharacter ℂ q) {N : ℕ} (hN : 0<N) (s : ℂ) :
    deriv (corrected χ N) s = correctedPrime χ N s := (hasDerivAt_corrected χ hN s).deriv

/-- Cauchy's derivative estimate on any circle around the region of interest. -/
theorem derivative_from_sphere (χ : DirichletCharacter ℂ q) (hn : χ≠1) {N : ℕ} (hN : 0<N)
    {z : ℂ} {R M : ℝ} (hR : 0<R)
    (hB : ∀ w ∈ Metric.sphere z R, ‖DirichletCharacter.LFunction χ w-corrected χ N w‖ ≤ M) :
    ‖deriv (DirichletCharacter.LFunction χ) z - deriv (corrected χ N) z‖ ≤ M/R := by
  have hf := DirichletCharacter.differentiable_LFunction hn
  have hg : Differentiable ℂ (corrected χ N) := fun s => (hasDerivAt_corrected χ hN s).differentiableAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (hf.sub hg).diffContOnCl hB
  simpa only [deriv_sub (hf z) (hg z)] using h

/-- q=13 at a cutoff divisible by 13: function error on enlarged discs. -/
theorem error13_around_line (χ : DirichletCharacter ℂ 13) (hn : χ≠1)
    {s : ℂ} (hlo : 1/4≤s.re) (hhi : s.re≤3/4) (ht : |s.im|≤17/8) :
    ‖DirichletCharacter.LFunction χ s - corrected χ 390 s‖ ≤ (252:ℝ)/8125 := by
  have hs : 0<s.re := by linarith
  have hi := abs_le.mp ht
  have him : s.im^2 ≤ (17/8:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.2) (by linarith : 0≤17/8+s.im)]
  have hre : s.re^2 ≤ (3/4:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0≤3/4+s.re)]
  have hr1 : (s.re+1)^2 ≤ (7/4:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0≤11/4+s.re)]
  have hn1 : ‖s‖ ≤ 12/5 := by
    have h : ‖s‖^2 = s.re^2+s.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
    nlinarith [norm_nonneg s]
  have hn2 : ‖s+1‖ ≤ 14/5 := by
    have h : ‖s+1‖^2 = (s.re+1)^2+s.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; simp; ring
    nlinarith [norm_nonneg (s+1)]
  have powval : (390:ℝ)^(-s.re-1) ≤ 1/(390*4) := by
    have hbase : (256:ℝ)^(1/4:ℝ) = 4 := by
      rw [show (256:ℝ) = 4^(4:ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0:ℝ)≤4)]
      norm_num
    have hroot : (4:ℝ)≤390^(1/4:ℝ) := by
      exact hbase.ge.trans (Real.rpow_le_rpow (by norm_num) (by norm_num : (256:ℝ)≤390) (by norm_num))
    calc
      _ ≤ (390:ℝ)^(-(1+1/4):ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1/(390*(390:ℝ)^(1/4:ℝ)) := by rw [Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]; simp only [one_div]
      _ ≤ _ := one_div_le_one_div_of_le (by norm_num) (mul_le_mul_of_nonneg_left hroot (by norm_num))
  have he := error_bound χ hn (N:=390) (by decide) hs
    (fun x _ => uniform_radius_at_multiple χ hn (by decide : 13∣390) radius13 x)
  norm_num only [Nat.cast_ofNat] at he
  refine he.trans ?_
  have hp := mul_le_mul hn1 hn2 (norm_nonneg _) (by norm_num)
  have hd : 9*(390:ℝ)^(-s.re-1)/(s.re+1) ≤ 9*(1/(390*4))/(5/4) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left powval (by norm_num))
      (by norm_num) (by linarith)
  exact (mul_le_mul hp hd (by positivity) (by norm_num)).trans_eq (by norm_num)

/-- On both sides of the critical line, for every nonprincipal character modulo 13,
a 390-term corrected polynomial approximates the true derivative within 1/4. -/
theorem derivative13_near_line (χ : DirichletCharacter ℂ 13) (hn : χ≠1)
    {z : ℂ} (hlo : 3/8≤z.re) (hhi : z.re≤5/8) (ht : |z.im|≤2) :
    ‖deriv (DirichletCharacter.LFunction χ) z - deriv (corrected χ 390) z‖ < 1/4 := by
  refine (derivative_from_sphere χ hn (N:=390) (by decide)
    (z:=z) (R:=1/8) (M:=252/8125) (by norm_num) ?_).trans_lt (by norm_num)
  intro w hw
  have distEq : ‖w-z‖=1/8 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hw
  have hr := abs_le.mp (Complex.abs_re_le_norm (w-z))
  have hi := abs_le.mp (Complex.abs_im_le_norm (w-z))
  rw [distEq, Complex.sub_re] at hr
  rw [distEq, Complex.sub_im] at hi
  have ht' := abs_le.mp ht
  exact error13_around_line χ hn (by linarith [hr.1]) (by linarith [hr.2])
    (abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩)

/-- The same enclosure in a form that can be used directly by a finite interval evaluator. -/
theorem derivative13_explicit (χ : DirichletCharacter ℂ 13) (hn : χ≠1)
    {z : ℂ} (hlo : 3/8≤z.re) (hhi : z.re≤5/8) (ht : |z.im|≤2) :
    ‖deriv (DirichletCharacter.LFunction χ) z - correctedPrime χ 390 z‖ < 1/4 := by
  simpa only [deriv_corrected_eq χ (by decide : 0 < 390) z] using
    derivative13_near_line χ hn hlo hhi ht

end BMORPeriodicTail
end
end

section
namespace BMORThirteenCertificate
open Complex DirichletCharacter BMORPeriodicTail BMORStripZeroCount

private theorem nonzero_of_polynomial (χ : DirichletCharacter ℂ 13) (hn : χ≠1)
    (z : ℂ) (hl : 1/2≤z.re) (hu : z.re≤1) (ht : |z.im|≤2)
    (h : (135/4160:ℝ) < ‖corrected χ 104 z‖) : LFunction χ z ≠ 0 := by
  have he := error_at_multiple χ hn (N:=104) (m:=10) (by decide) radius13
    (by decide) (by decide) (by decide) hl hu ht
  intro hz
  rw [hz,zero_sub,norm_neg] at he
  norm_num at he h
  linarith

/-- Both half-strip checks involve only finite 104-term expressions. -/
theorem cover_of_polynomials (χ : DirichletCharacter ℂ 13) (hp : χ.IsPrimitive) (hn : χ≠1)
    (S : Set ℂ)
    (h : ∀ z : ℂ, 1/2≤z.re → z.re≤1 → |z.im|≤2 → z∉S →
      (135/4160:ℝ) < ‖corrected χ 104 z‖)
    (hi : ∀ z : ℂ, 1/2≤z.re → z.re≤1 → |z.im|≤2 → 1-z∉S →
      (135/4160:ℝ) < ‖corrected χ⁻¹ 104 z‖) :
    ∀ z ∈ zeros χ 2, z ∈ S := by
  intro z hz
  obtain ⟨hl,hu,ht,hz0⟩ := (mem_zeros χ 2 z).mp hz
  by_contra hs
  by_cases hc : 1/2≤z.re
  · exact nonzero_of_polynomial χ hn z hc hu.le ht (h z hc hu.le ht hs) hz0
  · apply BMORModThree.reflect_nonvanishing χ hp hl hu _ hz0
    have l : 1/2≤(1-z).re := by simp only [sub_re,one_re]; linarith
    have u : (1-z).re≤1 := by simp only [sub_re,one_re]; linarith
    have t : |(1-z).im|≤2 := by simpa using ht
    exact nonzero_of_polynomial χ⁻¹ (fun e => hn (inv_eq_one.mp e)) _ l u t
      (hi _ l u t (by simpa using hs))

/-- A single convex candidate box suffices if the finite 390-term derivative
polynomial stays in a disk with room for its certified uniform remainder. -/
theorem count_le_one (χ : DirichletCharacter ℂ 13) (hp : χ.IsPrimitive) (hn : χ≠1)
    (S : Set ℂ) (hS : Convex ℝ S)
    (small : ∀ z ∈ S, 3/8≤z.re ∧ z.re≤5/8 ∧ |z.im|≤2)
    (h : ∀ z : ℂ, 1/2≤z.re → z.re≤1 → |z.im|≤2 → z∉S →
      (135/4160:ℝ) < ‖corrected χ 104 z‖)
    (hi : ∀ z : ℂ, 1/2≤z.re → z.re≤1 → |z.im|≤2 → 1-z∉S →
      (135/4160:ℝ) < ‖corrected χ⁻¹ 104 z‖)
    (a : ℂ) (r : ℝ) (hr : 1/4+r < ‖a‖)
    (hd : ∀ z ∈ S, ‖correctedPrime χ 390 z-a‖ ≤ r) :
    count χ 2 ≤ 1 := by
  apply BMORCountBoxes.count_of_cover χ 2 (fun _ : Fin 1 => S) (fun _ => a) (fun _ => 1/4+r)
  · exact fun z hz => ⟨0,cover_of_polynomials χ hp hn S h hi z hz⟩
  · exact fun _ => hS
  · exact fun _ => hr
  · intro i z _
    exact ((differentiable_LFunction hn).analyticAt z)
  · intro i z hz
    obtain ⟨hl,hu,ht⟩ := small z hz
    have tri := dist_triangle (deriv (LFunction χ) z) (correctedPrime χ 390 z) a
    simp only [dist_eq_norm] at tri
    exact tri.trans (add_le_add (derivative13_explicit χ hn hl hu ht).le (hd z hz))
end BMORThirteenCertificate
end

section
namespace BMORModThirteen
open Complex DirichletCharacter

local instance : Fact (1 < 13) := ⟨by decide⟩

/-- The positive primitive twelfth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I / 12)

theorem omega_primitive : IsPrimitiveRoot omega 12 := Complex.isPrimitiveRoot_exp 12 (by decide)

theorem omega_radical : omega = ((Real.sqrt 3 : ℂ) + I) / 2 := by
  have he : (2 * (Real.pi : ℂ) * I / 12) = ((Real.pi / 6 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [omega, he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- The base-2 discrete logarithm on nonzero residue classes. The zero entry is unused. -/
def discreteLog (r : ZMod 13) : ℕ :=
  match r.val with
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | 5 => 9
  | 6 => 5
  | 7 => 11
  | 8 => 3
  | 9 => 8
  | 10 => 10
  | 11 => 7
  | 12 => 6
  | _ => 0

theorem two_pow_discreteLog : ∀ r : ZMod 13, r ≠ 0 → 2 ^ discreteLog r = r := by decide

private theorem two_unit : IsUnit (2 : ZMod 13) :=
  (ZMod.isUnit_iff_coprime 2 13).mpr (by decide)

theorem ext_two {χ ψ : DirichletCharacter ℂ 13} (h : χ 2 = ψ 2) : χ = ψ := by
  apply MulChar.ext
  intro r
  have hr : (r : ZMod 13) ≠ 0 := r.ne_zero
  conv_lhs => rw [← two_pow_discreteLog _ hr, map_pow]
  conv_rhs => rw [← two_pow_discreteLog _ hr, map_pow]
  rw [h]

theorem exists_exponent (χ : DirichletCharacter ℂ 13) :
    ∃ k : Fin 12, χ 2 = omega ^ (k : ℕ) := by
  have hw : χ (2 : ZMod 13) ^ 12 = 1 := by
    rw [← map_pow, show (2 : ZMod 13) ^ 12 = 1 by decide, map_one]
  obtain ⟨k, hk, e⟩ := omega_primitive.eq_pow_of_pow_eq_one hw
  exact ⟨⟨k, hk⟩, e.symm⟩

noncomputable def index (χ : DirichletCharacter ℂ 13) : Fin 12 := (exists_exponent χ).choose

theorem eval_two (χ : DirichletCharacter ℂ 13) : χ 2 = omega ^ (index χ : ℕ) :=
  (exists_exponent χ).choose_spec

theorem index_eq_iff {χ : DirichletCharacter ℂ 13} {k : Fin 12} :
    index χ = k ↔ χ 2 = omega ^ (k : ℕ) := by
  constructor
  · rintro rfl
    exact eval_two _
  · intro h
    exact Fin.ext (omega_primitive.pow_inj (index χ).isLt k.isLt ((eval_two χ).symm.trans h))

theorem index_bijective : Function.Bijective index := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro χ ψ e
    exact ext_two ((eval_two χ).trans (e ▸ (eval_two ψ).symm))
  · rw [card_eq_totient_of_hasEnoughRootsOfUnity ℂ 13, Nat.card_fin]
    decide

noncomputable def characterEquiv : DirichletCharacter ℂ 13 ≃ Fin 12 :=
  Equiv.ofBijective index index_bijective

noncomputable def character (k : Fin 12) : DirichletCharacter ℂ 13 := characterEquiv.symm k

@[simp] theorem index_character (k : Fin 12) : index (character k) = k :=
  characterEquiv.apply_symm_apply k

theorem character_index (χ : DirichletCharacter ℂ 13) : character (index χ) = χ :=
  characterEquiv.symm_apply_apply χ

theorem character_two (k : Fin 12) : character k 2 = omega ^ (k : ℕ) :=
  index_eq_iff.mp (index_character k)

theorem character_apply (k : Fin 12) (r : ZMod 13) :
    character k r = if r = 0 then 0 else omega ^ ((k : ℕ) * discreteLog r) := by
  split_ifs with hr
  · subst r
    exact MulChar.map_nonunit _ (by simp)
  · conv_lhs => rw [← two_pow_discreteLog _ hr, map_pow, character_two, ← pow_mul]


/-- Directly matches the finite twelve-entry array, reducing the exponent before evaluation. -/
theorem character_table (k : Fin 12) (r : ZMod 13) :
    character k r = if r = 0 then 0 else omega ^ (((k : ℕ) * discreteLog r) % 12) := by
  rw [character_apply]
  split_ifs
  · rfl
  · exact pow_eq_pow_mod _ omega_primitive.pow_eq_one

theorem index_one : index (1 : DirichletCharacter ℂ 13) = 0 := by
  apply index_eq_iff.mpr
  simp [MulChar.one_apply two_unit]

theorem character_zero : character 0 = 1 := by
  rw [← index_one, character_index]

theorem nonprincipal_iff (k : Fin 12) : character k ≠ 1 ↔ k ≠ 0 := by
  rw [← character_zero]
  exact characterEquiv.symm.injective.ne_iff

theorem nonprincipal_cases (χ : DirichletCharacter ℂ 13) (hχ : χ ≠ 1) :
    ∃ k : Fin 12, k ≠ 0 ∧ χ = character k := by
  exact ⟨index χ, (nonprincipal_iff _).mp ((character_index χ).symm ▸ hχ), (character_index χ).symm⟩


theorem primitive_iff_nonzero (k : Fin 12) : (character k).IsPrimitive ↔ k ≠ 0 := by
  constructor
  · rintro h rfl
    have eq : (character 0).conductor = 13 := h
    rw [character_zero, conductor_one] at eq
    contradiction
  · intro h
    rcases (show Nat.Prime 13 by decide).eq_one_or_self_of_dvd _ (conductor_dvd_level (character k)) with hc|hc
    · exact ((nonprincipal_iff k).mpr h (eq_one_iff_conductor_eq_one.mpr hc)).elim
    · exact hc

theorem unique_nonprincipal (χ : DirichletCharacter ℂ 13) (hχ : χ ≠ 1) :
    ∃! k : Fin 12, k ≠ 0 ∧ χ = character k := by
  obtain ⟨k, hk, rfl⟩ := nonprincipal_cases χ hχ
  refine ⟨k, ⟨hk, rfl⟩, ?_⟩
  intro j hj
  exact characterEquiv.symm.injective hj.2.symm

theorem character_inv {j k : Fin 12} (h : (j : ℕ) + k = 12) :
    (character j)⁻¹ = character k := by
  apply ext_two
  rw [MulChar.inv_apply_eq_inv',character_two,character_two]
  have hp : omega ^ (j : ℕ) * omega ^ (k : ℕ) = 1 := by
    rw [← pow_add,h,omega_primitive.pow_eq_one]
  exact inv_eq_of_mul_eq_one_right hp

theorem five_inverse : (character 5)⁻¹ = character 7 := character_inv (by decide)
theorem seven_inverse : (character 7)⁻¹ = character 5 := character_inv (by decide)

end BMORModThirteen
end

section
noncomputable section
namespace BMORModThirteen
open Complex Finset BMORModThree.Mellin BMORPeriodicTail

/-- Character coefficient used by the finite evaluator. -/
def tableValue (k : Fin 12) (n : ℕ) : ℂ :=
  if (n : ZMod 13) = 0 then 0 else omega ^ (((k : ℕ) * discreteLog (n : ZMod 13)) % 12)

theorem character_nat (k : Fin 12) (n : ℕ) : character k (n : ZMod 13) = tableValue k n :=
  character_table k _

/-- The centering coefficient computed by the thirteen-residue loop. -/
def tableMean (k : Fin 12) : ℂ :=
  ∑ j ∈ range 13, tableValue k (j+1) * ((13-((j+1 : ℕ):ℂ))/13)

private theorem summed_prefixes (f : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ range n, ∑ j ∈ range k, f (j+1)) =
      ∑ j ∈ range n, (((n : ℂ)-((j+1 : ℕ):ℂ))*f (j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j => (((n+1:ℕ):ℂ)-((j+1:ℕ):ℂ))*f (j+1))]
    simp only [sub_self,zero_mul,add_zero,← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    ring

theorem mean_eq_table (k : Fin 12) (hk : k ≠ 0) :
    mean (character k) = tableMean k := by
  rw [mean_eq_finite _ ((nonprincipal_iff k).mpr hk)]
  simp only [charPartialSum, character_nat, summed_prefixes, tableMean, Finset.sum_div]
  apply sum_congr rfl
  intro j _
  push_cast
  ring

theorem partial_sum_at_multiple (k : Fin 12) (hk : k ≠ 0) {N : ℕ} (hN : 13 ∣ N) :
    charPartialSum (character k) N = 0 := by
  have hp := (integerRemainder_periodic (character k)).map_mod_nat N
  simpa [integerRemainder, charMean_eq, (nonprincipal_iff k).mpr hk,
    Nat.mod_eq_zero_of_dvd hN, charPartialSum] using hp.symm

/-- Exact identity for the Python fixed point evaluator's unrounded polynomial. -/
theorem corrected_eq_table (k : Fin 12) (hk : k ≠ 0) {N : ℕ} (hN : 13 ∣ N) (s : ℂ) :
    corrected (character k) N s =
      (∑ j ∈ range N, ((j+1 : ℕ) : ℂ)^(-s) * tableValue k (j+1)) +
        tableMean k * (N:ℂ)^(-s) := by
  simp only [corrected, head, character_nat, mean_eq_table k hk, partial_sum_at_multiple k hk hN, sub_zero]

theorem correctedPrime_eq_table (k : Fin 12) (hk : k ≠ 0) {N : ℕ} (hN : 13 ∣ N) (s : ℂ) :
    correctedPrime (character k) N s =
      (∑ j ∈ range N, -(((j+1:ℕ):ℂ)^(-s)*Complex.log (j+1:ℕ)) * tableValue k (j+1)) +
        tableMean k * (-((N:ℂ)^(-s)*Complex.log N)) := by
  simp only [correctedPrime, character_nat, mean_eq_table k hk, partial_sum_at_multiple k hk hN, sub_zero]

end BMORModThirteen
end
end

section
namespace BMORRationalExpLog
open Finset

noncomputable def expTaylor32 (z : ℂ) : ℂ := ∑ k ∈ range 33, z ^ k / k.factorial

theorem l1_le_three_halves_norm (w : ℂ) : |w.re| + |w.im| ≤ (3/2 : ℝ) * ‖w‖ := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith only [Complex.sq_norm_sub_sq_re w, sq_abs w.re, sq_abs w.im,
    sq_nonneg (|w.re| - |w.im|), sq_nonneg ‖w‖]

private theorem norm_exp_error_sharp (z : ℂ) (h : ‖z‖ ≤ 1) :
    ‖Complex.exp z - expTaylor32 z‖ ≤ 34 / ((Nat.factorial 33 : ℝ) * 33) := by
  have a := Complex.exp_bound h (n := 33) (by decide)
  have p := pow_le_one₀ (norm_nonneg z) h (n := 33)
  refine a.trans ?_
  norm_num only [Nat.cast_ofNat, Nat.reduceSucc]
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (by positivity) p

/-- Euclidean-norm enclosure for the Taylor polynomial through degree 32. -/
theorem exp_error (z : ℂ) (h : ‖z‖ ≤ 1) :
    ‖Complex.exp z - expTaylor32 z‖ ≤ 2 / (Nat.factorial 33 : ℝ) := by
  exact (norm_exp_error_sharp z h).trans (by norm_num [Nat.factorial])

/-- The same numerical allowance also works with the additive componentwise radius. -/
theorem exp_error_l1 (z : ℂ) (h : ‖z‖ ≤ 1) :
    |(Complex.exp z - expTaylor32 z).re| + |(Complex.exp z - expTaylor32 z).im| ≤
      2 / (Nat.factorial 33 : ℝ) := by
  refine (l1_le_three_halves_norm _).trans ?_
  calc
    _ ≤ (3/2 : ℝ) * (34 / ((Nat.factorial 33 : ℝ) * 33)) :=
      mul_le_mul_of_nonneg_left (norm_exp_error_sharp z h) (by norm_num)
    _ ≤ _ := by norm_num [Nat.factorial]

/-- Five squarings undo the argument reduction by 32. -/
theorem five_squares (z : ℂ) :
    (((((Complex.exp (z/32))^2)^2)^2)^2)^2 = Complex.exp z := by
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  change Complex.exp (z/32)^32 = Complex.exp z
  rw [← Complex.exp_nat_mul (z/32) 32]
  congr 1
  push_cast
  ring

noncomputable def logTaylor41 (t : ℝ) : ℝ :=
  2 * ∑ j ∈ range 41, t^(2*j+1) / (2*j+1)

theorem log_error (t : ℝ) (ht : 0 ≤ t) (h : t ≤ 1/3) :
    |Real.log ((1+t)/(1-t)) - logTaylor41 t| ≤ 2*t^83/(1-t^2) := by
  have ht' : |t|<1 := by rw [abs_of_nonneg ht]; linarith
  have e := Real.sum_range_sub_log_div_le ht' 41
  rw [abs_of_nonneg ht] at e
  change |(1/2 : ℝ) * Real.log ((1+t)/(1-t)) -
    ∑ j ∈ range 41, t^(2*j+1)/(2*j+1)| ≤ t^83/(1-t^2) at e
  unfold logTaylor41
  rw [show Real.log ((1+t)/(1-t)) - 2 * ∑ j ∈ range 41, t^(2*j+1)/(2*j+1) =
    2 * ((1/2 : ℝ) * Real.log ((1+t)/(1-t)) - ∑ j ∈ range 41, t^(2*j+1)/(2*j+1)) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0:ℝ)≤2), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left e (by norm_num)

/-- Direct range-reduction interface for the script's m in [1,2]. -/
theorem reduced_log_error {m : ℝ} (hm : 1≤m) (hu : m≤2) :
    let t := (m-1)/(m+1)
    |Real.log m - logTaylor41 t| ≤ 2*t^83/(1-t^2) := by
  dsimp only
  have hd : 0<m+1 := by linarith
  have ht : 0≤(m-1)/(m+1) := div_nonneg (by linarith) hd.le
  have hup : (m-1)/(m+1)≤1/3 := (div_le_iff₀ hd).mpr (by linarith)
  have hden : 0<1-(m-1)/(m+1) := by linarith
  have eq : (1+(m-1)/(m+1))/(1-(m-1)/(m+1))=m := by
    apply (div_eq_iff hden.ne').mpr
    field_simp
    ring
  simpa only [eq] using log_error ((m-1)/(m+1)) ht hup

end BMORRationalExpLog
end

section
namespace BMORRationalExpTail
open Finset Complex Filter
open scoped Topology

noncomputable def l1 (z : ℂ) : ℝ := |z.re| + |z.im|

theorem l1_nonneg (z : ℂ) : 0 ≤ l1 z := by unfold l1; positivity

theorem l1_add (a b : ℂ) : l1 (a+b) ≤ l1 a + l1 b := by
  simp only [l1, add_re, add_im]
  linarith [abs_add_le a.re b.re, abs_add_le a.im b.im]

theorem l1_mul (a b : ℂ) : l1 (a*b) ≤ l1 a * l1 b := by
  have hr := abs_sub (a.re*b.re) (a.im*b.im)
  have hi := abs_add_le (a.re*b.im) (a.im*b.re)
  simp only [abs_mul] at hr hi
  simp only [l1, mul_re, mul_im]
  linarith only [hr,hi]

theorem l1_pow (z : ℂ) (n : ℕ) : l1 (z^n) ≤ l1 z ^ n := by
  induction n with
  | zero => simp [l1]
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (l1_mul ..).trans (mul_le_mul_of_nonneg_right ih (l1_nonneg z))

theorem l1_sum {ι : Type*} (F : Finset ι) (f : ι → ℂ) :
    l1 (∑ i ∈ F, f i) ≤ ∑ i ∈ F, l1 (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [l1]
  | insert i F hi ih => simp only [sum_insert hi]; exact (l1_add ..).trans (by linarith)

private theorem l1_div_natCast (z : ℂ) (n : ℕ) : l1 (z/n) = l1 z/n := by
  simp [l1, Complex.div_natCast_re, Complex.div_natCast_im, abs_div, add_div]

/-- Bound terms starting at index m using the geometric ratio v/(m+1). -/
private theorem tail_term {z : ℂ} {v : ℝ} (hz : l1 z ≤ v) (m i : ℕ) :
    l1 (z^(i+m)/(i+m).factorial) ≤
      v^m/(m.factorial : ℝ) * (v/((m:ℝ)+1))^i := by
  have hv := (l1_nonneg z).trans hz
  have hf : (m.factorial : ℝ) * ((m:ℝ)+1)^i ≤ ((m+i).factorial : ℝ) := by
    exact_mod_cast (@Nat.factorial_mul_pow_le_factorial m i)
  rw [l1_div_natCast, Nat.add_comm i m]
  calc
    _ ≤ v^(m+i) / ((m+i).factorial : ℝ) := by
      gcongr
      exact (l1_pow z (m+i)).trans (pow_le_pow_left₀ (l1_nonneg _) hz _)
    _ ≤ v^(m+i) / ((m.factorial : ℝ) * ((m:ℝ)+1)^i) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hf
    _ = _ := by rw [pow_add, div_pow]; ring

/-- This is the precise radius added by the finite-cover code after its last polynomial term.
    m is the first omitted index, so degree 18 corresponds to m=19. -/
theorem exp_tail_l1 (z : ℂ) (m : ℕ) (v : ℝ) (hz : l1 z ≤ v) (h : v < (m:ℝ)+1) :
    l1 (Complex.exp z - ∑ i ∈ range m, z^i/i.factorial) ≤
      v^m/(m.factorial : ℝ) / (1 - v/((m:ℝ)+1)) := by
  let c := v^m/(m.factorial : ℝ)
  let r := v/((m:ℝ)+1)
  have hv := (l1_nonneg z).trans hz
  have hc : 0≤c := by dsimp [c]; positivity
  have hr : 0≤r := by dsimp [r]; positivity
  have hr' : r<1 := (div_lt_one (by positivity)).mpr h
  have series : HasSum (fun i : ℕ => z^i / i.factorial) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    exact (NormedSpace.expSeries_div_summable z).hasSum
  have tail := ((hasSum_nat_add_iff' m).mpr series).tendsto_sum_nat
  have cont : Continuous l1 := Complex.continuous_re.abs.add Complex.continuous_im.abs
  apply le_of_tendsto_of_tendsto' ((cont.tendsto _).comp tail) tendsto_const_nhds
  intro n
  calc
    _ ≤ ∑ i ∈ range n, l1 (z^(i+m)/(i+m).factorial) := l1_sum _ _
    _ ≤ ∑ i ∈ range n, c*r^i := sum_le_sum (fun i _ => tail_term hz m i)
    _ ≤ c*(1-r)⁻¹ := sum_le_hasSum _ (fun i _ => mul_nonneg hc (pow_nonneg hr _))
      ((hasSum_geometric_of_lt_one hr hr').mul_left c)
    _ = _ := by rfl

/-- The actual polynomial in the cover has one coefficient per degree after
    summing over character terms, including the derivative variant. -/
theorem weighted_exp_tail_l1 {ι : Type*} (F : Finset ι) (w b : ι → ℂ) (u : ℂ)
    (m : ℕ) (v : ℝ) (hz : ∀ a ∈ F, l1 (u*b a) ≤ v) (h : v<(m:ℝ)+1) :
    l1 ((∑ a ∈ F, w a * Complex.exp (u*b a)) -
      ∑ j ∈ range m, (∑ a ∈ F, w a * b a ^ j / j.factorial) * u^j) ≤
    (∑ a ∈ F, l1 (w a)) * (v^m/(m.factorial : ℝ) / (1-v/((m:ℝ)+1))) := by
  let P (a : ι) := ∑ j ∈ range m, (u*b a)^j / j.factorial
  have eq : (∑ j ∈ range m, (∑ a ∈ F, w a * b a ^ j / j.factorial) * u^j) =
      ∑ a ∈ F, w a * P a := by
    simp only [P, mul_sum, sum_mul, mul_pow]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro j _
    ring
  rw [eq, ← sum_sub_distrib]
  refine (l1_sum _ _).trans ?_
  rw [sum_mul]
  apply sum_le_sum
  intro a ha
  rw [← mul_sub]
  exact (l1_mul ..).trans (mul_le_mul_of_nonneg_left (exp_tail_l1 _ m v (hz a ha) h) (l1_nonneg _))

end BMORRationalExpTail
end

section
namespace BMORRationalBall
open Complex

/-- Rational centers and l1 radii. An integer fixed-point triple is divided
by its common positive denominator once to obtain one of these balls. -/
structure Ball where
  x : ℚ
  y : ℚ
  r : ℚ
deriving DecidableEq

def size (z : ℂ) : ℝ := |z.re|+|z.im|
def center (b : Ball) : ℂ := ⟨b.x,b.y⟩
def Holds (b : Ball) (z : ℂ) : Prop := size (z-center b) ≤ b.r

private theorem size_add (z w : ℂ) : size (z+w) ≤ size z+size w := by
  unfold size
  simp only [add_re,add_im]
  linarith [abs_add_le z.re w.re,abs_add_le z.im w.im]

private theorem size_mul (z w : ℂ) : size (z*w) ≤ size z*size w := by
  unfold size
  simp only [mul_re,mul_im]
  calc
    _ ≤ (|z.re*w.re|+|z.im*w.im|)+(|z.re*w.im|+|z.im*w.re|) :=
      add_le_add (abs_sub _ _) (abs_add_le _ _)
    _ = _ := by simp only [abs_mul]; ring

private theorem size_nonneg (z : ℂ) : 0 ≤ size z := by unfold size; positivity

def addBall (a b : Ball) : Ball := ⟨a.x+b.x,a.y+b.y,a.r+b.r⟩
def mulBall (a b : Ball) : Ball :=
  ⟨a.x*b.x-a.y*b.y,a.x*b.y+a.y*b.x,
    (|a.x|+|a.y|)*b.r+a.r*(|b.x|+|b.y|+b.r)⟩
def containsBall (b c : Ball) : Bool :=
  decide (|b.x-c.x|+|b.y-c.y|+b.r ≤ c.r)

theorem contains_sound {b c : Ball} (h : containsBall b c = true) {z : ℂ}
    (hz : Holds b z) : Holds c z := by
  have hr : |b.x-c.x|+|b.y-c.y|+b.r ≤ c.r := of_decide_eq_true h
  have hreal : size (center b-center c)+(b.r:ℝ) ≤ c.r := by
    unfold size center
    simp only [sub_re,sub_im]
    exact_mod_cast hr
  have hadd := size_add (z-center b) (center b-center c)
  rw [sub_add_sub_cancel] at hadd
  unfold Holds at hz
  exact hadd.trans (by linarith)

theorem add_sound {a b : Ball} {z w : ℂ} (hz : Holds a z) (hw : Holds b w) :
    Holds (addBall a b) (z+w) := by
  have hc : center (addBall a b) = center a+center b := by
    apply Complex.ext <;> simp [center,addBall]
  unfold Holds
  rw [hc,show z+w-(center a+center b) = (z-center a)+(w-center b) by ring]
  have h := size_add (z-center a) (w-center b)
  exact h.trans (by simpa [addBall] using add_le_add hz hw)

theorem mul_sound {a b : Ball} {z w : ℂ} (hz : Holds a z) (hw : Holds b w) :
    Holds (mulBall a b) (z*w) := by
  have hc : center (mulBall a b) = center a * center b := by
    apply Complex.ext <;> simp [center,mulBall,mul_re,mul_im]
  have bound : size w ≤ size (center b) + (b.r:ℝ) := by
    have h := size_add (center b) (w-center b)
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add (le_refl _) hw)
  change size (z*w-center (mulBall a b)) ≤ _
  rw [hc,show z*w-center a*center b = center a*(w-center b)+(z-center a)*w by ring]
  apply (size_add _ _).trans
  apply (add_le_add (size_mul _ _) (size_mul _ _)).trans
  have h₁ := mul_le_mul_of_nonneg_left hw (size_nonneg (center a))
  have h₂ := mul_le_mul hz bound (size_nonneg w) ((size_nonneg _).trans hz)
  convert add_le_add h₁ h₂ using 1 <;> simp [mulBall,size,center]

/-- Round the center down in each coordinate on the dyadic grid. Two
extra units of radius cover both rounding errors. -/
def rounded (p : ℕ) (b : Ball) : Ball :=
  let d : ℚ := 2^p
  ⟨(⌊b.x*d⌋:ℤ)/d,(⌊b.y*d⌋:ℤ)/d,((⌈b.r*d⌉:ℤ)+2)/d⟩

theorem rounded_contains (p : ℕ) (b : Ball) : containsBall b (rounded p b) = true := by
  apply decide_eq_true
  let d : ℚ := 2^p
  have hd : 0<d := by dsimp [d]; positivity
  have coord (x : ℚ) :
      |x-(⌊x*d⌋:ℤ)/d| ≤ 1/d := by
    have hlo : (⌊x*d⌋:ℤ)/d ≤ x := (div_le_iff₀ hd).mpr (Int.floor_le _)
    rw [abs_of_nonneg (sub_nonneg.mpr hlo), sub_le_iff_le_add, ←add_div]
    exact (le_div_iff₀ hd).mpr (by linarith [Int.lt_floor_add_one (x*d)])
  change |b.x-(⌊b.x*d⌋:ℤ)/d|+|b.y-(⌊b.y*d⌋:ℤ)/d|+b.r ≤ ((⌈b.r*d⌉:ℤ)+2)/d
  apply (add_le_add (add_le_add (coord _) (coord _)) (le_refl _)).trans
  have hb : b.r ≤ (⌈b.r*d⌉:ℤ)/d := (le_div_iff₀ hd).mpr (Int.le_ceil _)
  linarith [show (1:ℚ)/d+1/d+(⌈b.r*d⌉:ℤ)/d=((⌈b.r*d⌉:ℤ)+2)/d by ring]

theorem rounded_mul_sound {a b : Ball} {z w : ℂ} (p : ℕ) (ha : Holds a z) (hb : Holds b w) :
    Holds (rounded p (mulBall a b)) (z*w) :=
  contains_sound (rounded_contains p _) (mul_sound ha hb)

end BMORRationalBall
end

section
namespace BMORLogEvaluator
open Finset BMORRationalBall

def ratio (m : ℚ) := (m-1)/(m+1)
def approx (t : ℚ) : ℚ := 2 * ∑ j ∈ range 41, t^(2*j+1)/(2*j+1)
def radius (t : ℚ) : ℚ := 2*t^83/(1-t^2)

private theorem approx_cast (t : ℚ) :
    ((approx t : ℚ) : ℝ) = BMORRationalExpLog.logTaylor41 (t:ℝ) := by
  unfold approx BMORRationalExpLog.logTaylor41
  push_cast
  rfl

private theorem reduced {m : ℚ} (hl : 1≤m) (hu : m≤2) :
    |Real.log (m:ℝ) - (approx (ratio m):ℝ)| ≤ (radius (ratio m):ℝ) := by
  have h := BMORRationalExpLog.reduced_log_error (m:=(m:ℝ)) (by exact_mod_cast hl) (by exact_mod_cast hu)
  rw [approx_cast]
  simpa [ratio,radius] using h

/-- Choose k with 2^k <= n <= 2^(k+1). The output uses the same 104-bit
fixed-point grid as the complex disk checks. -/
def logBall (n k : ℕ) : Ball :=
  let m : ℚ := (n:ℚ)/2^k
  rounded 104 ⟨k*approx (ratio 2)+approx (ratio m),0,k*radius (ratio 2)+radius (ratio m)⟩

theorem logBall_sound {n k : ℕ} (hl : 2^k ≤ n) (hu : n ≤ 2^(k+1)) :
    Holds (logBall n k) ((Real.log (n:ℝ) : ℝ):ℂ) := by
  let m : ℚ := (n:ℚ)/2^k
  have pos : (0:ℚ)<2^k := by positivity
  have lm : 1≤m := by
    apply (le_div_iff₀ pos).mpr
    simpa using (show (2:ℚ)^k≤(n:ℚ) by exact_mod_cast hl)
  have um : m≤2 := by
    apply (div_le_iff₀ pos).mpr
    have h : (n:ℚ)≤2^(k+1) := by exact_mod_cast hu
    simpa [pow_succ,mul_comm] using h
  have l2 := reduced (m:=2) (by norm_num) (by norm_num)
  have l := reduced lm um
  have hm : 0<(m:ℝ) := by exact_mod_cast (by linarith : 0<m)
  have idn : (n:ℝ)=(2:ℝ)^k*(m:ℝ) := by dsimp [m]; push_cast; field_simp
  have logn : Real.log (n:ℝ) = k * Real.log 2 + Real.log (m:ℝ) := by
    rw [idn,Real.log_mul (by positivity) hm.ne',Real.log_pow]
  apply contains_sound (rounded_contains 104 _)
  change |Real.log (n:ℝ)-((k*approx (ratio 2)+approx (ratio m):ℚ):ℝ)| + |(0:ℝ)-0| ≤
    ((k*radius (ratio 2)+radius (ratio m):ℚ):ℝ)
  rw [logn]
  push_cast
  simp only [sub_self,abs_zero,add_zero]
  have q := abs_add_le ((k:ℝ)*(Real.log 2 - (approx (ratio 2):ℝ)))
    (Real.log (m:ℝ) - (approx (ratio m):ℝ))
  rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤k)] at q
  convert q.trans (add_le_add (mul_le_mul_of_nonneg_left l2 (by positivity : (0:ℝ)≤k)) l) using 1 <;> push_cast <;> ring_nf

/-- One concrete nonlinear datum used to encode the period 13. -/
theorem log13_check : Holds ⟨256494935746/100000000000,0,1/100000000000⟩
    ((Real.log 13 : ℝ):ℂ) := by
  have h := logBall_sound (n:=13) (k:=3) (by decide) (by decide)
  apply contains_sound (b:=logBall 13 3) _ (by simpa using h)
  decide +kernel

end BMORLogEvaluator
end

section
namespace BMORRationalBallExp
open BMORRationalBall BMORRationalExpLog Finset Complex

def point (q : ℚ) : Ball := ⟨q,0,0⟩

theorem point_sound (q : ℚ) : Holds (point q) (q : ℂ) := by
  have h : center (point q) = (q : ℂ) := by
    apply Complex.ext <;> simp [point,center]
  simp only [Holds,h,sub_self]
  simp [size,point]

def timesRat (a : Ball) (q : ℚ) : Ball := rounded 104 (mulBall a (point q))

theorem timesRat_sound (a : Ball) (q : ℚ) (z : ℂ) (ha : Holds a z) :
    Holds (timesRat a q) (z*(q : ℂ)) :=
  rounded_mul_sound 104 ha (point_sound _)

def terms (b : Ball) : ℕ → Ball × Ball
  | 0 => (point 1,point 1)
  | n+1 =>
    let (prev,acc) := terms b n
    let next := timesRat (rounded 104 (mulBall prev b)) (1/((n:ℚ)+1))
    (next,addBall acc next)

theorem terms_sound (b : Ball) {z : ℂ} (hb : Holds b z) (n : ℕ) :
    Holds (terms b n).1 (z^n/n.factorial) ∧
    Holds (terms b n).2 (∑ j ∈ range (n+1), z^j/j.factorial) := by
  induction n with
  | zero => simpa [terms] using And.intro (point_sound 1) (point_sound 1)
  | succ n ih =>
    have h := timesRat_sound _ (1/((n:ℚ)+1)) _ (rounded_mul_sound 104 ih.1 hb)
    have hsucc : z^n / (n.factorial:ℂ) * z * (((1/((n:ℚ)+1)):ℚ):ℂ) =
        z^(n+1)/(n+1).factorial := by
      simp only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast,pow_succ,
        Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hsucc] at h
    exact ⟨h, by simpa only [terms, sum_range_succ (fun j => z^j/j.factorial) (n+1)]
      using add_sound ih.2 h⟩

/-- One grid unit rounds the certified 32nd-degree remainder upwards. -/
def withTaylorError (a : Ball) : Ball := {a with r := a.r + 1/(2^104)}

theorem withTaylorError_sound (a : Ball) (z : ℂ) (hz : ‖z‖≤1)
    (ha : Holds a (expTaylor32 z)) : Holds (withTaylorError a) (Complex.exp z) := by
  have e := exp_error_l1 z hz
  have hh := BMORRationalExpTail.l1_add (Complex.exp z-expTaylor32 z) (expTaylor32 z-center a)
  rw [sub_add_sub_cancel] at hh
  have bd : (2:ℝ)/(Nat.factorial 33:ℝ) ≤ (((1/(2^104)):ℚ):ℝ) := by norm_num [Nat.factorial]
  change BMORRationalExpTail.l1 (Complex.exp z - center a) ≤ ((a.r+1/(2^104):ℚ):ℝ)
  rw [Rat.cast_add]
  exact hh.trans (add_le_add (e.trans bd) ha) |>.trans (by linarith)

def squareN : ℕ → Ball → Ball
  | 0, a => a
  | n+1, a => let prev := squareN n a; rounded 104 (mulBall prev prev)

theorem squareN_sound (n : ℕ) {a : Ball} {z : ℂ} (ha : Holds a z) :
    Holds (squareN n a) (z^(2^n:ℕ)) := by
  induction n with
  | zero => simpa [squareN] using ha
  | succ n ih =>
    simpa only [squareN, pow_succ 2 n, pow_mul, pow_two] using rounded_mul_sound 104 ih ih

def evaluate (a : Ball) : Ball :=
  let b := timesRat a (1/32)
  squareN 5 (withTaylorError (terms b 32).2)

theorem evaluate_sound (a : Ball) (z : ℂ) (ha : Holds a z) (hz : ‖z‖≤32) :
    Holds (evaluate a) (Complex.exp z) := by
  have reduced : Holds (timesRat a (1/32)) (z/32) := by
    convert timesRat_sound a (1/32) z ha using 1
    push_cast
    ring
  have hnorm : ‖z/32‖≤1 := by
    rw [norm_div]
    norm_num
    linarith
  have hP := (terms_sound _ reduced 32).2
  have h := squareN_sound 5 (withTaylorError_sound _ _ hnorm hP)
  unfold evaluate
  convert h using 1
  rw [← five_squares z]
  ring

def inRange (a : Ball) : Bool := decide (|a.x|+|a.y|+a.r≤32)

theorem evaluate_sound_checked (a : Ball) (z : ℂ) (ha : Holds a z) (h : inRange a = true) :
    Holds (evaluate a) (Complex.exp z) := by
  apply evaluate_sound _ _ ha
  have hq : |a.x|+|a.y|+a.r≤32 := of_decide_eq_true h
  have hr : size (center a) + (a.r:ℝ) ≤ 32 := by
    change |(a.x:ℝ)|+|(a.y:ℝ)|+(a.r:ℝ)≤32
    exact_mod_cast hq
  have hsize := BMORRationalExpTail.l1_add (center a) (z-center a)
  rw [add_sub_cancel] at hsize
  have htotal : size z ≤ 32 := hsize.trans ((add_le_add (le_refl _) ha).trans hr)
  apply le_trans _ htotal
  unfold size
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith only [Complex.sq_norm_sub_sq_re z, sq_abs z.re, sq_abs z.im,
    mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)]

/-- A nonzero-input kernel check enclosing exp(1) within 10⁻¹¹ of 2.718281828459. -/
theorem one_check :
    containsBall (evaluate (point 1)) ⟨2718281828459/10^12,0,1/10^11⟩ = true := by
  decide +kernel

theorem exp_one_enclosed : Holds ⟨2718281828459/10^12,0,1/10^11⟩ (Complex.exp 1) := by
  apply contains_sound one_check
  apply evaluate_sound
  · simpa using point_sound 1
  · norm_num

theorem imaginary_unit_check :
    containsBall (evaluate ⟨0,1,0⟩) ⟨540302305868/10^12,841470984808/10^12,1/10^11⟩ = true := by
  decide +kernel

theorem exp_I_enclosed :
    Holds ⟨540302305868/10^12,841470984808/10^12,1/10^11⟩ (Complex.exp Complex.I) := by
  apply contains_sound imaginary_unit_check
  apply evaluate_sound_checked
  · change |(Complex.I - center ⟨0,1,0⟩).re| + |(Complex.I - center ⟨0,1,0⟩).im| ≤ (0:ℝ)
    norm_num [center,sub_re,sub_im]
  · decide +kernel

end BMORRationalBallExp
end

section
namespace BMORRationalCover
open Complex Set

/-- Closed rational rectangle, using inclusive boundaries on both sides of every split. -/
structure Box where
  l : ℚ
  r : ℚ
  b : ℚ
  t : ℚ
deriving Repr, DecidableEq

def Box.region (A : Box) : Set ℂ :=
  {z | (A.l:ℝ)≤z.re ∧ z.re≤A.r ∧ (A.b:ℝ)≤z.im ∧ z.im≤A.t}

def Box.cx (A : Box) := (A.l+A.r)/2
def Box.cy (A : Box) := (A.b+A.t)/2
noncomputable def Box.center (A : Box) : ℂ := ⟨A.cx,A.cy⟩
def Box.radius (A : Box) := (A.r-A.l + (A.t-A.b))/2
def Box.left (A : Box) : Box := { A with r := A.cx }
def Box.right (A : Box) : Box := { A with l := A.cx }
def Box.bottom (A : Box) : Box := { A with t := A.cy }
def Box.top (A : Box) : Box := { A with b := A.cy }

def Box.inside (A H : Box) := H.l≤A.l ∧ A.r≤H.r ∧ H.b≤A.b ∧ A.t≤H.t
instance (A H : Box) : Decidable (A.inside H) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem Box.inside_sound {A H : Box} (h : A.inside H) : A.region ⊆ H.region := by
  intro z hz
  exact ⟨(by exact_mod_cast h.1 : (H.l:ℝ)≤A.l).trans hz.1,
    hz.2.1.trans (by exact_mod_cast h.2.1),
    (by exact_mod_cast h.2.2.1 : (H.b:ℝ)≤A.b).trans hz.2.2.1, hz.2.2.2.trans (by exact_mod_cast h.2.2.2)⟩

theorem Box.mem_left_or_right (A : Box) {z : ℂ} (hz : z∈A.region) :
    z∈A.left.region ∨ z∈A.right.region := by
  rcases le_total z.re (A.cx:ℝ) with h|h
  · exact Or.inl ⟨hz.1,h,hz.2.2⟩
  · exact Or.inr ⟨h,hz.2.1,hz.2.2⟩

theorem Box.mem_bottom_or_top (A : Box) {z : ℂ} (hz : z∈A.region) :
    z∈A.bottom.region ∨ z∈A.top.region := by
  rcases le_total z.im (A.cy:ℝ) with h|h
  · exact Or.inl ⟨hz.1,hz.2.1,hz.2.2.1,h⟩
  · exact Or.inr ⟨hz.1,hz.2.1,h,hz.2.2.2⟩

theorem Box.center_mem (A : Box) {z : ℂ} (hz : z∈A.region) : A.center∈A.region := by
  rcases hz with ⟨hl,hr,hb,ht⟩
  simp only [region, center, cx, cy, Set.mem_ofPred_eq, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem Box.norm_sub_center (A : Box) {z : ℂ} (hz : z∈A.region) :
    ‖z-A.center‖ ≤ (A.radius:ℝ) := by
  rcases hz with ⟨hl,hr,hb,ht⟩
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, center, cx, cy, radius]
  push_cast
  have h₁ : |z.re-((A.l:ℝ)+A.r)/2| ≤ ((A.r:ℝ)-A.l)/2 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have h₂ : |z.im-((A.b:ℝ)+A.t)/2| ≤ ((A.t:ℝ)-A.b)/2 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  linarith

theorem Box.convex (A : Box) : Convex ℝ A.region :=
  (convex_halfSpace_re_ge (A.l:ℝ)).inter ((convex_halfSpace_re_le (A.r:ℝ)).inter
    ((convex_halfSpace_im_ge (A.b:ℝ)).inter (convex_halfSpace_im_le (A.t:ℝ))))

/-- A lower bound for the approximant at the center, its local slope bound, and
a uniform error bound between the target and the approximant. -/
structure Bounds where
  lower : ℚ
  slope : ℚ
  err : ℚ
deriving Repr

def Bounds.passes (d : Bounds) (A : Box) :=
  decide (0≤d.slope ∧ 0≤d.err ∧ d.slope*A.radius+d.err<d.lower)

/-- Analytic obligations at an exclusion leaf; the approximant may differ across leaves. -/
def LeafFacts (f : ℂ → ℂ) (A : Box) (d : Bounds) := ∃ p : ℂ → ℂ,
  (d.lower:ℝ) ≤ ‖p A.center‖ ∧
  (∀ z ∈ A.region, ‖p z-p A.center‖ ≤ (d.slope:ℝ)*‖z-A.center‖) ∧
  ∀ z ∈ A.region, ‖f z-p z‖ ≤ (d.err:ℝ)

theorem LeafFacts.of_deriv {f p : ℂ → ℂ} {A : Box} {d : Bounds}
    (hl : (d.lower:ℝ) ≤ ‖p A.center‖) (hd : ∀ z∈A.region, DifferentiableAt ℂ p z)
    (hb : ∀ z∈A.region, ‖deriv p z‖≤(d.slope:ℝ))
    (he : ∀ z∈A.region, ‖f z-p z‖≤(d.err:ℝ)) : LeafFacts f A d := by
  refine ⟨p,hl,?_,he⟩
  intro z hz
  exact A.convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivAt.hasDerivWithinAt) hb (A.center_mem hz) hz

theorem excludes {f : ℂ → ℂ} {A : Box} {d : Bounds} (hc : d.passes A = true)
    (hf : LeafFacts f A d) {z : ℂ} (hz : z∈A.region) : f z≠0 := by
  intro hzero
  obtain ⟨p,hlo,hs,he⟩ := hf
  obtain ⟨hs₀,_,hlt⟩ := of_decide_eq_true hc
  have hlt' : (d.slope:ℝ)*A.radius+d.err < d.lower := by exact_mod_cast hlt
  have h₁ := (hs z hz).trans (mul_le_mul_of_nonneg_left (A.norm_sub_center hz)
    (by exact_mod_cast hs₀ : 0≤(d.slope:ℝ)))
  have h₂ := he z hz
  rw [hzero,zero_sub,norm_neg] at h₂
  have h₃ := norm_le_norm_add_norm_sub (p z) (p A.center)
  linarith

inductive Tree where
  | exclude (d : Bounds)
  | candidate
  | vertical (left right : Tree)
  | horizontal (bottom top : Tree)
deriving Repr

def Tree.check (hint : Option Box) (A : Box) : Tree → Bool
  | .exclude d => d.passes A
  | .candidate => hint.any fun H => decide (A.inside H)
  | .vertical l r => l.check hint A.left && r.check hint A.right
  | .horizontal b t => b.check hint A.bottom && t.check hint A.top

def Tree.facts (f : ℂ → ℂ) (A : Box) : Tree → Prop
  | .exclude d => LeafFacts f A d
  | .candidate => True
  | .vertical l r => l.facts f A.left ∧ r.facts f A.right
  | .horizontal b t => b.facts f A.bottom ∧ t.facts f A.top

theorem Tree.sound {t : Tree} {hint : Option Box} {A : Box} {f : ℂ→ℂ}
    (checked : t.check hint A = true) (facts : t.facts f A) {z : ℂ} (hz : z∈A.region)
    (h0 : f z = 0) : ∃ H, hint = some H ∧ z∈H.region := by
  induction t generalizing A with
  | exclude d => exact False.elim (excludes checked facts hz h0)
  | candidate =>
    cases hint with
    | none => simp [check] at checked
    | some H =>
      refine ⟨H,rfl,Box.inside_sound ?_ hz⟩
      simpa [check] using checked
  | vertical l r il ir =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp checked
    obtain h|h := A.mem_left_or_right hz
    · exact il hl facts.1 h
    · exact ir hr facts.2 h
  | horizontal b t ib it =>
    obtain ⟨hb,ht⟩ := Bool.and_eq_true_iff.mp checked
    obtain h|h := A.mem_bottom_or_top hz
    · exact ib hb facts.1 h
    · exact it ht facts.2 h

def rightStrip : Box := ⟨1/2,1,-2,2⟩
def rootBox (y : ℚ) : Box := ⟨1/2-1/16,1/2+1/16,y-1/16,y+1/16⟩

end BMORRationalCover
end

section
namespace BMORRationalCover.Mod13
open BMORRationalCover
private abbrev E (a s e d : ℕ) : Tree := .exclude ⟨(a:ℚ)/d,(s:ℚ)/d,(e:ℚ)/d⟩
private abbrev c : Tree := .candidate
private abbrev H := Tree.horizontal
private abbrev V := Tree.vertical

def tree1 : Tree :=
(H (H (H (V (H (V (E 128 547 9 256) (H (E 98 547 9 256) (E 121 547 9 256))) (E 160 547 9 256)) (H (V (H (E 101 547 9 256) (E 113 547 9 256)) (E 125 547 9 256)) (V (E 136 547 9 256) (E 150 547 9 256)))) (V (E 190 371 9 256) (E 192 371 9 256))) (H (E 256 239 9 256) (E 312 175 9 256))) (H (H (E 370 280 9 256) (E 440 427 9 256)) (H (E 509 615 9 256) (E 536 691 9 256))))
theorem checked1 : tree1.check none rightStrip = true := by decide +kernel

def tree2 : Tree :=
(H (H (H (E 325 442 9 256) (E 297 421 9 256)) (H (E 239 337 9 256) (V (E 175 386 9 256) (E 204 386 9 256)))) (H (H (V (E 162 367 9 256) (E 200 367 9 256)) (V (E 214 535 9 256) (E 244 535 9 256))) (H (E 333 558 9 256) (E 457 819 9 256))))
theorem checked2 : tree2.check none rightStrip = true := by decide +kernel

def tree3 : Tree :=
(H (H (H (V (H (V (H (V (E 66 486 9 256) (E 61 486 9 256)) (E 91 486 9 256)) (H (V (E 57 486 9 256) (E 58 486 9 256)) (E 79 486 9 256))) (V (E 125 486 9 256) (E 109 486 9 256))) (H (V (H (E 74 486 9 256) (E 81 486 9 256)) (H (E 94 486 9 256) (E 100 486 9 256))) (V (H (E 91 486 9 256) (E 104 486 9 256)) (E 112 486 9 256)))) (V (E 160 351 9 256) (E 143 351 9 256))) (H (E 195 231 9 256) (E 251 158 9 256))) (H (H (E 308 246 9 256) (E 379 392 9 256)) (H (E 453 571 9 256) (E 491 633 9 256))))
theorem checked3 : tree3.check none rightStrip = true := by decide +kernel

def tree4 : Tree :=
(H (H (H (V (H (V (H (E 73 411 9 256) (E 94 411 9 256)) (E 92 411 9 256)) (E 121 411 9 256)) (H (V (E 102 411 9 256) (E 112 411 9 256)) (E 127 411 9 256))) (E 147 198 9 256)) (H (E 147 202 9 256) (V (E 117 252 9 256) (E 137 252 9 256)))) (H (H (V (H (E 98 349 9 256) (E 133 349 9 256)) (H (E 132 349 9 256) (E 136 349 9 256))) (V (E 208 505 9 256) (H (E 162 505 9 256) (E 198 505 9 256)))) (H (V (E 305 713 9 256) (H (E 230 713 9 256) (E 277 713 9 256))) (V (E 393 831 9 256) (E 380 831 9 256)))))
theorem checked4 : tree4.check none rightStrip = true := by decide +kernel

def tree5 : Tree :=
(H (H (H (E 313 474 9 256) (E 272 389 9 256)) (H (E 208 263 9 256) (E 149 251 9 256))) (H (H (V (H (E 100 268 9 256) (V (E 67 268 9 256) (E 81 268 9 256))) (E 111 268 9 256)) (V (H (V (H (V (E 47 392 9 256) (E 51 392 9 256)) (V (H (E 34 392 9 256) (V (H (E 29 392 9 256) (E 24 392 9 256)) (E 108 1567 34 1024))) (H (E 41 392 9 256) (E 34 392 9 256)))) (H (E 63 392 9 256) (V (E 46 392 9 256) (E 56 392 9 256)))) (V (H (V (H (V (H (V (E 20 392 9 256) (E 72 1567 34 1024)) (V (H (E 16 392 9 256) (V (E 55 1567 34 1024) (E 208 6267 133 4096))) (H (E 61 1567 34 1024) (V (H (E 13 392 9 256) (E 49 1567 34 1024)) (E 14 392 9 256))))) (H (E 87 1567 34 1024) (V (H (E 17 392 9 256) (E 16 392 9 256)) (E 19 392 9 256)))) (V (H (V (H (V (H (E 47 1567 34 1024) c) (H (V (E 44 1567 34 1024) (E 171 6267 133 4096)) c)) c) (H (V (H (E 183 6267 133 4096) c) (H (E 51 1567 34 1024) c)) c)) c) (H (V (H (E 231 6267 133 4096) c) (H (E 17 392 9 256) c)) c))) (H (V (H (E 27 392 9 256) (E 23 392 9 256)) (E 30 392 9 256)) (V (H (V (E 19 392 9 256) (E 21 392 9 256)) (V (H (E 16 392 9 256) (E 60 1567 34 1024)) (E 74 1567 34 1024))) (H (E 25 392 9 256) (E 22 392 9 256))))) (V (H c (V (H (V (H (V (H c (E 13 392 9 256)) (E 54 1567 34 1024)) (E 16 392 9 256)) (H (E 59 1567 34 1024) (E 18 392 9 256))) (E 22 392 9 256)) (H (V (E 72 1567 34 1024) (E 19 392 9 256)) (E 25 392 9 256)))) (H (V (H (V (H (V (H (E 13 392 9 256) (E 49 1567 34 1024)) (E 14 392 9 256)) (V (H (E 183 6267 133 4096) (V (E 170 6267 133 4096) (E 44 1567 34 1024))) (H (E 51 1567 34 1024) (E 48 1567 34 1024)))) (H (E 16 392 9 256) (E 59 1567 34 1024))) (V (H (V (E 209 6267 133 4096) (E 55 1567 34 1024)) (E 16 392 9 256)) (H (E 60 1567 34 1024) (E 18 392 9 256)))) (H (V (E 73 1567 34 1024) (E 21 392 9 256)) (V (E 72 1567 34 1024) (E 19 392 9 256)))) (V (H (E 87 1567 34 1024) (E 28 392 9 256)) (E 111 1567 34 1024))))) (H (V (H (E 38 392 9 256) (V (E 29 392 9 256) (E 35 392 9 256))) (E 183 1567 34 1024)) (V (H (V (H (E 25 392 9 256) (E 23 392 9 256)) (E 30 392 9 256)) (V (E 30 392 9 256) (E 32 392 9 256))) (H (E 38 392 9 256) (E 36 392 9 256)))))) (H (V (H (E 79 392 9 256) (E 69 392 9 256)) (E 90 392 9 256)) (V (H (E 60 392 9 256) (V (E 47 392 9 256) (E 58 392 9 256))) (H (E 79 392 9 256) (E 74 392 9 256)))))) (H (V (H (V (H (V (H (V (H (E 28 531 9 256) (E 36 531 9 256)) (E 35 531 9 256)) (E 48 531 9 256)) (H (V (E 38 531 9 256) (E 41 531 9 256)) (E 53 531 9 256))) (E 1195 8488 133 4096)) (H (V (H (E 44 531 9 256) (E 58 531 9 256)) (H (E 48 531 9 256) (E 61 531 9 256))) (E 81 531 9 256))) (V (E 128 531 9 256) (E 129 531 9 256))) (H (V (H (V (H (E 51 531 9 256) (E 64 531 9 256)) (E 60 531 9 256)) (E 84 531 9 256)) (H (V (E 65 531 9 256) (E 76 531 9 256)) (E 85 531 9 256))) (V (E 127 531 9 256) (E 123 531 9 256)))) (V (H (E 830 3182 34 1024) (E 293 796 9 256)) (H (V (E 190 796 9 256) (E 178 796 9 256)) (E 244 796 9 256))))))
theorem checked5 : tree5.check (some (rootBox (113/128))) rightStrip = true := by decide +kernel

def tree6 : Tree :=
(H (H (H (E 270 412 9 256) (E 237 338 9 256)) (H (E 185 328 9 256) (V (E 136 289 9 256) (E 162 289 9 256)))) (H (H (V (E 136 289 9 256) (E 162 289 9 256)) (E 185 328 9 256)) (H (E 237 338 9 256) (E 270 412 9 256))))
theorem checked6 : tree6.check none rightStrip = true := by decide +kernel

def tree7 : Tree :=
(H (H (H (V (H (E 293 796 9 256) (E 830 3182 34 1024)) (H (E 244 796 9 256) (V (E 190 796 9 256) (E 178 796 9 256)))) (V (H (V (E 128 531 9 256) (E 129 531 9 256)) (V (H (E 1195 8488 133 4096) (V (H (E 48 531 9 256) (V (H (E 36 531 9 256) (E 28 531 9 256)) (E 35 531 9 256))) (H (E 53 531 9 256) (V (E 38 531 9 256) (E 41 531 9 256))))) (H (E 81 531 9 256) (V (H (E 58 531 9 256) (E 44 531 9 256)) (H (E 61 531 9 256) (E 48 531 9 256)))))) (H (V (E 127 531 9 256) (E 123 531 9 256)) (V (H (E 84 531 9 256) (V (H (E 64 531 9 256) (E 51 531 9 256)) (E 60 531 9 256))) (H (E 85 531 9 256) (V (E 65 531 9 256) (E 76 531 9 256))))))) (H (V (H (V (H (V (H (V (H (E 22 392 9 256) (V (H (E 16 392 9 256) (V (H (E 13 392 9 256) c) (E 54 1567 34 1024))) (H (E 18 392 9 256) (E 59 1567 34 1024)))) (H (E 25 392 9 256) (V (E 72 1567 34 1024) (E 19 392 9 256)))) c) (H (V (H (E 28 392 9 256) (E 87 1567 34 1024)) (E 111 1567 34 1024)) (V (H (V (H (E 16 392 9 256) (V (E 209 6267 133 4096) (E 55 1567 34 1024))) (H (E 18 392 9 256) (E 60 1567 34 1024))) (V (H (V (H (V (E 170 6267 133 4096) (E 44 1567 34 1024)) (E 183 6267 133 4096)) (H (E 48 1567 34 1024) (E 51 1567 34 1024))) (V (H (E 49 1567 34 1024) (E 13 392 9 256)) (E 14 392 9 256))) (H (E 59 1567 34 1024) (E 16 392 9 256)))) (H (V (E 72 1567 34 1024) (E 19 392 9 256)) (V (E 73 1567 34 1024) (E 21 392 9 256)))))) (V (H (V (H c (V (H c (V (H c (E 47 1567 34 1024)) (H c (V (E 44 1567 34 1024) (E 171 6267 133 4096))))) (H c (V (H c (E 183 6267 133 4096)) (H c (E 51 1567 34 1024)))))) (H c (V (H c (E 231 6267 133 4096)) (H c (E 17 392 9 256))))) (V (H (V (H (V (E 55 1567 34 1024) (E 208 6267 133 4096)) (E 16 392 9 256)) (H (V (H (E 49 1567 34 1024) (E 13 392 9 256)) (E 14 392 9 256)) (E 61 1567 34 1024))) (V (E 20 392 9 256) (E 72 1567 34 1024))) (H (V (H (E 16 392 9 256) (E 17 392 9 256)) (E 19 392 9 256)) (E 87 1567 34 1024)))) (H (V (H (V (H (E 60 1567 34 1024) (E 16 392 9 256)) (E 74 1567 34 1024)) (V (E 19 392 9 256) (E 21 392 9 256))) (H (E 22 392 9 256) (E 25 392 9 256))) (V (H (E 23 392 9 256) (E 27 392 9 256)) (E 30 392 9 256))))) (H (V (H (V (E 30 392 9 256) (E 32 392 9 256)) (V (H (E 23 392 9 256) (E 25 392 9 256)) (E 30 392 9 256))) (H (E 36 392 9 256) (E 38 392 9 256))) (V (H (V (E 29 392 9 256) (E 35 392 9 256)) (E 38 392 9 256)) (E 183 1567 34 1024)))) (V (H (V (H (V (H (E 24 392 9 256) (E 29 392 9 256)) (E 108 1567 34 1024)) (E 34 392 9 256)) (H (E 34 392 9 256) (E 41 392 9 256))) (V (E 47 392 9 256) (E 51 392 9 256))) (H (V (E 46 392 9 256) (E 56 392 9 256)) (E 63 392 9 256)))) (H (V (H (V (E 47 392 9 256) (E 58 392 9 256)) (E 60 392 9 256)) (H (E 74 392 9 256) (E 79 392 9 256))) (V (H (E 69 392 9 256) (E 79 392 9 256)) (E 90 392 9 256)))) (V (H (V (E 67 268 9 256) (E 81 268 9 256)) (E 100 268 9 256)) (E 111 268 9 256)))) (H (H (E 149 251 9 256) (E 208 263 9 256)) (H (E 272 389 9 256) (E 313 474 9 256))))
theorem checked7 : tree7.check (some (rootBox (-113/128))) rightStrip = true := by decide +kernel

def tree8 : Tree :=
(H (H (H (V (E 393 831 9 256) (E 380 831 9 256)) (V (E 305 713 9 256) (H (E 277 713 9 256) (E 230 713 9 256)))) (H (V (E 208 505 9 256) (H (E 198 505 9 256) (E 162 505 9 256))) (V (H (E 133 349 9 256) (E 98 349 9 256)) (H (E 136 349 9 256) (E 132 349 9 256))))) (H (H (V (E 117 252 9 256) (E 137 252 9 256)) (E 147 202 9 256)) (H (E 147 198 9 256) (V (H (E 121 411 9 256) (V (H (E 94 411 9 256) (E 73 411 9 256)) (E 92 411 9 256))) (H (E 127 411 9 256) (V (E 102 411 9 256) (E 112 411 9 256)))))))
theorem checked8 : tree8.check none rightStrip = true := by decide +kernel

def tree9 : Tree :=
(H (H (H (E 491 633 9 256) (E 453 571 9 256)) (H (E 379 392 9 256) (E 308 246 9 256))) (H (H (E 251 158 9 256) (E 195 231 9 256)) (H (V (E 160 351 9 256) (E 143 351 9 256)) (V (H (V (E 125 486 9 256) (E 109 486 9 256)) (V (H (E 91 486 9 256) (V (E 66 486 9 256) (E 61 486 9 256))) (H (E 79 486 9 256) (V (E 57 486 9 256) (E 58 486 9 256))))) (H (V (H (E 104 486 9 256) (E 91 486 9 256)) (E 112 486 9 256)) (V (H (E 81 486 9 256) (E 74 486 9 256)) (H (E 100 486 9 256) (E 94 486 9 256))))))))
theorem checked9 : tree9.check none rightStrip = true := by decide +kernel

def tree10 : Tree :=
(H (H (H (E 457 819 9 256) (E 333 558 9 256)) (H (V (E 214 535 9 256) (E 244 535 9 256)) (V (E 162 367 9 256) (E 200 367 9 256)))) (H (H (V (E 175 386 9 256) (E 204 386 9 256)) (E 239 337 9 256)) (H (E 297 421 9 256) (E 325 442 9 256))))
theorem checked10 : tree10.check none rightStrip = true := by decide +kernel

def tree11 : Tree :=
(H (H (H (E 536 691 9 256) (E 509 615 9 256)) (H (E 440 427 9 256) (E 370 280 9 256))) (H (H (E 312 175 9 256) (E 256 239 9 256)) (H (V (E 190 371 9 256) (E 192 371 9 256)) (V (H (E 160 547 9 256) (V (E 128 547 9 256) (H (E 121 547 9 256) (E 98 547 9 256)))) (H (V (E 136 547 9 256) (E 150 547 9 256)) (V (H (E 113 547 9 256) (E 101 547 9 256)) (E 125 547 9 256)))))))
theorem checked11 : tree11.check none rightStrip = true := by decide +kernel

end BMORRationalCover.Mod13
namespace BMORRationalCover.Mod13
open BMORRationalCover

/-- The indices 0,...,10 store the original nonprincipal exponents 1,...,11. -/
def proofTree (k : Fin 11) : Tree :=
  match k.val with
  | 0 => tree1 | 1 => tree2 | 2 => tree3 | 3 => tree4 | 4 => tree5 | 5 => tree6
  | 6 => tree7 | 7 => tree8 | 8 => tree9 | 9 => tree10 | _ => tree11

def hint (k : Fin 11) : Option Box :=
  if k.val=4 then some (rootBox (113/128)) else
  if k.val=6 then some (rootBox (-113/128)) else none

theorem check_all (k : Fin 11) : (proofTree k).check (hint k) rightStrip = true := by
  fin_cases k
  all_goals first | exact checked1 | exact checked2 | exact checked3 | exact checked4 | exact checked5 |
            exact checked6 | exact checked7 | exact checked8 | exact checked9 | exact checked10 | exact checked11

/-- To conclude the cover for its L-function, provide the analytic enclosure premises
only on exclusion leaves. The closed-boundary geometry and every rational acceptance test are proved. -/
theorem cover (k : Fin 11) {f : ℂ → ℂ} (h : (proofTree k).facts f rightStrip) {z : ℂ}
    (hl : 1/2 ≤ z.re) (hr : z.re ≤ 1) (hb : -2 ≤ z.im) (ht : z.im ≤ 2) (hz : f z=0) :
    ∃ H, hint k=some H ∧ z∈H.region := by
  apply Tree.sound (check_all k) h _ hz
  change ((1/2:ℚ):ℝ) ≤ z.re ∧ z.re≤((1:ℚ):ℝ) ∧ ((-2:ℚ):ℝ)≤z.im ∧ z.im≤((2:ℚ):ℝ)
  norm_num
  exact ⟨hl,hr,hb,ht⟩

end BMORRationalCover.Mod13
end

section
namespace BMORAPLogPrimitive
open Finset Real

noncomputable def primitive (q x : ℝ) : ℝ := (x/q-1/2)*log x-x/q

/-- A logarithmic step has a positive error whose upper bound telescopes. -/
theorem step {q x : ℝ} (hq : 0<q) (hx : 0<x) :
    0≤primitive q (x+q)-primitive q x-log x ∧
    primitive q (x+q)-primitive q x-log x ≤ q/4*(1/x-1/(x+q)) := by
  let u := q/(2*x+q)
  have hp : 0<2*x+q := by linarith
  have hu : 0<u := div_pos hq hp
  have hu' : u<1 := (div_lt_one hp).2 (by linarith)
  have hv : 1-u≠0 := by linarith
  have hv' : 1-u^2≠0 := by nlinarith [mul_pos (by linarith : 0<1-u) (by linarith : 0<1+u)]
  have ratio : (1+u)/(1-u)=(x+q)/x := by
    apply (div_eq_iff hv).2
    dsimp [u];field_simp;ring
  have L := Real.sum_range_le_log_div hu.le hu' 1
  have U := Real.log_div_le_sum_range_add hu.le hu' 1
  norm_num [ratio] at L U
  have hp' : 0<x+q := by linarith
  have eq : primitive q (x+q)-primitive q x-log x =
      log ((x+q)/x)/(2*u)-1 := by
    rw [log_div hp'.ne' hx.ne']
    simp only [primitive,u]
    field_simp
    <;> ring
  have budget : u^2/(1-u^2)=q/4*(1/x-1/(x+q)) := by
    apply (div_eq_iff hv').2
    dsimp [u]
    field_simp
    <;> ring
  rw [eq,←budget]
  have pos : 0<2*u := by positivity
  constructor
  · have h : 1≤log ((x+q)/x)/(2*u) := (le_div_iff₀ pos).2 (by linarith)
    linarith
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ pos).2
    calc
      _ ≤ 2*u+2*(u^3/(1-u^2)) := by linarith
      _ = _ := by ring

/-- All terms of an arithmetic progression are controlled by two real logs. -/
theorem prefix_bound {q x : ℝ} (hq : 0<q) (hx : 0<x) (n : ℕ) :
    let y := x+q*n
    0≤primitive q y-primitive q x-∑ i ∈ range n,log (x+q*i) ∧
    primitive q y-primitive q x-∑ i ∈ range n,log (x+q*i) ≤ q/4*(1/x-1/y) := by
  dsimp only
  induction n with
  | zero => simp
  | succ n ih =>
    have h := step hq (x:=x+q*n) (by positivity)
    rw [Nat.cast_succ,mul_add,mul_one,←add_assoc,sum_range_succ]
    constructor
    · linarith only [ih.1,h.1]
    · linarith only [ih.2,h.2]

#print axioms prefix_bound
end BMORAPLogPrimitive
end

section
namespace BMORFiniteLogConstants
open Finset

def lower (u : ℚ) (n : ℕ) : ℚ :=
  2*∑ i ∈ range n, u^(2*i+1)/((2*i+1:ℕ):ℚ)

theorem gap (u : ℚ) (hu₀ : 0≤u) (hu₁ : u<1) (n : ℕ) :
    0≤Real.log ((1+(u:ℝ))/(1-u))-(lower u n:ℝ) ∧
    Real.log ((1+(u:ℝ))/(1-u))-(lower u n:ℝ) ≤
      2*((u:ℝ)^(2*n+1)/(1-u^2)) := by
  have pl := Real.sum_range_le_log_div (show 0≤(u:ℝ) by exact_mod_cast hu₀)
    (show (u:ℝ)<1 by exact_mod_cast hu₁) n
  have pu := Real.log_div_le_sum_range_add (show 0≤(u:ℝ) by exact_mod_cast hu₀)
    (show (u:ℝ)<1 by exact_mod_cast hu₁) n
  have eq : (lower u n : ℝ) =
      2*∑ i ∈ range n,(u:ℝ)^(2*i+1)/(2*i+1) := by unfold lower;push_cast;rfl
  rw [eq];constructor <;> linarith

def center (e : ℕ) : ℚ := e*lower (1/3) 110 + lower (1/5) 110

set_option maxRecDepth 8192 in
theorem center_error (e : ℕ) (he : e≤46) :
    |Real.log (3*(2:ℝ)^e/2)-(center e:ℝ)| ≤ 1/10^(42:ℕ) := by
  have h₂ := gap (1/3) (by norm_num) (by norm_num) 110
  have h₃ := gap (1/5) (by norm_num) (by norm_num) 110
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,
    show (1+(1/3:ℝ))/(1-1/3)=2 by norm_num,
    show (1+(1/5:ℝ))/(1-1/5)=3/2 by norm_num] at h₂ h₃
  have e₂ : Real.log 2-(lower (1/3) 110 : ℝ)≤1/10^(45:ℕ) := h₂.2.trans (by norm_num)
  have e₃ : Real.log (3/2)-(lower (1/5) 110 : ℝ)≤1/10^(45:ℕ) := h₃.2.trans (by norm_num)
  rw [show 3*(2:ℝ)^e/2=2^e*(3/2) by ring,Real.log_mul (by positivity) (by norm_num),Real.log_pow]
  unfold center;push_cast
  have en : (e:ℝ)≤46 := by exact_mod_cast he
  have H := mul_le_mul_of_nonneg_left e₂ (Nat.cast_nonneg e)
  have L := mul_nonneg (Nat.cast_nonneg e) h₂.1
  apply abs_le.mpr
  constructor <;> linarith

#print axioms gap
#print axioms center_error
end BMORFiniteLogConstants
end

section
namespace BMORQ3LargeLogs
open BMORFiniteLogConstants
set_option maxRecDepth 8192
private theorem tight (u a : ℚ) (h₀ : 0≤u) (h₁ : u<1)
    (hL : a≤lower u 16) (hU : lower u 16+2*(u^33/(1-u^2))≤a+1/10^12) :
    (a:ℝ)≤Real.log ((1+(u:ℝ))/(1-u)) ∧ Real.log ((1+(u:ℝ))/(1-u))≤(a:ℝ)+1/10^12 := by
  have A := gap u h₀ h₁ 16
  have B := (Rat.cast_le (K:=ℝ)).mpr hL
  have C := (Rat.cast_le (K:=ℝ)).mpr hU
  push_cast at C
  norm_num only [show 2*16+1=33 by decide] at A
  constructor <;> linarith

theorem small : (693147180559/10^12:ℝ)≤Real.log 2 ∧ Real.log 2≤693147180560/10^12 := by
  have H := tight (1/3) (693147180559/10^12) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  norm_num at H ⊢
  exact H

private theorem base : (22802707378596/10^12:ℝ)≤Real.log 8000000000 ∧
    Real.log 8000000000≤22802707378635/10^12 := by
  have H := tight (1/9) (223143551314/10^12) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  have J := small
  norm_num at H
  rw [show (8000000000:ℝ)=2^30*(5/4)^9 by norm_num,Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

private theorem shift (u : ℝ) (h : 0≤u) :
    Real.log 8000000000 + u/(8000000000+u) ≤ Real.log (8000000000+u) ∧
    Real.log (8000000000+u) ≤ Real.log 8000000000+u/8000000000 := by
  let t : ℝ := (8000000000+u)/8000000000
  have ht : 0<t := by dsimp [t]; positivity
  have l := Real.one_sub_inv_le_log_of_pos ht
  have r := Real.log_le_sub_one_of_pos ht
  have eq : Real.log t=Real.log (8000000000+u)-Real.log 8000000000 := Real.log_div (by positivity) (by norm_num)
  rw [eq] at l r
  have a : 1-t⁻¹=u/(8000000000+u) := by dsimp [t];field_simp <;> ring
  have b : t-1=u/8000000000 := by dsimp [t];ring
  rw [a] at l
  rw [b] at r
  constructor <;> linarith

theorem log1 : (22802707378845/10^12:ℝ)≤Real.log 8000000002 ∧
    Real.log 8000000002≤22802707378885/10^12 := by
  have H := shift 2 (by norm_num)
  have J := base
  norm_num at H J ⊢
  constructor <;> linarith

theorem log2 : (22802707378970/10^12:ℝ)≤Real.log 8000000003 ∧
    Real.log 8000000003≤22802707379010/10^12 := by
  have H := shift 3 (by norm_num)
  have J := base
  norm_num at H J ⊢
  constructor <;> linarith

#print axioms log1
#print axioms log2
#print axioms small
end BMORQ3LargeLogs
end

section
namespace BMORFiniteQuotientPsi
open Finset

noncomputable def progression (f : ℕ→ℝ) (N q a d : ℕ) :=
  ∑ n ∈ Icc 1 N, if n*d%q=a%q then f n else 0

noncomputable def psi := progression ArithmeticFunction.vonMangoldt
noncomputable def logMass := progression (fun n => Real.log n)

private abbrev Pair := Σ _ : ℕ, ℕ

/-- Write n = mk before summing the divisor identity log n = Σ Λ(k).
The multiplier d allows a single recurrence to treat all residue classes. -/
theorem log_eq_quotients (N q a d : ℕ) :
    logMass N q a d = ∑ m ∈ Icc 1 N, psi (N/m) q a (m*d) := by
  let lhs := (Icc 1 N).sigma Nat.divisors
  let rhs := (Icc 1 N).sigma (fun m => Icc 1 (N/m))
  let lf (x : Pair) : ℝ := if x.1*d%q=a%q then ArithmeticFunction.vonMangoldt x.2 else 0
  let rf (x : Pair) : ℝ := if x.2*(x.1*d)%q=a%q then ArithmeticFunction.vonMangoldt x.2 else 0
  have hL : logMass N q a d = ∑ x ∈ lhs, lf x := by
    unfold lhs logMass progression; rw [sum_sigma]; apply sum_congr rfl
    intro n _
    by_cases h : n*d%q=a%q <;> simp [lf,h,ArithmeticFunction.vonMangoldt_sum]
  have hR : (∑ x ∈ rhs, rf x) = ∑ m ∈ Icc 1 N, psi (N/m) q a (m*d) := by
    unfold rhs;rw [sum_sigma];rfl
  refine hL.trans ((?_ : (∑ x ∈ lhs, lf x) = ∑ x ∈ rhs, rf x).trans hR)
  apply sum_nbij' (fun x : Pair => (⟨x.1/x.2,x.2⟩:Pair)) (fun x : Pair => (⟨x.1*x.2,x.2⟩:Pair))
  · rintro ⟨n,k⟩ hx
    obtain ⟨hn,hk⟩:=mem_sigma.mp hx
    obtain ⟨hn0,hnN⟩:=mem_Icc.mp hn
    have hdiv := Nat.dvd_of_mem_divisors hk
    have kpos := Nat.pos_of_mem_divisors hk
    have mpos := Nat.div_pos (Nat.le_of_dvd hn0 hdiv) kpos
    have prod := Nat.div_mul_cancel hdiv
    apply mem_sigma.mpr
    exact ⟨mem_Icc.mpr ⟨mpos,(Nat.div_le_self ..).trans hnN⟩,
      mem_Icc.mpr ⟨kpos,(Nat.le_div_iff_mul_le mpos).mpr (by simpa [Nat.mul_comm] using prod.le.trans hnN)⟩⟩
  · rintro ⟨m,k⟩ hx
    obtain ⟨hm,hk⟩:=mem_sigma.mp hx
    obtain ⟨mp,_⟩:=mem_Icc.mp hm
    obtain ⟨kp,bound⟩:=mem_Icc.mp hk
    have p : 0<m*k := Nat.mul_pos mp kp
    apply mem_sigma.mpr
    exact ⟨mem_Icc.mpr ⟨p,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le mp).mp bound⟩,
      Nat.mem_divisors.mpr ⟨dvd_mul_left _ _,p.ne'⟩⟩
  · rintro ⟨n,k⟩ hx
    have h := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors (mem_sigma.mp hx).2)
    exact congrArg (fun y => (⟨y,k⟩:Pair)) h
  · rintro ⟨m,k⟩ hx
    have kp := (mem_Icc.mp (mem_sigma.mp hx).2).1
    exact congrArg (fun y => (⟨y,k⟩:Pair)) (Nat.mul_div_cancel m kp)
  · rintro ⟨n,k⟩ hx
    have hd := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors (mem_sigma.mp hx).2)
    have key : k*(n/k*d)=n*d := by rw [←Nat.mul_assoc,Nat.mul_comm k,hd]
    simp only [lf,rf,key]

/-- Every recursive term on the right has a strictly smaller integer argument. -/
theorem split (N q a d : ℕ) (hN : 1≤N) :
    psi N q a d = logMass N q a d - ∑ m ∈ Icc 2 N, psi (N/m) q a (m*d) := by
  have h := log_eq_quotients N q a d
  have sets : Icc 1 N = insert 1 (Icc 2 N) := by
    ext m;simp only [mem_Icc,mem_insert];omega
  rw [sets,sum_insert (by simp),Nat.div_one,one_mul] at h
  linarith

theorem frozen (N q a : ℕ) :
    (∑ n ∈ (range (N+1)).filter (fun n => n%q=a%q), ArithmeticFunction.vonMangoldt n) =
    psi N q a 1 := by
  rw [sum_filter]
  change _ = ∑ n ∈ Icc 1 N, if n*1%q=a%q then ArithmeticFunction.vonMangoldt n else 0
  simp only [mul_one]
  have sets : range (N+1)=insert 0 (Icc 1 N) := by
    ext m;simp only [mem_range,mem_insert,mem_Icc];omega
  rw [sets,sum_insert (by simp)]
  simp

#print axioms log_eq_quotients
#print axioms split
#print axioms frozen
end BMORFiniteQuotientPsi
end

section
namespace BMORFiniteQuotientPsi
open Finset

def candidates (q a d : ℕ) := (range q).filter (fun r => (r*d)%q=a%q)

def residue (q a d : ℕ) : Option ℕ :=
  if h : (candidates q a d).Nonempty then some ((candidates q a d).min' h) else none

theorem solution {q a d r : ℕ} (hq : 0<q) (ha : a.Coprime q)
    (hs : residue q a d=some r) : r<q ∧ ∀ x : ℕ,(x*d)%q=a%q ↔ x%q=r := by
  unfold residue at hs
  split at hs
  · rename_i h
    have hr := min'_mem (candidates q a d) h
    have eq := Option.some.inj hs
    rw [eq] at hr
    obtain ⟨hr',hm⟩ := mem_filter.mp hr
    have hc : (r*d).Coprime q := (show Nat.ModEq q (r*d) a from hm).gcd_eq.trans ha
    have hd : d.Coprime q := (Nat.coprime_mul_iff_left.mp hc).2
    have hmod : Nat.ModEq q (r*d) a := hm
    refine ⟨mem_range.mp hr',?_⟩
    intro x
    constructor
    · intro hx
      exact Nat.mod_eq_of_modEq (Nat.ModEq.cancel_right_of_coprime hd.symm
        ((show Nat.ModEq q (x*d) a from hx).trans hmod.symm)) (mem_range.mp hr')
    · intro hx
      have c : Nat.ModEq q x r := hx.trans (Nat.mod_eq_of_lt (mem_range.mp hr')).symm
      exact (c.mul_right d).trans hmod
  · simp at hs

theorem no_solution {q a d : ℕ} (hq : 0<q) (hs : residue q a d=none) (x : ℕ) :
    (x*d)%q≠a%q := by
  intro hx
  have hr : x%q∈candidates q a d :=
    mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq),((Nat.mod_modEq x q).mul_right d).trans hx⟩
  simp [residue,show (candidates q a d).Nonempty from ⟨_,hr⟩] at hs

theorem logMass_residue (N q a d : ℕ) (hq : 0<q) (ha : a.Coprime q) :
    logMass N q a d = (residue q a d).elim 0 (fun r =>
      ∑ x ∈ Icc 1 N, if x%q=r then Real.log x else 0) := by
  unfold logMass progression
  cases h : residue q a d with
  | none => simp [no_solution hq h]
  | some r => simp only [Option.elim_some,(solution hq ha h).2]

#print axioms solution
#print axioms logMass_residue
end BMORFiniteQuotientPsi
end

section
namespace BMORFiniteLogMoments
open Finset

noncomputable def powerSum (n j : ℕ) : ℚ :=
  ∑ i ∈ range (j+1), bernoulli i * ((j+1).choose i) * (n:ℚ)^(j+1-i)/(j+1)

/-- n enters only through powers. Both finite ranges are bounded by j. -/
noncomputable def moment (n : ℕ) (a d : ℚ) (j : ℕ) : ℚ :=
  ∑ i ∈ range (j+1), (d^i * a^(j-i) * j.choose i) * powerSum n i

theorem moment_eq (n : ℕ) (a d : ℚ) (j : ℕ) :
    (∑ v ∈ range n,(a+d*v)^j)=moment n a d j := by
  change _ = ∑ i ∈ range (j+1), (d^i*a^(j-i)*j.choose i)*powerSum n i
  calc
    _ = ∑ v ∈ range n, ∑ i ∈ range (j+1), (d^i*a^(j-i)*j.choose i)*(v:ℚ)^i := by
      apply sum_congr rfl
      intro v _
      rw [add_comm,add_pow]
      apply sum_congr rfl
      intro i _
      rw [mul_pow];ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [←mul_sum,sum_range_pow]
      rfl

noncomputable def correction (n m : ℕ) (C a d : ℚ) : ℚ :=
  ∑ j ∈ range m,moment n (1-a/C) (-d/C) (j+1)/(j+1)

theorem correction_eq (n m : ℕ) (C a d : ℚ) :
    (correction n m C a d:ℝ) = ∑ v ∈ range n, ∑ j ∈ range m,
        (1-((a:ℝ)+(d:ℝ)*v)/(C:ℝ))^(j+1)/(j+1) := by
  have q : correction n m C a d = ∑ v ∈ range n, ∑ j ∈ range m,
      (1-(a+d*v)/C)^(j+1)/(j+1) := by
    unfold correction;rw [sum_comm (s:=range n)]
    apply sum_congr rfl
    intro j _
    rw [←moment_eq,←sum_div]
    apply congrArg (·/((j:ℚ)+1))
    apply sum_congr rfl
    intro v _
    congr 1
    ring
  rw [q]
  push_cast
  rfl

private theorem log_cell {C x : ℝ} (hc : 0<C) (hx : 0<x) (m : ℕ)
    (hu : |1-x/C|≤1/3) :
    |(Real.log x-Real.log C)+(∑ j ∈ range m, (1-x/C)^(j+1)/(j+1))| ≤
      (1/3:ℝ)^(m+1)/(1-1/3) := by
  have raw := Real.abs_log_sub_add_sum_range_le (hu.trans_lt (by norm_num : (1/3:ℝ)<1)) m
  rw [sub_sub_cancel,Real.log_div hx.ne' hc.ne',add_comm] at raw
  exact raw.trans (div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hu _)
    (by norm_num) (by linarith))

/-- Uniform logarithm sum error for one arithmetic progression inside [t,2t]
using center C=3t/2. The certified correction requires no loop of length n. -/
theorem block (n m : ℕ) {t a d : ℚ} (ht : 0<t)
    (points : ∀ v∈range n,t≤a+d*v ∧ a+d*v≤2*t) :
    |(∑ v ∈ range n, Real.log ((a:ℝ)+(d:ℝ)*v)) -
      ((n:ℝ)*Real.log ((3*t/2:ℚ):ℝ) - (correction n m (3*t/2) a d:ℝ))|
    ≤ n*((1/3:ℝ)^(m+1)/(1-1/3)) := by
  let C : ℚ := 3*t/2
  have hc : (0:ℝ)<(C:ℝ) := by exact_mod_cast (show 0<C by dsimp [C];positivity)
  have row (v : ℕ) (hv : v∈range n) := points v hv
  have bound (v : ℕ) (hv : v∈range n) :
      |(Real.log ((a:ℝ)+(d:ℝ)*v)-Real.log (C:ℝ))+
        ∑ j ∈ range m, (1-((a:ℝ)+(d:ℝ)*v)/(C:ℝ))^(j+1)/(j+1)| ≤
          (1/3:ℝ)^(m+1)/(1-1/3) := by
    obtain ⟨h₁,h₂⟩:=row v hv
    have h₁' : (t:ℝ)≤(a:ℝ)+(d:ℝ)*v := by exact_mod_cast h₁
    have h₂' : (a:ℝ)+(d:ℝ)*v≤2*(t:ℝ) := by exact_mod_cast h₂
    have hce : (C:ℝ)=3*(t:ℝ)/2 := by simp [C]
    apply log_cell hc (by linarith)
    apply abs_le.mpr
    constructor
    · rw [le_sub_iff_add_le,←le_sub_iff_add_le']
      apply (div_le_iff₀ hc).mpr
      linarith
    · rw [sub_le_iff_le_add,←sub_le_iff_le_add']
      apply (le_div_iff₀ hc).mpr
      linarith
  change |(∑ v ∈ range n,Real.log ((a:ℝ)+(d:ℝ)*v))-((n:ℝ)*Real.log (C:ℝ)-(correction n m C a d:ℝ))|≤_
  rw [correction_eq,sub_sub_eq_add_sub]
  have shift : (n:ℝ)*Real.log (C:ℝ)=∑ _v ∈ range n,Real.log (C:ℝ) := by simp
  rw [shift]
  rw [show ∀ (x y z : ℝ), x+z-y=(x-y)+z by intros;ring,←sum_sub_distrib,←sum_add_distrib]
  exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum bound).trans_eq (by simp))

set_option maxRecDepth 8192 in
theorem error80 (n : ℕ) (hn : n≤40000000000000) :
    (n:ℝ)*((1/3:ℝ)^(80+1)/(1-1/3)) < 1/10^(24:ℕ) := by
  have H : (n:ℝ)≤40000000000000 := by exact_mod_cast hn
  have h₀ : 0≤(1/3:ℝ)^(80+1)/(1-1/3) := by positivity
  exact (mul_le_mul_of_nonneg_right H h₀).trans_lt (by norm_num)

#print axioms moment_eq
#print axioms block
#print axioms error80
end BMORFiniteLogMoments
end

section
namespace BMORFiniteAPCells
open Finset

/-- First integer in [L,∞) with the indicated canonical residue. -/
def first (L q r : ℕ) :=
  if L%q≤r then q*(L/q)+r else q*(L/q+1)+r

theorem first_properties {L q r : ℕ} (hq : 0<q) (hr : r<q) :
    L≤first L q r ∧ first L q r<L+q ∧ first L q r%q=r := by
  have h := Nat.mod_add_div L q
  have h' := Nat.mod_lt L hq
  unfold first
  split <;> simp [Nat.mul_add,Nat.add_assoc,Nat.mod_eq_of_lt hr] <;> omega

/-- Number of progression elements below the exclusive right endpoint U. -/
def length (x U q : ℕ) := if x<U then (U-1-x)/q+1 else 0

theorem lt_length {x U q v : ℕ} (hq : 0<q) :
    v<length x U q ↔ x+q*v<U := by
  unfold length
  split
  · rw [Nat.lt_succ_iff,Nat.le_div_iff_mul_le hq,Nat.mul_comm v q]; omega
  · omega

theorem cell_eq {L U q r : ℕ} (hq : 0<q) (hr : r<q) (f : ℕ→ℝ) :
    (∑ x ∈ (Ico L U).filter (fun x => x%q=r), f x) =
      ∑ v ∈ range (length (first L q r) U q), f (first L q r+q*v) := by
  let a := first L q r
  obtain ⟨hL,hsmall,hmod⟩ := first_properties (L:=L) hq hr
  change (∑ x ∈ _, f x) = ∑ v ∈ range (length a U q),f (a+q*v)
  have rep {x : ℕ} (hx : x∈(Ico L U).filter (fun x => x%q=r)) :
      a+q*((x-a)/q)=x := by
    obtain ⟨h,hm⟩ := mem_filter.mp hx
    have conj : Nat.ModEq q a x := hmod.trans hm.symm
    have ha : a≤x := conj.le_of_lt_add (by have := (mem_Ico.mp h).1; dsimp [a]; omega)
    obtain ⟨t,ht⟩ := (Nat.modEq_iff_exists_eq_add ha).mp conj
    subst x
    simp [hq]
  apply sum_nbij' (fun x => (x-a)/q) (fun v => a+q*v)
  · intro x hx
    apply mem_range.mpr
    apply (lt_length hq).mpr
    rw [rep hx]
    exact (mem_Ico.mp (mem_filter.mp hx).1).2
  · intro v hv
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by dsimp [a];omega,(lt_length hq).mp (mem_range.mp hv)⟩,?_⟩
    simpa only [Nat.add_mul_mod_self_left] using hmod
  · exact fun _ hx => rep hx
  · intro v _;simp [hq]
  · intro x hx; rw [rep hx]

/-- Dyadic cells partition all positive integers up to N; the final cell is clipped. -/
theorem dyadic (N E : ℕ) (hE : N<2^E) (f : ℕ→ℝ) :
    (∑ x ∈ Icc 1 N,f x) = ∑ e ∈ range E,
      ∑ x ∈ Ico (min (2^e) (N+1)) (min (2^(e+1)) (N+1)), f x := by
  have aux (k : ℕ) : (∑ e ∈ range k,
      ∑ x ∈ Ico (min (2^e) (N+1)) (min (2^(e+1)) (N+1)), f x) =
      ∑ x ∈ Ico 1 (min (2^k) (N+1)), f x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ,ih]
      apply sum_Ico_consecutive
      · exact le_min (Nat.one_le_two_pow) (by omega)
      · exact min_le_min_right _ (by rw [pow_succ];omega)
  rw [aux,min_eq_right (by omega)]
  apply sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [mem_Icc,mem_Ico];omega

#print axioms cell_eq
#print axioms dyadic
end BMORFiniteAPCells
end

section
namespace BMORQ3DirectLogMass
open Finset BMORFiniteQuotientPsi BMORFiniteAPCells BMORAPLogPrimitive

def massNumerator (d : ℕ) : ℕ :=
  if d=1 then 19784204993555707634330348482169231845900871380646
  else 19784204996249712494363294771074097740916196405460

private theorem reindex (d : ℕ) (hd : d=1 ∨ d=2) :
    logMass 8000000000 3 1 d = ∑ i ∈ range 2666666667, Real.log ((d:ℝ)+3*i) := by
  have hr : d<3 := by omega
  have hs : residue 3 1 d=some d := by rcases hd with rfl|rfl <;> decide
  have hf : first 1 3 d=d := by rcases hd with rfl|rfl <;> decide
  have hl : BMORFiniteAPCells.length d 8000000001 3=2666666667 := by rcases hd with rfl|rfl <;> decide
  have sets : Icc 1 8000000000=Ico 1 8000000001 := by
    ext k
    simp only [mem_Icc,mem_Ico]
    omega
  rw [logMass_residue _ _ _ _ (by decide) (by decide),hs,Option.elim_some,sets,←sum_filter]
  rw [cell_eq (by decide : 0<3) hr (fun x : ℕ => Real.log (x:ℝ)),hf,hl]
  push_cast <;> rfl

/-- The two large rational mass witnesses are within one of the original
real logarithmic sums at eight billion. No table accuracy input is needed. -/
theorem actual_mass (d : ℕ) (hd : d=1 ∨ d=2) :
    |logMass 8000000000 3 1 d - (massNumerator d : ℝ)/2^128| ≤ 1 := by
  rw [reindex d hd]
  rcases hd with rfl|rfl
  · have H := prefix_bound (q:=3) (x:=1) (by norm_num) (by norm_num) 2666666667
    have L := BMORQ3LargeLogs.log1
    norm_num only [primitive,Nat.cast_ofNat,Real.log_one,mul_zero] at H
    generalize hsum : (∑ i ∈ range 2666666667,Real.log ((1:ℝ)+3*i))=S at H ⊢
    norm_num [massNumerator] at H L ⊢
    apply abs_le.mpr
    constructor <;> linarith
  · have H := prefix_bound (q:=3) (x:=2) (by norm_num) (by norm_num) 2666666667
    have L := BMORQ3LargeLogs.log2
    have J := BMORQ3LargeLogs.small
    norm_num only [primitive,Nat.cast_ofNat] at H
    generalize hsum : (∑ i ∈ range 2666666667,Real.log ((2:ℝ)+3*i))=S at H ⊢
    norm_num [massNumerator] at H L J ⊢
    apply abs_le.mpr
    constructor <;> linarith

#print axioms actual_mass
end BMORQ3DirectLogMass
end

section
namespace BMORDoubleModulus
open Finset ArithmeticFunction

def residueSet (n q a : ℕ) := (range (n+1)).filter (fun k => k%q=a%q)
noncomputable def sumAP (n q a : ℕ) := ∑ k ∈ residueSet n q a,vonMangoldt k

/-- Doubling an odd modulus omits only even prime powers in a reduced
residue class. Their entire Mangoldt contribution is at most log n. -/
theorem loss {n q a : ℕ} (hn : 0<n) (hq : Nat.Coprime 2 q) (ha : a%2=1) :
    0≤sumAP n q a-sumAP n (2*q) a ∧ sumAP n q a-sumAP n (2*q) a≤Real.log n := by
  classical
  let A := residueSet n q a
  let B := residueSet n (2*q) a
  let D := (2^(Nat.log 2 n)).divisors
  have sub : B⊆A := by
    intro k hk
    obtain ⟨kn,hm⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨kn,Nat.ModEq.of_dvd (dvd_mul_left q 2) hm⟩
  have diff : sumAP n q a-sumAP n (2*q) a=∑ k ∈ A \ B,vonMangoldt k := by
    have eq := sum_sdiff sub (f:=fun k => vonMangoldt k)
    change (∑ k ∈ A,vonMangoldt k)-(∑ k ∈ B,vonMangoldt k)=_
    linarith
  rw [diff]
  refine ⟨sum_nonneg (fun _ _ => vonMangoldt_nonneg),?_⟩
  let C := (A \ B).filter (fun k => vonMangoldt k≠0)
  have covered : C⊆D := by
    intro k hk
    obtain ⟨hk',nz⟩ := mem_filter.mp hk
    obtain ⟨ka,kb⟩ := mem_sdiff.mp hk'
    obtain ⟨kn,km⟩ := mem_filter.mp ka
    have kn' : k≤n := Nat.lt_succ_iff.mp (mem_range.mp kn)
    have even : 2∣k := by
      by_contra h
      have w : k%2=1 := by omega
      exact kb (mem_filter.mpr ⟨kn,(Nat.modEq_and_modEq_iff_modEq_mul hq).mp ⟨w.trans ha.symm,km⟩⟩)
    obtain ⟨p,j,hp,_,he⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp nz)
    have pd : 2∣p := Nat.prime_two.dvd_of_dvd_pow (by simpa only [he] using even : 2∣p^j)
    have pe := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp pd
    subst p
    apply Nat.mem_divisors.mpr
    rw [←he]
    exact ⟨pow_dvd_pow _ (Nat.le_log_of_pow_le (by decide : 1<2) (by simpa only [he] using kn')),by positivity⟩
  have eq : (∑ k ∈ C,vonMangoldt k)=∑ k ∈ A \ B,vonMangoldt k := by
    simp [C,sum_filter]
    apply sum_congr rfl
    intro x _
    split <;> simp_all
  rw [←eq]
  calc
    _ ≤ ∑ k ∈ D,vonMangoldt k := sum_le_sum_of_subset_of_nonneg covered (fun _ _ _ => vonMangoldt_nonneg)
    _ = Real.log ((2^(Nat.log 2 n):ℕ):ℝ) := vonMangoldt_sum
    _ ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 hn.ne')

/-- A stronger error interval on odd q also certifies its even lift 2q. -/
theorem transfer {n q a : ℕ} (hn : 0<n) (hq : Nat.Coprime 2 q) (ha : a%2=1)
    {B : ℝ} (lower : (n:ℝ)/q.totient-B+Real.log n≤sumAP n q a)
    (upper : sumAP n q a≤(n:ℝ)/q.totient+B) :
    |sumAP n (2*q) a-(n:ℝ)/(2*q).totient|≤B := by
  have H := loss hn hq ha
  rw [Nat.totient_mul hq,Nat.totient_two,one_mul]
  apply abs_le.mpr
  constructor <;> linarith

#print axioms loss
#print axioms transfer
end BMORDoubleModulus
end

section
namespace BMORProgression
theorem doubled_residue_loss {n q a : ℕ} (hn : 0<n) (hq : Nat.Coprime 2 q) (ha : a%2=1) :
    0≤psi q a n-psi (2*q) a n ∧ psi q a n-psi (2*q) a n≤Real.log n :=
  BMORDoubleModulus.loss hn hq ha
#print axioms doubled_residue_loss
end BMORProgression
end

section
namespace BMORDoubleModulus
open Finset ArithmeticFunction

def misses (q a : ℕ) : Bool :=
  (List.range q.totient).all (fun j => decide ((2^j)%q≠a%q))

theorem misses_all {q a : ℕ} (hq : 0<q) (h₂ : Nat.Coprime 2 q) (check : misses q a=true) (j : ℕ) :
    (2^j)%q≠a%q := by
  let t := q.totient
  have pos : 0<t := Nat.totient_pos.mpr hq
  have eql : 2^j ≡ 2^(j%t) [MOD q] := calc
    2^j = 2^(j%t+t*(j/t)) := congrArg (fun k : ℕ => 2^k) (Nat.mod_add_div j t).symm
    _ = 2^(j%t)*(2^t)^(j/t) := by rw [pow_add,pow_mul]
    _ ≡ 2^(j%t)*1^(j/t) [MOD q] :=
      (Nat.ModEq.pow (j/t) (Nat.ModEq.pow_totient h₂)).mul_left _
    _ = _ := by simp
  have h := (List.all_eq_true.mp check) (j%t) (List.mem_range.mpr (Nat.mod_lt _ pos))
  exact fun eq => of_decide_eq_true h (eql.symm.trans eq)

/-- Equality holds at every N when the odd residue contains no powers of two. -/
theorem exact_lift {q a : ℕ} (hq : 0<q) (h₂ : Nat.Coprime 2 q) (ha : a%2=1)
    (check : misses q a=true) (N : ℕ) : sumAP N (2*q) a=sumAP N q a := by
  classical
  apply sum_subset
  · intro k hk
    obtain ⟨kn,hm⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨kn,Nat.ModEq.of_dvd (dvd_mul_left q 2) hm⟩
  · intro k hk hb
    obtain ⟨kn,hi⟩ := mem_filter.mp hk
    by_contra nz
    obtain ⟨p,j,hp,_,he⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp nz)
    have even : 2∣k := by
      by_contra h
      have w : k%2=1 := by omega
      exact hb (mem_filter.mpr ⟨kn,(Nat.modEq_and_modEq_iff_modEq_mul h₂).mp ⟨w.trans ha.symm,hi⟩⟩)
    have pd : 2∣p := Nat.prime_two.dvd_of_dvd_pow (by simpa only [he] using even : 2∣p^j)
    have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp pd
    subst p
    exact misses_all hq h₂ check j (by simpa only [he] using hi)

def inherited (q : ℕ) : Finset ℕ :=
  (range (2*q)).filter (fun a => a.Coprime (2*q) ∧ misses q a=true)

/-- Count individual reduced classes of doubled moduli in the frozen range
whose complete prime-power sum is inherited exactly at every endpoint. -/
theorem classes : (∑ q ∈ (Icc 3 51).filter (fun q => q%2=1), (inherited q).card)=219 := by
  decide +kernel

#print axioms exact_lift
#print axioms classes
end BMORDoubleModulus
end

section
namespace BMORDoubleModulus
open Finset

/-- A class selected by the finite certificate has exactly the same absolute
error as its odd-modulus reduction at every index. -/
theorem inherited_error {q a : ℕ} (hq : 0<q) (odd : q%2=1) (h : a∈inherited q) (N : ℕ) :
    |sumAP N (2*q) a-(N:ℝ)/(2*q).totient|=|sumAP N q (a%q)-(N:ℝ)/q.totient| := by
  have h₂ : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  obtain ⟨_,ha,check⟩ := mem_filter.mp h
  have c₂ : a.Coprime 2 := ha.coprime_dvd_right (dvd_mul_right 2 q)
  have parity : a%2=1 := by obtain ⟨k,hk⟩ := Nat.coprime_two_right.mp c₂; omega
  rw [exact_lift hq h₂ parity check,Nat.totient_mul h₂,Nat.totient_two,one_mul]
  simp only [sumAP,residueSet,Nat.mod_mod]

theorem moduli :
    (((Icc 3 51).filter (fun q => q%2=1)).filter (fun q => (inherited q).card>0)).card=15 := by
  decide +kernel

#print axioms inherited_error
#print axioms moduli
end BMORDoubleModulus
end

section
namespace BMORProgression
theorem doubled_exact_error {q a : ℕ} (hq : 0<q) (odd : q%2=1)
    (h : a∈BMORDoubleModulus.inherited q) (n : ℕ) :
    |psi (2*q) a n-(n:ℝ)/(2*q).totient|=|psi q (a%q) n-(n:ℝ)/q.totient| :=
  BMORDoubleModulus.inherited_error hq odd h n
#print axioms doubled_exact_error
end BMORProgression
end

section
namespace BMORDoubleModulus
open Finset

def redundant (q a : ℕ) : Prop :=
  q%2=0 ∧ (q/2)%2=1 ∧ misses (q/2) a=true

instance (q a : ℕ) : Decidable (redundant q a) := by unfold redundant; infer_instance

/-- Only these pairs need a separate proof. The right-hand side of the desired
inequality is allowed to depend on n but not on the modulus. -/
theorem reduce_all (B : ℕ → ℝ)
    (H : ∀ q a n : ℕ, 3≤q → q≤105 → a<q → a.Coprime q → 8000000000≤n → ¬redundant q a →
        |sumAP n q a-(n:ℝ)/q.totient|≤B n)
    (q a n : ℕ) (qlo : 3≤q) (qhi : q≤105) (alt : a<q) (cop : a.Coprime q) (lo : 8000000000≤n) :
    |sumAP n q a-(n:ℝ)/q.totient|≤B n := by
  by_cases h : redundant q a
  · obtain ⟨even,odd,chk⟩ := h
    let r := q/2
    have hr : 3≤r := by dsimp [r]; omega
    have ep : q=2*r := by dsimp [r]; omega
    have co : a.Coprime (2*r) := ep ▸ cop
    have mem : a∈inherited r :=
      mem_filter.mpr ⟨mem_range.mpr (ep ▸ alt),co,chk⟩
    have c : a.Coprime r := co.coprime_dvd_right (dvd_mul_left r 2)
    have cc : (a%r).Coprime r := (Nat.gcd_rec r a).symm.trans c.symm.gcd_eq_one
    have keep : ¬redundant r (a%r) := fun e => by
      have v := e.1
      change r%2=1 at odd
      omega
    calc
      _ = |sumAP n (2*r) a-(n:ℝ)/(2*r).totient| := by rw [←ep]
      _ = _ := inherited_error (by omega) odd mem n
      _ ≤ B n := H r (a%r) n hr (by omega) (Nat.mod_lt _ (by omega)) cc lo keep
  · exact H q a n qlo qhi alt cop lo h

def remaining (q : ℕ) : Finset ℕ :=
  (range q).filter (fun a => a.Coprime q ∧ ¬redundant q a)

theorem remaining_count : (∑ q∈Icc 3 105,(remaining q).card)=3153 := by
  decide +kernel

#print axioms reduce_all
#print axioms remaining_count
end BMORDoubleModulus
end

section
namespace BMORProgression
/-- A uniform proof on the 3153 remaining classes suffices for the frozen statement. -/
theorem of_reduced_classes
    (H : ∀ q a n : ℕ, 3≤q → q≤105 → a<q → a.Coprime q → 8000000000≤n →
      ¬BMORDoubleModulus.redundant q a →
      |psi q a n-(n:ℝ)/q.totient|≤(n:ℝ)/(840*Real.log n)) :
    ∀ q a n : ℕ, 3≤q → q≤105 → a<q → a.Coprime q → 8000000000≤n →
      |psi q a n-(n:ℝ)/q.totient|≤(n:ℝ)/(840*Real.log n) :=
  BMORDoubleModulus.reduce_all (fun n => (n:ℝ)/(840*Real.log n)) H
#print axioms of_reduced_classes
end BMORProgression
end