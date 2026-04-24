import Architect
import PrimeNumberTheoremAnd.MellinCalculus
import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.ZetaConj
import PrimeNumberTheoremAnd.SmoothExistence
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

blueprint_comment /--
The approach here is completely standard. We follow the use of
$\mathcal{M}(\widetilde{1_{\epsilon}})$ as in [Kontorovich 2015].
-/

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ


@[blueprint "ChebyshevPsi"
  (title := "ChebyshevPsi")
  (statement := /--
  The (second) Chebyshev Psi function is defined as
  $$
  \psi(x) := \sum_{n \le x} \Lambda(n),
  $$
  where $\Lambda(n)$ is the von Mangoldt function.
  -/)
  (latexEnv := "definition")]
noncomputable abbrev ChebyshevPsi (x : ℝ) : ℝ :=
  Chebyshev.psi x

blueprint_comment /--
It has already been established that zeta doesn't vanish on the 1 line, and has a pole at $s=1$
of order 1.
We also have the following.
-/

@[blueprint "LogDerivativeDirichlet"
  (title := "LogDerivativeDirichlet")
  (statement := /--
  We have that, for $\Re(s)>1$,
  $$-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}. $$-/)
  (proof := /-- Already in Mathlib. -/)]
theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, Λ n / (n : ℂ) ^ s := by
  sorry

blueprint_comment /--

The main object of study is the following inverse Mellin-type transform, which will turn out to
be a smoothed Chebyshev function.
-/

noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

@[blueprint
  (title := "SmoothedChebyshev")
  (statement := /--
  Fix $\epsilon>0$, and a bumpfunction supported in $[1/2,2]$. Then we define the smoothed
  Chebyshev function $\psi_{\epsilon}$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
  $$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(\sigma)}\frac{-\zeta'(s)}{\zeta(s)}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)
  X^{s}ds,$$
  where we'll take $\sigma = 1 + 1 / \log X$.
  -/)]
noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate


open MeasureTheory

@[blueprint
  (title := "SmoothedChebyshevDirichlet-aux-integrable")
  (statement := /--
  Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in
  $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$,
  and $\sigma\in (1, 2]$, the function
  $$
  x \mapsto\mathcal{M}(\widetilde{1_{\epsilon}})(\sigma + ix)
  $$
  is integrable on $\mathbb{R}$.
  -/)
  (proof := /--
  By Lemma \ref{MellinOfSmooth1b} the integrand is $O(1/t^2)$ as $t\rightarrow \infty$ and hence
  the function is integrable.
  -/)
  (latexEnv := "lemma")]
lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  sorry

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

@[blueprint
  (title := "SmoothedChebyshevDirichlet-aux-tsum-integral")
  (statement := /--
  Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in
  $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$ and
  $\sigma\in(1,2]$, the function
  $x \mapsto \sum_{n=1}^\infty \frac{\Lambda(n)}{n^{\sigma+it}}
  \mathcal{M}(\widetilde{1_{\epsilon}})(\sigma+it) x^{\sigma+it}$ is equal to
  $\sum_{n=1}^\infty \int_{(0,\infty)} \frac{\Lambda(n)}{n^{\sigma+it}}
  \mathcal{M}(\widetilde{1_{\epsilon}})(\sigma+it) x^{\sigma+it}$.
  -/)
  (proof := /-- Interchange of summation and integration. -/)
  (latexEnv := "lemma")]
lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
  sorry

@[blueprint
  (title := "SmoothedChebyshevDirichlet")
  (statement := /--
  We have that
  $$\psi_{\epsilon}(X) = \sum_{n=1}^\infty \Lambda(n)\widetilde{1_{\epsilon}}(n/X).$$
  -/)
  (proof := /--
  We have that
  $$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(2)}\sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)
  X^{s}ds.$$
  We have enough decay (thanks to quadratic decay of $\mathcal{M}(\widetilde{1_{\epsilon}})$) to
  justify the interchange of summation and integration. We then get
  $$\psi_{\epsilon}(X) =
  \sum_{n=1}^\infty \Lambda(n)\frac{1}{2\pi i}\int_{(2)}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)
  (n/X)^{-s}
  ds
  $$
  and apply the Mellin inversion formula.
  -/)]
theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  sorry

blueprint_comment /--
The smoothed Chebyshev function is close to the actual Chebyshev function.
-/


@[blueprint
  (title := "SmoothedChebyshevClose")
  (statement := /--
  We have that
  $$\psi_{\epsilon}(X) = \psi(X) + O(\epsilon X \log X).$$
  -/)
  (proof := /--
  Take the difference. By Lemma \ref{Smooth1Properties_above} and \ref{Smooth1Properties_below},
  the sums agree except when $1-c \epsilon \leq n/X \leq 1+c \epsilon$. This is an interval of
  length $\ll \epsilon X$, and the summands are bounded by $\Lambda(n) \ll \log X$.

  %[No longer relevant, as we will do better than any power of log savings...: This is not enough,
  %as it loses a log! (Which is fine if our target is the strong PNT, with
  %exp-root-log savings, but not here with the ``softer'' approach.) So we will need something like
  %the Selberg sieve (already in Mathlib? Or close?) to conclude that the number of primes in this
  %interval is $\ll \epsilon X / \log X + 1$.
  %(The number of prime powers is $\ll X^{1/2}$.)
  %And multiplying that by $\Lambda (n) \ll \log X$ gives the desired bound.]
  -/)]
theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X := by
  sorry


blueprint_comment /--
Returning to the definition of $\psi_{\epsilon}$, fix a large $T$ to be chosen later, and set
$\sigma_0 = 1 + 1 / log X$,
$\sigma_1 = 1- A/ \log T^9$, and
$\sigma_2<\sigma_1$ a constant.
Pull
contours (via rectangles!) to go
from $\sigma_0-i\infty$ up to $\sigma_0-iT$, then over to $\sigma_1-iT$, up to $\sigma_1-3i$,
over to $\sigma_2-3i$, up to $\sigma_2+3i$, back over to $\sigma_1+3i$, up to $\sigma_1+iT$,
over to $\sigma_0+iT$, and finally up to $\sigma_0+i\infty$.

In the process, we will pick up the residue at $s=1$.
We will do this in several stages. Here the interval integrals are defined as follows:
-/

@[blueprint
  "I1"
  (title := "I₁")
  (statement := /--
  $$
  I_1(\nu, \epsilon, X, T) := \frac{1}{2\pi i} \int_{-\infty}^{-T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_0 + t i)
  \right)
   \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
  X^{\sigma_0 + t i}
  \ i \ dt
  $$
  -/)]
noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

@[blueprint
  "I2"
  (title := "I₂")
  (statement := /--
  $$
  I_2(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
  \left(
  \frac{-\zeta'}\zeta(\sigma - i T)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma - i T)
  X^{\sigma - i T} \ d\sigma
  $$
  -/)]
noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

@[blueprint
  "I37"
  (title := "I₃₇")
  (statement := /--
  $$
  I_{37}(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{-T}^{T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_1 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

@[blueprint
  "I8"
  (title := "I₈")
  (statement := /--
  $$
  I_8(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
  \left(
  \frac{-\zeta'}\zeta(\sigma + T i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma + T i)
  X^{\sigma + T i} \ d\sigma
  $$
  -/)]
noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

@[blueprint
  "I9"
  (title := "I₉")
  (statement := /--
  $$
  I_9(\nu, \epsilon, X, T) := \frac{1}{2\pi i} \int_{T}^{\infty}
  \left(
  \frac{-\zeta'}\zeta(\sigma_0 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
  X^{\sigma_0 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

@[blueprint
  "I3"
  (title := "I₃")
  (statement := /--
  $$
  I_3(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{-T}^{-3}
  \left(
  \frac{-\zeta'}\zeta(\sigma_1 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

@[blueprint
  "I7"
  (title := "I₇")
  (statement := /--
  $$
  I_7(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{3}^{T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_1 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

@[blueprint
  "I4"
  (title := "I₄")
  (statement := /--
  $$
  I_4(\nu, \epsilon, X, \sigma_1, \sigma_2) := \frac{1}{2\pi i} \int_{\sigma_2}^{\sigma_1}
  \left(
  \frac{-\zeta'}\zeta(\sigma - 3 i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma - 3 i)
  X^{\sigma - 3 i} \ d\sigma
  $$
  -/)]
noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

@[blueprint
  "I6"
  (title := "I₆")
  (statement := /--
  $$
  I_6(\nu, \epsilon, X, \sigma_1, \sigma_2) := \frac{1}{2\pi i} \int_{\sigma_2}^{\sigma_1}
  \left(
  \frac{-\zeta'}\zeta(\sigma + 3 i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma + 3 i)
  X^{\sigma + 3 i} \ d\sigma
  $$
  -/)]
noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

@[blueprint
  "I5"
  (title := "I₅")
  (statement := /--
  $$
  I_5(\nu, \epsilon, X, \sigma_2) := \frac{1}{2\pi i} \int_{-3}^{3}
  \left(
  \frac{-\zeta'}\zeta(\sigma_2 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_2 + t i)
  X^{\sigma_2 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))


def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})


-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED
@[blueprint
  (title := "dlog-riemannZeta-bdd-on-vertical-lines")
  (statement := /--
  For $\sigma_0 > 1$, there exists a constant $C > 0$ such that
  $$
  \forall t \in \R, \quad
  \left\| \frac{\zeta'(\sigma_0 + t i)}{\zeta(\sigma_0 + t i)} \right\| \leq C.
  $$
  -/)
  (proof := /--
  Write as Dirichlet series and estimate trivially using Theorem \ref{LogDerivativeDirichlet}.
  -/)
  (latexEnv := "lemma")]
theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
    ∃ c > 0, ∀(t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ c := by
  sorry

@[blueprint
  (title := "SmoothedChebyshevPull1-aux-integrable")
  (statement := /--
  The integrand $$\zeta'(s)/\zeta(s)\mathcal{M}(\widetilde{1_{\epsilon}})(s)X^{s}$$
  is integrable on the contour $\sigma_0 + t i$ for $t \in \R$ and $\sigma_0 > 1$.
  -/)
  (proof := /--
  The $\zeta'(s)/\zeta(s)$ term is bounded, as is $X^s$, and the smoothing function
  $\mathcal{M}(\widetilde{1_{\epsilon}})(s)$
  decays like $1/|s|^2$ by Theorem \ref{MellinOfSmooth1b}.
  Actually, we already know that
  $\mathcal{M}(\widetilde{1_{\epsilon}})(s)$
  is integrable from Theorem \ref{SmoothedChebyshevDirichlet_aux_integrable},
  so we should just need to bound the rest.
  -/)
  (latexEnv := "lemma")]
theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  sorry


@[blueprint
  (title := "BddAboveOnRect")
  (statement := /-- Let $g : \C \to \C$ be a holomorphic function on a rectangle, then $g$ is bounded above on the rectangle. -/)
  (proof := /-- Use the compactness of the rectangle and the fact that holomorphic functions are continuous. -/)
  (latexEnv := "lemma")]
lemma BddAboveOnRect {g : ℂ → ℂ} {z w : ℂ} (holoOn : HolomorphicOn g (z.Rectangle w)) :
    BddAbove (norm ∘ g '' (z.Rectangle w)) := by
  sorry

@[blueprint
  (title := "SmoothedChebyshevPull1")
  (statement := /--
  We have that
  $$\psi_{\epsilon}(X) =
  \mathcal{M}(\widetilde{1_{\epsilon}})(1)
  X^{1} +
  I_1 - I_2 +I_{37} + I_8 + I_9
  .
  $$
  -/)
  (proof := /-- Pull rectangle contours and evaluate the pole at $s=1$. -/)]
theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
  sorry



blueprint_comment /--
Next pull contours to another box.
-/

@[blueprint
  (title := "SmoothedChebyshevPull2")
  (statement := /--
  We have that
  $$
  I_{37} =
  I_3 - I_4 + I_5 + I_6 + I_7
  .
  $$
  -/)
  (proof := /-- Mimic the proof of Lemma \ref{SmoothedChebyshevPull1}. -/)
  (latexEnv := "lemma")]
theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  sorry

blueprint_comment /--
We insert this information in $\psi_{\epsilon}$. We add and subtract the integral over the box
$[1-\delta,2] \times_{ℂ} [-T,T]$, which we evaluate as follows
-/
@[blueprint
  (title := "ZetaBoxEval")
  (statement := /--
  For all $\epsilon > 0$ sufficiently close to $0$, the rectangle integral over $[1-\delta,2] \times_{ℂ} [-T,T]$ of the integrand in
  $\psi_{\epsilon}$ is
  $$
  \frac{X^{1}}{1}\mathcal{M}(\widetilde{1_{\epsilon}})(1)
  = X(1+O(\epsilon))
  ,$$
  where the implicit constant is independent of $X$.
  -/)
  (proof := /-- Unfold the definitions and apply Lemma \ref{MellinOfSmooth1c}. -/)]
theorem ZetaBoxEval {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C, ∀ᶠ ε in (nhdsWithin 0 (Ioi 0)), ∀ X : ℝ, 0 ≤ X →
    ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X - X‖ ≤ C * ε * X := by
  sorry


blueprint_comment /--
It remains to estimate all of the integrals.
-/

blueprint_comment /--
This auxiliary lemma is useful for what follows.
-/
@[blueprint
  (title := "IBound-aux1")
  (statement := /--
  Given a natural number $k$ and a real number $X_0 > 0$, there exists $C \geq 1$ so that for all $X \geq X_0$,
  $$
  \log^k X \le C \cdot X.
  $$
  -/)
  (proof := /--
  We use the fact that $\log^k X / X$ goes to $0$ as $X \to \infty$.
  Then we use the extreme value theorem to find a constant $C$ that works for all $X \geq X_0$.
  -/)
  (latexEnv := "lemma")]
lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) (k : ℕ) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
  sorry

@[blueprint
  (title := "I1Bound")
  (statement := /--
  We have that
  $$
  \left|I_{1}(\nu, \epsilon, X, T)\
  \right| \ll \frac{X}{\epsilon T}
  .
  $$
  Same with $I_9$.
  -/)
  (proof := /--
    Unfold the definitions and apply the triangle inequality.
  $$
  \left|I_{1}(\nu, \epsilon, X, T)\right| =
  \left|
  \frac{1}{2\pi i} \int_{-\infty}^{-T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_0 + t i)
  \right)
   \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
  X^{\sigma_0 + t i}
  \ i \ dt
  \right|
  $$
  By Theorem \ref{dlog_riemannZeta_bdd_on_vertical_lines} (once fixed!!),
  $\zeta'/\zeta (\sigma_0 + t i)$ is bounded by $\zeta'/\zeta(\sigma_0)$, and
  Theorem \ref{riemannZetaLogDerivResidue} gives $\ll 1/(\sigma_0-1)$ for the latter. This gives:
  $$
  \leq
  \frac{1}{2\pi}
  \left|
   \int_{-\infty}^{-T}
  C \log X\cdot
   \frac{C'}{\epsilon|\sigma_0 + t i|^2}
  X^{\sigma_0}
  \ dt
  \right|
  ,
  $$
  where we used Theorem \ref{MellinOfSmooth1b}.
  Continuing the calculation, we have
  $$
  \leq
  \log X \cdot
  C'' \frac{X^{\sigma_0}}{\epsilon}
  \int_{-\infty}^{-T}
  \frac{1}{t^2}
  \ dt
  \ \leq \
  C''' \frac{X\log X}{\epsilon T}
  ,
  $$
  where we used that $\sigma_0=1+1/\log X$, and $X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
  -/)
  (latexEnv := "lemma")]
theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
  sorry



@[blueprint
  (title := "I2Bound")
  (statement := /--
  Assuming a bound of the form of Lemma \ref{LogDerivZetaBndUnif} we have that
  $$
  \left|I_{2}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon T}
  .
  $$
  -/)
  (proof := /--
  Unfold the definitions and apply the triangle inequality.
  $$
  \left|I_{2}(\nu, \epsilon, X, T, \sigma_1)\right| =
  \left|\frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
  \left(\frac{-\zeta'}\zeta(\sigma - T i) \right) \cdot
  \mathcal M(\widetilde 1_\epsilon)(\sigma - T i) \cdot
  X^{\sigma - T i}
   \ d\sigma
  \right|
  $$
  $$\leq
  \frac{1}{2\pi}
  \int_{\sigma_1}^{\sigma_0}
  C \cdot \log T ^ 9
  \frac{C'}{\epsilon|\sigma - T i|^2}
  X^{\sigma_0}
   \ d\sigma
   \leq
  C'' \cdot \frac{X\log T^9}{\epsilon T^2}
  ,
  $$
  where we used Theorems \ref{MellinOfSmooth1b}, the hypothesised bound on zeta and the fact that
  $X^\sigma \le X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
  Since $T>3$, we have $\log T^9 \leq C''' T$.
  -/)
  (latexEnv := "lemma")]
lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  sorry

@[blueprint
  (title := "I8I2")
  (statement := /--
  Symmetry between $I_2$ and $I_8$:
  $$
  I_8(\nu, \epsilon, X, T) = -\overline{I_2(\nu, \epsilon, X, T)}
  .
  $$
  -/)
  (proof := /-- This is a direct consequence of the definitions of $I_2$ and $I_8$. -/)
  (latexEnv := "lemma")]
lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  sorry


@[blueprint
  (title := "I8Bound")
  (statement := /--
  We have that
  $$
  \left|I_{8}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon T}
  .
  $$
  -/)
  (proof := /--
  We deduce this from the corresponding bound for $I_2$, using the symmetry between $I_2$ and $I_8$.
  -/)
  (latexEnv := "lemma")]
lemma I8Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  sorry

@[blueprint
  (title := "log-pow-over-xsq-integral-bounded")
  (statement := /--
  For every $n$ there is some absolute constant $C>0$ such that
  $$
  \int_3^T \frac{(\log x)^9}{x^2}dx < C
  $$
  -/)
  (proof := /-- Induct on n and just integrate by parts. -/)
  (latexEnv := "lemma")]
lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T >3, ∫ x in Ioo 3 T, (Real.log x)^n / x^2 < C := by
  sorry

set_option maxHeartbeats 400000 in
-- Slow
@[blueprint
  (title := "I3Bound")
  (statement := /--
  Assuming a bound of the form of Lemma \ref{LogDerivZetaBndUnif} we have that
  $$
  \left|I_{3}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon}\, X^{-\frac{A}{(\log T)^9}}
  .
  $$
  Same with $I_7$.
  -/)
  (proof := /--
  Unfold the definitions and apply the triangle inequality.
  $$
  \left|I_{3}(\nu, \epsilon, X, T, \sigma_1)\right| =
  \left|\frac{1}{2\pi i} \int_{-T}^3
  \left(\frac{-\zeta'}\zeta(\sigma_1 + t i) \right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i}
  \ i \ dt
  \right|
  $$
  $$\leq
  \frac{1}{2\pi}
  \int_{-T}^3
  C \cdot \log t ^ 9
  \frac{C'}{\epsilon|\sigma_1 + t i|^2}
  X^{\sigma_1}
   \ dt
  ,
  $$
  where we used Theorems \ref{MellinOfSmooth1b} and the hypothesised bound on zeta.
  Now we estimate $X^{\sigma_1} = X \cdot X^{-A/ \log T^9}$, and the integral is absolutely bounded.
  -/)
  (latexEnv := "lemma")]
theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  sorry



@[blueprint
  (title := "I4Bound")
  (statement := /--
  We have that
  $$
  \left|I_{4}(\nu, \epsilon, X, \sigma_1, \sigma_2)\right| \ll \frac{X}{\epsilon}\,
   X^{-\frac{A}{(\log T)^9}}
  .
  $$
  Same with $I_6$.
  -/)
  (proof := /--
  The analysis of $I_4$ is similar to that of $I_2$, (in Lemma \ref{I2Bound}) but even easier.
  Let $C$ be the sup of $-\zeta'/\zeta$ on the curve $\sigma_2 + 3 i$ to $1+ 3i$ (this curve is compact, and away from the pole at $s=1$).
  Apply Theorem \ref{MellinOfSmooth1b} to get the bound $1/(\epsilon |s|^2)$, which is bounded by $C'/\epsilon$.
  And $X^s$ is bounded by $X^{\sigma_1} = X \cdot X^{-A/ \log T^9}$.
  Putting these together gives the result.
  -/)
  (latexEnv := "lemma")]
lemma I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  sorry

@[blueprint
  (title := "I5Bound")
  (statement := /--
  We have that
  $$
  \left|I_{5}(\nu, \epsilon, X, \sigma_2)\right| \ll \frac{X^{\sigma_2}}{\epsilon}.
  $$
  -/)
  (proof := /--
  Here $\zeta'/\zeta$ is absolutely bounded on the compact interval $\sigma_2 + i [-3,3]$, and
  $X^s$ is bounded by $X^{\sigma_2}$. Using Theorem \ref{MellinOfSmooth1b} gives the bound $1/(\epsilon |s|^2)$, which is bounded by $C'/\epsilon$.
  Putting these together gives the result.
  -/)
  (latexEnv := "lemma")]
lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by
  sorry


blueprint_comment /--
\section{MediumPNT}

-/
set_option maxHeartbeats 400000 in
-- Slow
/-- *** Prime Number Theorem (Medium Strength) *** The `ChebyshevPsi` function is asymptotic to `x`. -/
@[blueprint
  (title := "MediumPNT")
  (statement := /--
    We have
  $$ \sum_{n \leq x} \Lambda(n) = x + O(x \exp(-c(\log x)^{1/10})).$$
  -/)
  (proof := /-- Evaluate the integrals. -/)]
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  sorry
