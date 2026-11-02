import Mathlib
import Gimle.Asgard.Examples.BurgersSquare
import Gimle.Asgard.Examples.PolynomialHeat
import Gimle.Asgard.Examples.BurgersFront
import Gimle.Asgard.Streams.ColeHopf

/-!
# Burgers: from a unique formal stream to a certified front

The viscous Burgers equation is

$$ u_t = -u\,u_x + \nu\,u_{xx}. $$

We first treat it as a formal power series in $t$ and $x$: exact rational
coefficients, with no convergence assumed. We then certify convergence and
bounds for one particular Cole–Hopf front.

**Proved here.** Formal uniqueness at $\nu = \tfrac{1}{10}$ for every profile,
circuit reconstruction from $x^2$, and the first coefficients. For the front
from $\varphi(0,x)=1+e^{-x}$ at $\nu=\tfrac12$, the series converges on
$|t|\le\tfrac16$, $|x|\le\tfrac18$. Its $16\times16$ truncation has error at
most $\tfrac{1}{16384}$; its sum is $1/(1+e^{x-t/2})$ and lies in
$[\tfrac25,\tfrac35]$ on that box.

**Refuted and unresolved.** The front's tighter upper bound $\tfrac{27}{50}$
is refuted at a corner of the box. The decider's $10^{-6}$ truncation request
on the same box remains unknown: failure to certify it is not a refutation.

**Scope.** The divergence discussion for the $x^2$ series is unformalized;
its finite numerical evidence is not a proof. The front's convergence and
closed-form identification apply only on the certified box. This notebook
does not prove that the closed form solves the real PDE, or address shocks
or the limit $\nu\to0$.

**Route.** Construct the formal stream, inspect its coefficients and limits,
certify the front's series, identify its sum, then inspect automated bounds.
[More Burgers fronts](BurgersFronts.lean) applies the decider to two other cases.

## Construct the unique formal stream {fold}

At $\nu=\tfrac{1}{10}$, equal initial profiles determine equal formal
streams. The circuit reconstructs exactly the stream from $x^2$; this is
formal uniqueness, with no convergence hypothesis or conclusion.

### Read the causal recurrence {fold}

Each new time coefficient depends only on earlier time degrees. Picard
iteration constructs the stream, and induction establishes uniqueness;
the library's general result allows every rational viscosity.

Write $u = \sum_{n,k} c_{n,k}\, t^n x^k$ and $[t^n x^k]$ for
$c_{n,k}$. The equation says

$$ (n+1)\, c_{n+1,k} = \nu\,(k+2)(k+1)\, c_{n,k+2} - \sum_{i+j=n}\ \sum_{a+b=k} c_{i,a}\,(b+1)\,c_{j,b+1}, $$

and the right-hand side involves only $t$-degrees $\le n$: the equation is
**causal** in $t$. The library proves this once for any causal right-hand side
(the formal Cauchy–Kowalevski lemma): **Picard iteration** along $t$ —
integrate the right-hand side of the previous iterate from the profile, again
and again — constructs a solution, and strong induction on the $t$-degree
shows there is no other with the same profile. Burgers is an instance because
sums, spatial derivatives and Cauchy products (products of series) are causal.

### Read the circuit interface {fold}

The circuit integrates the Burgers right-hand side from the boundary
profile. Its relation states that its candidate is the formal solution.
-/
namespace Notebook.Burgers
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Burgers Gimle.Asgard.Examples.BurgersSquare

/-!
The right-hand side $-u\,u_x + \nu\,u_{xx}$ is a stream expression in the
unknown: two spatial derivatives, a Cauchy product, two constants. The library
compiles it, integrates it along $t$ from the boundary profile, and proves
that the resulting circuit relates $[u, \text{profile}, \_]$ to
$[\text{rhs}\,u, u]$ exactly when $u$ is the formal solution. The third input
is unused; it is there because the heat circuit has the same shape.

In the Lean below, `rhs basis ν u` is the right-hand side as a function of the
stream `u`; `stream basis ν b` is the formal solution from the boundary
stream `b`; `ofPoly .ogf p` reads the polynomial `p` as a stream of ordinary
coefficients (the `.ogf` basis; `.egf` stores $n!\,k!$ times them); and an
index `Finsupp.single 0 n + Finsupp.single 1 k` is the monomial $t^n x^k$,
axis $0$ being $t$. `MvPolynomial.X 1 ^ 2` is $x^2$. The library fixes
`ν := 1/10` for its example, which is why the restatements below typecheck
with `1 / 10` written out.

### Check uniqueness and reconstruction {fold}

Two formal streams satisfying the equation with the same $t = 0$ slice are
equal. The claim is for $\nu = \tfrac{1}{10}$ and either basis; the library's
theorem is for every $\nu$.
-/

/-- Two formal Burgers solutions with the same profile are the same stream. -/
theorem uniqueness (basis : Basis) (a b : Stream 2)
    (ha : derivative basis 0 a = rhs basis (1 / 10) a)
    (hb : derivative basis 0 b = rhs basis (1 / 10) b)
    (slice : ∀ m : Index 2, m 0 = 0 → a m = b m) : a = b := by
  exact formal_unique basis (1 / 10) a b ha hb slice

/-- The compiled circuit reconstructs the constructed stream from `x²` … -/
theorem circuit_reconstructs (unused : Stream 2) :
    (circuit .ogf (1 / 10)).Rel
      ![stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2)),
        ofPoly .ogf (MvPolynomial.X 1 ^ 2), unused]
      ![rhs .ogf (1 / 10) (stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2))),
        stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2))] := by
  exact circuit_solution .ogf (1 / 10) _ unused

/-- … and nothing else: whatever it reconstructs from `x²` is that stream. -/
theorem from_circuit (a unused v : Stream 2)
    (rel : (circuit .ogf (1 / 10)).Rel ![a, ofPoly .ogf (MvPolynomial.X 1 ^ 2), unused] ![v, a]) :
    a = stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2)) := by
  exact candidate_stream .ogf (1 / 10) _ a unused v rel

/-!
## Inspect coefficients and the limits of formal reasoning {fold}

At $\nu=\tfrac{1}{10}$, the first coefficients from $x^2$ are exact and
rule out the heat stream $x^2+2t$. They do not establish convergence or
divergence. For affine data, only the first-iterate coefficient is checked.

### Compute the first coefficients from $x^2$ {fold}

Polynomial Picard iterates give the correct coefficients through their
iteration's time degree. Terms at higher degrees can still change.

From a polynomial profile every Picard iterate is a polynomial, and the
$n$-th iterate is right up to $t$-degree $n$. The library computes the first
three as polynomial identities:

$$ \begin{aligned} p_1 &= x^2 + t\Big(\tfrac15 - 2x^3\Big) \\ p_2 &= x^2 + t\Big(\tfrac15 - 2x^3\Big) + t^2\Big(-\tfrac45 x + 5x^4\Big) + t^3\Big(\tfrac25 x^2 - 4x^5\Big) \\ p_3 &= (p_2 \text{ up to } t^2) + t^3\Big(\tfrac{16}{5}x^2 - 14x^5\Big) + t^4(\cdots) + \dots + t^7(\cdots) \end{aligned} $$

The $t^3$ term of $p_2$, $\tfrac25 x^2 - 4x^5$, is an artefact of the
iteration; the true slice, $\tfrac{16}{5}x^2 - 14x^5$, appears in $p_3$,
whose own artefacts run from $t^4$ to $t^7$. That is the theorem made
visible: the $n$-th iterate is the stream up to degree $n$, and no further.
-/

/-- The coefficient of $t$ is $\tfrac15$: only the viscous term
$\nu\,(x^2)'' = \tfrac15$ contributes, since $u_0 u_0' = 2x^3$ has no constant
part (the library also checks that it is $0$ without viscosity). -/
theorem coefficient_t :
    stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2)) (Finsupp.single 0 1) = 1 / 5 := by
  exact coeff_t

/-- The coefficient of $t x^3$ is $-2$: only the nonlinearity contributes. -/
theorem coefficient_t_x3 :
    stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2))
      (Finsupp.single 0 1 + Finsupp.single 1 3) = -2 := by
  exact coeff_t_x3

/-- At $t^2$: the coefficients of $x$ and $x^4$ are $-\tfrac45$ and $5$. -/
theorem coefficients_t2 :
    stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2))
        (Finsupp.single 0 2 + Finsupp.single 1 1) = -4 / 5 ∧
      stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2))
        (Finsupp.single 0 2 + Finsupp.single 1 4) = 5 := by
  exact ⟨coeff_t2_x, coeff_t2_x4⟩

/-- At $t^3$: the coefficients of $x^2$ and $x^5$ are $\tfrac{16}{5}$ and $-14$,
from the third iterate, not from the second's artefact. -/
theorem coefficients_t3 :
    stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2))
        (Finsupp.single 0 3 + Finsupp.single 1 2) = 16 / 5 ∧
      stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2))
        (Finsupp.single 0 3 + Finsupp.single 1 5) = -14 := by
  exact ⟨coeff_t3_x2, coeff_t3_x5⟩

/-!
### Reject the proposed heat stream {fold}

The checked coefficient $[t]=\tfrac15$ rules out the proposed value $2$.
This is a proved negation, not a decider refutation.

The heat equation from the same profile has the polynomial solution
$x^2 + 2t$, so its $t$-coefficient is $2$. Burgers' is $\tfrac15$: the two
streams differ. This comparison also uses different diffusion coefficients:
$x^2+2t$ is the heat solution at viscosity $1$, whereas this Burgers stream
uses $\nu=\tfrac{1}{10}$. This theorem is
proved on this page from `coefficient_t` rather than restated.
-/

/-- The heat stream from `x²` is not the Burgers stream from `x²`. -/
theorem not_heat :
    Heat.stream .ogf (Polynomial.X ^ 2) ≠
      stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1 ^ 2)) := by
  intro same
  have := congrFun same (Finsupp.single 0 1)
  rw [coefficient_t, Heat.stream, Gimle.Asgard.Examples.PolynomialHeat.square, ofPoly_ogf_apply]
    at this
  simp [MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X, Finsupp.ext_iff, Fin.forall_fin_two,
    Finsupp.single_apply] at this
  norm_num at this

/-!
### Separate coefficient evidence from convergence {fold}

The growth discussion for $x^2$ is unformalized, and finite coefficient
ratios do not prove divergence. The affine example below checks only the
first iterate, not convergence of its series.

#### Why divergence is plausible for the quadratic profile {fold}

The numerical ratios and the classical Cole–Hopf explanation motivate a
radius-zero claim for nonzero viscosity. That claim is not proved here.

Exact arithmetic on the recurrence gives the $t$-slices $u_n(x)$ — the
coefficient of $t^n$, a polynomial in $x$: $x^2$, then $\tfrac15 - 2x^3$, then
$-\tfrac45 x + 5x^4$, then $\tfrac{16}{5}x^2 - 14x^5$, as checked in
**Compute the first coefficients from $x^2$**. The $x$-degree grows by one per
$t$-degree, so the slices' degrees repeat modulo three, and the coefficients
grow. With
$a_n = \sum_k |c_{n,k}|\,2^{-k}$, the norm of the slice on $|x| \le \tfrac12$,
the ratios $a_{n+3}/a_n$ at $n = 3, 9, 15, 21$ are

$$ \begin{array}{c|l|l} \nu & a_{n+3}/a_n \text{ at } n = 3, 9, 15, 21 & \\ \hline 0 & 3.8,\ 5.5,\ 6.3,\ 6.6 & \text{plateau} \\ \tfrac{1}{10} & 9.4,\ 16.4,\ 21.5,\ 25.8 & \text{increasing, no plateau} \\ \tfrac{1}{2} & 27,\ 48,\ 66,\ 83 & \text{increasing, no plateau} \end{array} $$

The plateau at $\nu = 0$ is what Cauchy–Kowalevski predicts for the inviscid
equation with analytic data.
These finite ratios suggest growth but do not prove divergence. The explanation is
the classical divergence of the formal heat series (Kowalevski's 1875 example)
transported by Cole–Hopf: $u = -2\nu\,\varphi_x/\varphi$ with
$\varphi_t = \nu\varphi_{xx}$ and $\varphi(0, x) = e^{-x^3/(6\nu)}$, an entire
function of order three, whose heat series diverges; that picture predicts
growth like $(n!)^{1/3}$ asymptotically, which these small $n$ do not yet
show. The explanation is from the literature, not proved here. Divergence
does not touch the theorem: the coefficients are exact and unique, which is
what a formal statement claims. Certified truncation needs a stream whose
series converges; the last sections have one, from a Cole–Hopf potential.

#### Check the affine profile's first iterate {fold}

For initial profile $x$, the first iterate is $x-tx$, so its $[tx]$
coefficient is $-1$. The closed form mentioned below is explanatory only.

Affine data is the exception: from $u(0, x) = x$ the solution is
$x/(1+t)$, the viscous term vanishes identically, and the first iterate is
$x - t x$, so $[t x] = -1$. Nothing beyond the first iterate is proved.
-/

/-- From `x`, the coefficient of $t x$ is $-1$: the start of $x/(1+t)$. -/
theorem affine_coefficient :
    stream .ogf (1 / 10) (ofPoly .ogf (MvPolynomial.X 1))
      (Finsupp.single 0 1 + Finsupp.single 1 1) = -1 := by
  have idx : (Finsupp.single 0 1 + Finsupp.single 1 1 : Index 2) 0 = 1 := by simp
  rw [stream_ogf_coeff, idx, show (1 / 10 : ℚ) = ν from rfl, picard_affine_one]
  simp [MvPolynomial.coeff_X, Finsupp.ext_iff, Finsupp.single_apply]

/-!
## Certify convergence and truncation for the front {fold}

For $\nu=\tfrac12$ and potential $1+e^{-x}$, the series converges on
$|t|\le\tfrac16$, $|x|\le\tfrac18$. The error beyond the $16\times16$
window is at most $\tfrac{1}{16384}$, a certified bound rather than an estimate.

### Explain the coefficient majorant {fold}

A bound on every coefficient gives absolute convergence and a uniform
tail bound on a smaller box. Rational side conditions certify each step.

Cole–Hopf turns a solution $\varphi$ of the heat equation
$\varphi_t = \nu\varphi_{xx}$ into a solution $u = -2\nu\,\varphi_x/\varphi$ of
Burgers. As formal streams this is exact: `Streams.ColeHopf.quotient_pde`
proves it from a Leibniz rule for the derivative of streams and the
derivative of the inverse; after those rules the identity is polynomial in
$\varphi_x, \varphi_{xx}, \varphi_{xxx}, \varphi^{-1}$ and closes by `ring`.
Classically, $\varphi(0, x) = 1 + e^{-x}$ and $\nu = \tfrac12$ give the front
$1/(1 + e^{x - t/2})$, a step from $1$ to $0$ moving right at speed $\tfrac12$;
the stream here is its formal series, and the section after the certificate
identifies the two on the box.

A majorant is an explicit bound $|c_{n,k}| \le M R_t^{-n} R_x^{-k}$ on every
coefficient. It makes the series converge for $|t| < R_t$, $|x| < R_x$, and it
bounds the tail beyond a window — the partial sum over $n < N_t$,
$k < N_x$ — uniformly on any smaller box. The heat stream of an exponential-sum
profile has such a majorant; a calculus of majorants carries it through the
derivative, the inverse (at radii where the non-constant part of $\varphi$ is
small against its constant term, a rational inequality) and the product
(which halves the radii); and the library's tail theorem turns the majorant
into the uniform error. Every side condition is a rational inequality the
kernel decides.

The numbers: the potential fits $\rho = 1$; the inverse is majorized at radii
$(\tfrac23, \tfrac12)$, where that inequality holds with equality; the product
halves them to $(\tfrac13, \tfrac14)$; on $|t| \le \tfrac16$, $|x| \le \tfrac18$ at
window $16 \times 16$ the certified error is
$\tfrac12 \cdot 2 \cdot 2^{-16} \cdot 4 = \tfrac{1}{16384}$. By the closed form
identified below (`front_field`), the true error on that box is near
$10^{-19}$ — a numerical estimate, not a theorem; the certificate is a proof
of a bound, not a measurement.

### Check the constant term, convergence and error {fold}

The front's constant coefficient is $\tfrac12$. The following claims establish
the error constant, summation on the box and the uniform truncation bound.
-/

/-- The front's constant coefficient, $-2\nu\,(\sum c_i a_i)/(\sum c_i)$, is $\tfrac12$ —
as the closed form's $u(0, 0)$ predicts. -/
theorem front_at_origin :
    MvPowerSeries.constantCoeff (ColeHopf.front (1 / 2) [(1, 0), (1, -1)]) = 1 / 2 := by
  exact Gimle.Asgard.Examples.BurgersFront.constantCoeff_front_eq

/-- The certified error at window $16 \times 16$ is exactly $\tfrac{1}{16384}$. -/
theorem front_error :
    tailBound (ColeHopf.frontMajorant (1 / 2) [(1, 0), (1, -1)] ![2 / 3, 1 / 2]
      Gimle.Asgard.Examples.BurgersFront.hr) Gimle.Asgard.Examples.BurgersFront.box ![16, 16] =
      1 / 16384 := by
  exact Gimle.Asgard.Examples.BurgersFront.error_eq

/-- **Convergent.** At every point of the box the series of the front sums to
its analytic field: absolute convergence, from the majorant. -/
theorem front_converges (x : Fin 2 → ℝ) (hx : Gimle.Asgard.Examples.BurgersFront.box.Mem x) :
    HasSum (seriesTerm .ogf (ColeHopf.front (1 / 2) [(1, 0), (1, -1)]) x)
      (analyticField .ogf (ColeHopf.front (1 / 2) [(1, 0), (1, -1)]) x) := by
  exact (ColeHopf.certificate Gimle.Asgard.Examples.BurgersFront.hν
    Gimle.Asgard.Examples.BurgersFront.hρ Gimle.Asgard.Examples.BurgersFront.terms
    Gimle.Asgard.Examples.BurgersFront.fits Gimle.Asgard.Examples.BurgersFront.hr
    Gimle.Asgard.Examples.BurgersFront.inside Gimle.Asgard.Examples.BurgersFront.small
    Gimle.Asgard.Examples.BurgersFront.box Gimle.Asgard.Examples.BurgersFront.boxInside).hasSum hx

/-- **Certified.** Whatever the Burgers circuit at $\nu = \tfrac12$ reconstructs
from the front's $t = 0$ slice differs from its $16 \times 16$ window by at
most $\tfrac{1}{16384}$ everywhere on $|t| \le \tfrac16$, $|x| \le \tfrac18$. -/
theorem front_certified :
    ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf (1 / 2)).Rel
        ![a, ColeHopf.zeroSlice (ColeHopf.front (1 / 2) [(1, 0), (1, -1)]), unused] ![v, a] →
        TruncationBound .ogf a Gimle.Asgard.Examples.BurgersFront.box ![16, 16] (1 / 16384) := by
  exact Gimle.Asgard.Examples.BurgersFront.bound

/-!
## Identify the sum and test its bounds {fold}

On the certified box, the analytic field equals $1/(1+e^{x-t/2})$ and lies
in $[\tfrac25,\tfrac35]$. The upper bound $\tfrac{27}{50}$ is false, with a
checked negation at $(t,x)=(\tfrac16,-\tfrac18)$.

Everything so far is about the series. Its analytic field — the sum at a real
point, what a plot shows — is now identified: on a box strictly inside the
radii of both factors' majorants, the field of a product is the product of
the fields (the
Cauchy product of two absolutely convergent double series, regrouped along
antidiagonals), the field of an inverse is the inverse of the field, and the
heat stream of an exponential sum sums to $\sum_i c_i e^{\nu a_i^2 t + a_i x}$
everywhere. On the certified box the front's field is therefore
$-2\nu\,\varphi_x/\varphi$ evaluated on the classical heat fields, which is
$1/(1 + e^{x - t/2})$ — the closed form that was only named above. That this
function solves the real Burgers equation is classical and not proved here;
what is proved is the equality of the field with it on the box.

Bounds then follow from one inequality, $s + 1 \le e^s$. On the box
$|x - t/2| \le \tfrac{5}{24}$, so $e^{\pm(x - t/2)} \ge \tfrac{19}{24}$, which gives
$\tfrac25 \le u \le \tfrac35$. The tighter $u \le \tfrac{27}{50}$ is false: at
the corner $(t, x) = (\tfrac16, -\tfrac18)$, $u = 1/(1 + e^{-5/24}) \ge \tfrac{29}{53} > \tfrac{27}{50}$.
Its negation is a checked theorem here, restated from the library's
`not_below`: a proved negation, like `not_heat`, not a decider refutation. The
decider's own answer to the same bound, from the series alone, is in the last
section (`front_band_refuted`).
-/

/-- **Identified.** On the box the front's analytic field is the closed form
$1/(1 + e^{x - t/2})$. -/
theorem front_field (x : Fin 2 → ℝ) (hx : Gimle.Asgard.Examples.BurgersFront.box.Mem x) :
    analyticField .ogf (ColeHopf.front (1 / 2) [(1, 0), (1, -1)]) x =
      1 / (1 + Real.exp (x 1 - x 0 / 2)) := by
  exact Gimle.Asgard.Examples.BurgersFront.front_field_eq hx

/-- **Bounded.** Whatever the circuit reconstructs from the front's slice has its
field in $[\tfrac25, \tfrac35]$ everywhere on the box. -/
theorem front_band :
    ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf (1 / 2)).Rel
        ![a, ColeHopf.zeroSlice (ColeHopf.front (1 / 2) [(1, 0), (1, -1)]), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, Gimle.Asgard.Examples.BurgersFront.box.Mem x →
          2 / 5 ≤ analyticField .ogf a x ∧ analyticField .ogf a x ≤ 3 / 5 := by
  exact Gimle.Asgard.Examples.BurgersFront.band

/-- **Refuted**, as a proved negation: $u \le \tfrac{27}{50}$ on the box fails at the
corner $(\tfrac16, -\tfrac18)$, where the front itself is at least $\tfrac{29}{53}$. -/
theorem front_not_below :
    ¬ ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf (1 / 2)).Rel
        ![a, ColeHopf.zeroSlice (ColeHopf.front (1 / 2) [(1, 0), (1, -1)]), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, Gimle.Asgard.Examples.BurgersFront.box.Mem x →
          analyticField .ogf a x ≤ 27 / 50 := by
  exact Gimle.Asgard.Examples.BurgersFront.not_below

/-!
## Inspect the automated certificates and their limits {fold}

On the same box, the decider certifies truncation at tolerance $10^{-4}$
and the band $[\tfrac25,\tfrac35]$, and refutes the upper bound
$\tfrac{27}{50}$. The $10^{-6}$ truncation request remains unknown.

### Certify the requested truncation {fold}

The decider finds a certificate for tolerance $10^{-4}$ on the $16\times16$
window. Its search chooses the certificate; Lean checks the proof it produces.

The claims above restate a certificate someone wrote by hand, in the library.
The stream decider writes one itself. A goal names the model `burgers`, its
viscosity, the potential's exponential sum, the output, the window, the box
and a tolerance $\varepsilon$; the decider chooses $\rho$ as for the heat
boundary and the radii of the inverse on a rational grid, mirrors the tail
bound exactly to find the pair with the least certified error, and hands
Lean the application of the
library's `front_truncation` with every side condition closed by kernel
computation. Lean's check of that application, re-run as part of this file,
is the only authority; the mirror only chooses.

Asked for $\varepsilon = 10^{-4}$, it finds $\rho = 1$ and the radii
$(\tfrac23, \tfrac12)$ of the example above, with the certified error
$\tfrac{1}{16384} < 10^{-4}$, and the claim it writes is checked. Asked for
$\varepsilon = 10^{-6}$ on the same box and window, no radii on its grid certify
it: the directive stays undecided, exhausted, and no claim is written — the
decider never refutes a truncation claim, because a majorant bound says
nothing about the true error, which by the closed form identified above is
far below $10^{-6}$ (a numerical estimate, not a theorem).
-/

-- @decide front_decided : stream burgers viscosity 1/2 interpretation analytic-tail
--   basis ogf potential exponentials [1, 0], [1, -1] truncation u window 16, 16
--   radius 1/6, 1/8 epsilon 1/10000

namespace Decided_front_decided

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 6), (mkRat (1) 8)], by decide +kernel⟩

def forsetiRoot : Prop :=
  (∃ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a]) ∧
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a] →
    (∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
      (Gimle.Asgard.Streams.analyticField .ogf a x)) ∧
    Gimle.Asgard.Streams.TruncationBound .ogf a forsetiBox ![16, 16] (mkRat (1) 10000)

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (2) 3), (mkRat (1) 2)]

/-- u is the stream the Burgers circuit at viscosity 1/2 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges on the box, and its window (16, 16) is within 1/10000 of the sum there. The stream decider proved it. Goal (stream): stream burgers viscosity 1/2 interpretation analytic-tail basis ogf potential exponentials [1, 0], [1, -1] truncation u window 16, 16 radius 1/6, 1/8 epsilon 1/10000 -/
theorem front_decided :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2)
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1)])
    (∃ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u]) ∧
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/6 ∧ |x| ≤ 1/8 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        |Gimle.Asgard.Streams.analyticField .ogf u ![t, x] -
          Gimle.Asgard.Streams.windowField .ogf ![16, 16] u ![t, x]| ≤ 1/10000 := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    refine ⟨⟨_, 0, _, Gimle.Asgard.Streams.ColeHopf.circuit_front ((mkRat (1) 2) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) 0⟩, fun a unused v rel => ⟨fun x hx => ?_, ?_⟩⟩
    · have hc : MvPowerSeries.constantCoeff (Gimle.Asgard.Streams.ColeHopf.expSumHeat ((mkRat (1) 2) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]) ≠ 0 := by
        rw [Gimle.Asgard.Streams.ColeHopf.constantCoeff_expSumHeat]
        decide +kernel
      simp only [Gimle.Asgard.Streams.ColeHopf.front] at rel
      rw [Gimle.Asgard.Streams.ColeHopf.candidate_quotient ((mkRat (1) 2) : ℚ) _ hc (Gimle.Asgard.Streams.ColeHopf.heatSeries_pde ((mkRat (1) 2) : ℚ) _) a unused v rel]
      exact (Gimle.Asgard.Streams.ColeHopf.certificate (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel)).hasSum hx
    · exact Gimle.Asgard.Streams.ColeHopf.front_truncation (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) a unused v rel
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] = Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2) = Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2) := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/6 ∧ |x| ≤ 1/8 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 10000) : ℚ) : ℝ) = (1/10000) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot
    rw [forsetiFront, forsetiCircuit]
    obtain ⟨realized, every⟩ := claim
    refine ⟨realized, fun u unused u_t rel => ⟨fun z inside => ?_, fun z inside => ?_⟩⟩
    all_goals
      have point : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl
      have holds := every u unused u_t rel (z 0) (z 1) ((forsetiInside _ _).mp (point ▸ inside))
      rw [point] at holds
    · exact holds.1
    · rw [forsetiCast0]
      exact holds.2
  · intro lane
    unfold forsetiRoot at lane
    rw [forsetiFront, forsetiCircuit] at lane
    dsimp only
    obtain ⟨realized, every⟩ := lane
    refine ⟨realized, fun u unused u_t rel t x inside => ?_⟩
    obtain ⟨sums, bound⟩ := every u unused u_t rel
    have mem := (forsetiInside t x).mpr inside
    have close := bound _ mem
    rw [forsetiCast0] at close
    exact ⟨sums _ mem, close⟩

/-!
### Leave the tighter truncation request unresolved {fold}

No radii on the search grid certify $10^{-6}$ for this box and window.
The request is unknown and has no claim card; it is not refuted.
-/

end Decided_front_decided


-- @decide front_tighter : stream burgers viscosity 1/2 interpretation analytic-tail
--   basis ogf potential exponentials [1, 0], [1, -1] truncation u window 16, 16
--   radius 1/6, 1/8 epsilon 1/1000000

/-!
### Certify a band from the series alone {fold}

A kernel-checked coefficient window and a tail bound certify
$\tfrac25\le u\le\tfrac35$ throughout the box, without using the closed form.

`front_band` above is the library's hand-made bound, through the closed form
and `Real.add_one_le_exp`. The decider has no closed form and uses none. A
field claim read as an analytic field, `u >= 2/5 and u <= 3/5` on the same
box, is answered from the series alone: the decider computes the window of
the potential's inverse below $16 \times 16$ by the triangular recurrence,
and Lean's kernel checks that table against the finite identity
$(\varphi \cdot Q)_\alpha = [\alpha = 0]$ — a wrong table loses the proof
and admits nothing. The front's window $W = -2\nu\,(\varphi_x \cdot Q)$
then satisfies $|W(t, x) - W_0| \le \sum_{\alpha \ne 0} |W_\alpha| r^\alpha$
on the box, and the certified error puts the field within
$\tfrac{1}{16384}$ of $W$. For this box that bound is
$[0.4477, 0.5523]$, inside $[\tfrac25, \tfrac35]$, and the claim is checked.

Asked whether $u \le \tfrac{27}{50}$, the decider evaluates $W$ exactly at
the corner $(\tfrac16, -\tfrac18)$, where it is $0.5519$, above the bound by
more than the error, and Lean checks the refutation: the front itself is one
reconstruction, and its field at that corner is within $\tfrac{1}{16384}$ of
$W$. The bound is conservative, so a band inside $[0.4477, 0.5523]$ that the
corners do not leave stays undecided; it is never refuted on that account.
-/

-- @decide front_band_decided : stream burgers viscosity 1/2 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1]
--   field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u >= 2/5 and u <= 3/5

namespace Decided_front_band_decided

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 6), (mkRat (1) 8)], by decide +kernel⟩

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (2) 3), (mkRat (1) 2)]

def forsetiTable : List (List ℚ) := [
    [(mkRat (1) 2), (mkRat (1) 4), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (1) 480), (mkRat (0) 1), (mkRat (-17) 80640), (mkRat (0) 1), (mkRat (31) 1451520), (mkRat (0) 1), (mkRat (-691) 319334400), (mkRat (0) 1), (mkRat (5461) 24908083200), (mkRat (0) 1), (mkRat (-929569) 41845579776000)],
    [(mkRat (-1) 8), (mkRat (0) 1), (mkRat (1) 32), (mkRat (0) 1), (mkRat (-1) 192), (mkRat (0) 1), (mkRat (17) 23040), (mkRat (0) 1), (mkRat (-31) 322560), (mkRat (0) 1), (mkRat (691) 58060800), (mkRat (0) 1), (mkRat (-5461) 3832012800), (mkRat (0) 1), (mkRat (929569) 5579410636800), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-1) 64), (mkRat (0) 1), (mkRat (1) 192), (mkRat (0) 1), (mkRat (-17) 15360), (mkRat (0) 1), (mkRat (31) 161280), (mkRat (0) 1), (mkRat (-691) 23224320), (mkRat (0) 1), (mkRat (5461) 1277337600), (mkRat (0) 1), (mkRat (-929569) 1594117324800), (mkRat (0) 1), (mkRat (3202291) 41845579776000)],
    [(mkRat (1) 384), (mkRat (0) 1), (mkRat (-1) 384), (mkRat (0) 1), (mkRat (17) 18432), (mkRat (0) 1), (mkRat (-31) 138240), (mkRat (0) 1), (mkRat (691) 15482880), (mkRat (0) 1), (mkRat (-5461) 696729600), (mkRat (0) 1), (mkRat (929569) 735746457600), (mkRat (0) 1), (mkRat (-3202291) 16738231910400), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (1) 1536), (mkRat (0) 1), (mkRat (-17) 36864), (mkRat (0) 1), (mkRat (31) 184320), (mkRat (0) 1), (mkRat (-691) 15482880), (mkRat (0) 1), (mkRat (5461) 557383680), (mkRat (0) 1), (mkRat (-929569) 490497638400), (mkRat (0) 1), (mkRat (3202291) 9564703948800), (mkRat (0) 1), (mkRat (-221930581) 4017175658496000)],
    [(mkRat (-1) 15360), (mkRat (0) 1), (mkRat (17) 122880), (mkRat (0) 1), (mkRat (-31) 368640), (mkRat (0) 1), (mkRat (691) 22118400), (mkRat (0) 1), (mkRat (-5461) 619315200), (mkRat (0) 1), (mkRat (929569) 445906944000), (mkRat (0) 1), (mkRat (-3202291) 7357464576000), (mkRat (0) 1), (mkRat (221930581) 2678117105664000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-17) 737280), (mkRat (0) 1), (mkRat (31) 1105920), (mkRat (0) 1), (mkRat (-691) 44236800), (mkRat (0) 1), (mkRat (5461) 928972800), (mkRat (0) 1), (mkRat (-929569) 535088332800), (mkRat (0) 1), (mkRat (3202291) 7357464576000), (mkRat (0) 1), (mkRat (-221930581) 2295528947712000), (mkRat (0) 1), (mkRat (4722116521) 241030539509760000)],
    [(mkRat (17) 10321920), (mkRat (0) 1), (mkRat (-31) 5160960), (mkRat (0) 1), (mkRat (691) 123863040), (mkRat (0) 1), (mkRat (-5461) 1857945600), (mkRat (0) 1), (mkRat (929569) 832359628800), (mkRat (0) 1), (mkRat (-3202291) 9364045824000), (mkRat (0) 1), (mkRat (221930581) 2472108097536000), (mkRat (0) 1), (mkRat (-4722116521) 224961836875776000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (31) 41287680), (mkRat (0) 1), (mkRat (-691) 495452160), (mkRat (0) 1), (mkRat (5461) 4954521600), (mkRat (0) 1), (mkRat (-929569) 1664719257600), (mkRat (0) 1), (mkRat (3202291) 14982473318400), (mkRat (0) 1), (mkRat (-221930581) 3296144130048000), (mkRat (0) 1), (mkRat (4722116521) 257099242143744000), (mkRat (0) 1), (mkRat (-968383680827) 215963363400744960000)],
    [(mkRat (-31) 743178240), (mkRat (0) 1), (mkRat (691) 2972712960), (mkRat (0) 1), (mkRat (-5461) 17836277760), (mkRat (0) 1), (mkRat (929569) 4280706662400), (mkRat (0) 1), (mkRat (-3202291) 29964946636800), (mkRat (0) 1), (mkRat (221930581) 5393690394624000), (mkRat (0) 1), (mkRat (-4722116521) 355983566045184000), (mkRat (0) 1), (mkRat (968383680827) 259156036080893952000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-691) 29727129600), (mkRat (0) 1), (mkRat (5461) 89181388800), (mkRat (0) 1), (mkRat (-929569) 14269022208000), (mkRat (0) 1), (mkRat (3202291) 74912366592000), (mkRat (0) 1), (mkRat (-221930581) 10787380789248000), (mkRat (0) 1), (mkRat (4722116521) 593305943408640000), (mkRat (0) 1), (mkRat (-968383680827) 370222908686991360000), (mkRat (0) 1), (mkRat (14717667114151) 19436702706067046400000)],
    [(mkRat (691) 653996851200), (mkRat (0) 1), (mkRat (-5461) 653996851200), (mkRat (0) 1), (mkRat (929569) 62783697715200), (mkRat (0) 1), (mkRat (-3202291) 235438866432000), (mkRat (0) 1), (mkRat (221930581) 26369153040384000), (mkRat (0) 1), (mkRat (-4722116521) 1186611886817280000), (mkRat (0) 1), (mkRat (968383680827) 626531076239523840000), (mkRat (0) 1), (mkRat (-14717667114151) 28507163968898334720000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (5461) 7847962214400), (mkRat (0) 1), (mkRat (-929569) 376702186291200), (mkRat (0) 1), (mkRat (3202291) 941755465728000), (mkRat (0) 1), (mkRat (-221930581) 79107459121152000), (mkRat (0) 1), (mkRat (4722116521) 2847868528361472000), (mkRat (0) 1), (mkRat (-968383680827) 1253062152479047680000), (mkRat (0) 1), (mkRat (14717667114151) 48869423946682859520000), (mkRat (0) 1), (mkRat (-2093660879252671) 20525158057606800998400000)],
    [(mkRat (-5461) 204047017574400), (mkRat (0) 1), (mkRat (929569) 3264752281190400), (mkRat (0) 1), (mkRat (-3202291) 4897128421785600), (mkRat (0) 1), (mkRat (221930581) 293827705307136000), (mkRat (0) 1), (mkRat (-4722116521) 8227175748599808000), (mkRat (0) 1), (mkRat (968383680827) 2961783269495930880000), (mkRat (0) 1), (mkRat (-14717667114151) 97738847893365719040000), (mkRat (0) 1), (mkRat (2093660879252671) 35576940633185121730560000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-929569) 45706531936665600), (mkRat (0) 1), (mkRat (3202291) 34279898952499200), (mkRat (0) 1), (mkRat (-221930581) 1371195958099968000), (mkRat (0) 1), (mkRat (4722116521) 28795115120099328000), (mkRat (0) 1), (mkRat (-968383680827) 8292993154588606464000), (mkRat (0) 1), (mkRat (14717667114151) 228057311751186677760000), (mkRat (0) 1), (mkRat (-2093660879252671) 71153881266370243461120000), (mkRat (0) 1), (mkRat (86125672563201181) 7471157532968875563417600000)],
    [(mkRat (929569) 1371195958099968000), (mkRat (0) 1), (mkRat (-3202291) 342798989524992000), (mkRat (0) 1), (mkRat (221930581) 8227175748599808000), (mkRat (0) 1), (mkRat (-4722116521) 123407636228997120000), (mkRat (0) 1), (mkRat (968383680827) 27643310515295354880000), (mkRat (0) 1), (mkRat (-14717667114151) 621974486594145484800000), (mkRat (0) 1), (mkRat (2093660879252671) 164201264460854407987200000), (mkRat (0) 1), (mkRat (-86125672563201181) 14942315065937751126835200000), (mkRat (0) 1)]]

def forsetiQ (k : Gimle.Asgard.Streams.Lowering.Degrees 2) : ℚ := (forsetiTable.getD (k 0) []).getD (k 1) 0

def forsetiRoot : Prop :=
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a] →
    ∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
        (Gimle.Asgard.Streams.analyticField .ogf a x) ∧
      (((mkRat (2) 5) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.analyticField .ogf a x ∧ Gimle.Asgard.Streams.analyticField .ogf a x ≤ (((mkRat (3) 5) : ℚ) : ℝ)

/-- u is the stream the Burgers circuit at viscosity 1/2 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges at every point of the box, and its sum, the analytic field, stays within the band there. The stream decider proved it. Goal (stream): stream burgers viscosity 1/2 interpretation analytic-field basis ogf potential exponentials [1, 0], [1, -1] field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u >= 2/5 and u <= 3/5 -/
theorem front_band_decided :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2)
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/6 ∧ |x| ≤ 1/8 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        2/5 ≤ Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 3/5 := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    intro a unused v rel x hx
    refine ⟨?_, (Gimle.Asgard.Streams.ColeHopf.front_band_of_window (lo := ((mkRat (2) 5) : ℚ)) (hi := ((mkRat (3) 5) : ℚ)) (ε := (mkRat (1) 16384)) (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) (by decide +kernel) (Q := forsetiQ) (by decide +kernel) (by decide +kernel) (by decide +kernel) a unused v rel x hx)⟩
    have hc : MvPowerSeries.constantCoeff (Gimle.Asgard.Streams.ColeHopf.expSumHeat ((mkRat (1) 2) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]) ≠ 0 := by
      rw [Gimle.Asgard.Streams.ColeHopf.constantCoeff_expSumHeat]
      decide +kernel
    simp only [Gimle.Asgard.Streams.ColeHopf.front] at rel
    rw [Gimle.Asgard.Streams.ColeHopf.candidate_quotient ((mkRat (1) 2) : ℚ) _ hc (Gimle.Asgard.Streams.ColeHopf.heatSeries_pde ((mkRat (1) 2) : ℚ) _) a unused v rel]
    exact (Gimle.Asgard.Streams.ColeHopf.certificate (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel)).hasSum hx
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] = Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2) = Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2) := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/6 ∧ |x| ≤ 1/8 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (2) 5) : ℚ) : ℝ) = (2/5) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (3) 5) : ℚ) : ℝ) = (3/5) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot
    rw [forsetiFront, forsetiCircuit]
    intro u unused u_t rel z inside
    have point : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl
    have holds := claim u unused u_t rel (z 0) (z 1) ((forsetiInside _ _).mp (point ▸ inside))
    rw [point] at holds
    set_option linter.unusedSimpArgs false in simp only [forsetiCast0, forsetiCast1]
    exact holds
  · intro lane
    unfold forsetiRoot at lane
    rw [forsetiFront, forsetiCircuit] at lane
    dsimp only
    intro u unused u_t rel t x inside
    have holds := lane u unused u_t rel ![t, x] ((forsetiInside t x).mpr inside)
    set_option linter.unusedSimpArgs false in simp only [forsetiCast0, forsetiCast1] at holds
    exact holds

/-!
### Refute the tighter upper bound {fold}

At $(t,x)=(\tfrac16,-\tfrac18)$, the window exceeds $\tfrac{27}{50}$ by more
than the certified error. Lean checks the counterexample; the positive claim
below remains refuted, not proved by its `sorry`.
-/

end Decided_front_band_decided


-- @decide front_band_refuted : stream burgers viscosity 1/2 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1]
--   field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u <= 27/50

namespace Decided_front_band_refuted

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 6), (mkRat (1) 8)], by decide +kernel⟩

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (2) 3), (mkRat (1) 2)]

def forsetiTable : List (List ℚ) := [
    [(mkRat (1) 2), (mkRat (1) 4), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (1) 480), (mkRat (0) 1), (mkRat (-17) 80640), (mkRat (0) 1), (mkRat (31) 1451520), (mkRat (0) 1), (mkRat (-691) 319334400), (mkRat (0) 1), (mkRat (5461) 24908083200), (mkRat (0) 1), (mkRat (-929569) 41845579776000)],
    [(mkRat (-1) 8), (mkRat (0) 1), (mkRat (1) 32), (mkRat (0) 1), (mkRat (-1) 192), (mkRat (0) 1), (mkRat (17) 23040), (mkRat (0) 1), (mkRat (-31) 322560), (mkRat (0) 1), (mkRat (691) 58060800), (mkRat (0) 1), (mkRat (-5461) 3832012800), (mkRat (0) 1), (mkRat (929569) 5579410636800), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-1) 64), (mkRat (0) 1), (mkRat (1) 192), (mkRat (0) 1), (mkRat (-17) 15360), (mkRat (0) 1), (mkRat (31) 161280), (mkRat (0) 1), (mkRat (-691) 23224320), (mkRat (0) 1), (mkRat (5461) 1277337600), (mkRat (0) 1), (mkRat (-929569) 1594117324800), (mkRat (0) 1), (mkRat (3202291) 41845579776000)],
    [(mkRat (1) 384), (mkRat (0) 1), (mkRat (-1) 384), (mkRat (0) 1), (mkRat (17) 18432), (mkRat (0) 1), (mkRat (-31) 138240), (mkRat (0) 1), (mkRat (691) 15482880), (mkRat (0) 1), (mkRat (-5461) 696729600), (mkRat (0) 1), (mkRat (929569) 735746457600), (mkRat (0) 1), (mkRat (-3202291) 16738231910400), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (1) 1536), (mkRat (0) 1), (mkRat (-17) 36864), (mkRat (0) 1), (mkRat (31) 184320), (mkRat (0) 1), (mkRat (-691) 15482880), (mkRat (0) 1), (mkRat (5461) 557383680), (mkRat (0) 1), (mkRat (-929569) 490497638400), (mkRat (0) 1), (mkRat (3202291) 9564703948800), (mkRat (0) 1), (mkRat (-221930581) 4017175658496000)],
    [(mkRat (-1) 15360), (mkRat (0) 1), (mkRat (17) 122880), (mkRat (0) 1), (mkRat (-31) 368640), (mkRat (0) 1), (mkRat (691) 22118400), (mkRat (0) 1), (mkRat (-5461) 619315200), (mkRat (0) 1), (mkRat (929569) 445906944000), (mkRat (0) 1), (mkRat (-3202291) 7357464576000), (mkRat (0) 1), (mkRat (221930581) 2678117105664000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-17) 737280), (mkRat (0) 1), (mkRat (31) 1105920), (mkRat (0) 1), (mkRat (-691) 44236800), (mkRat (0) 1), (mkRat (5461) 928972800), (mkRat (0) 1), (mkRat (-929569) 535088332800), (mkRat (0) 1), (mkRat (3202291) 7357464576000), (mkRat (0) 1), (mkRat (-221930581) 2295528947712000), (mkRat (0) 1), (mkRat (4722116521) 241030539509760000)],
    [(mkRat (17) 10321920), (mkRat (0) 1), (mkRat (-31) 5160960), (mkRat (0) 1), (mkRat (691) 123863040), (mkRat (0) 1), (mkRat (-5461) 1857945600), (mkRat (0) 1), (mkRat (929569) 832359628800), (mkRat (0) 1), (mkRat (-3202291) 9364045824000), (mkRat (0) 1), (mkRat (221930581) 2472108097536000), (mkRat (0) 1), (mkRat (-4722116521) 224961836875776000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (31) 41287680), (mkRat (0) 1), (mkRat (-691) 495452160), (mkRat (0) 1), (mkRat (5461) 4954521600), (mkRat (0) 1), (mkRat (-929569) 1664719257600), (mkRat (0) 1), (mkRat (3202291) 14982473318400), (mkRat (0) 1), (mkRat (-221930581) 3296144130048000), (mkRat (0) 1), (mkRat (4722116521) 257099242143744000), (mkRat (0) 1), (mkRat (-968383680827) 215963363400744960000)],
    [(mkRat (-31) 743178240), (mkRat (0) 1), (mkRat (691) 2972712960), (mkRat (0) 1), (mkRat (-5461) 17836277760), (mkRat (0) 1), (mkRat (929569) 4280706662400), (mkRat (0) 1), (mkRat (-3202291) 29964946636800), (mkRat (0) 1), (mkRat (221930581) 5393690394624000), (mkRat (0) 1), (mkRat (-4722116521) 355983566045184000), (mkRat (0) 1), (mkRat (968383680827) 259156036080893952000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-691) 29727129600), (mkRat (0) 1), (mkRat (5461) 89181388800), (mkRat (0) 1), (mkRat (-929569) 14269022208000), (mkRat (0) 1), (mkRat (3202291) 74912366592000), (mkRat (0) 1), (mkRat (-221930581) 10787380789248000), (mkRat (0) 1), (mkRat (4722116521) 593305943408640000), (mkRat (0) 1), (mkRat (-968383680827) 370222908686991360000), (mkRat (0) 1), (mkRat (14717667114151) 19436702706067046400000)],
    [(mkRat (691) 653996851200), (mkRat (0) 1), (mkRat (-5461) 653996851200), (mkRat (0) 1), (mkRat (929569) 62783697715200), (mkRat (0) 1), (mkRat (-3202291) 235438866432000), (mkRat (0) 1), (mkRat (221930581) 26369153040384000), (mkRat (0) 1), (mkRat (-4722116521) 1186611886817280000), (mkRat (0) 1), (mkRat (968383680827) 626531076239523840000), (mkRat (0) 1), (mkRat (-14717667114151) 28507163968898334720000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (5461) 7847962214400), (mkRat (0) 1), (mkRat (-929569) 376702186291200), (mkRat (0) 1), (mkRat (3202291) 941755465728000), (mkRat (0) 1), (mkRat (-221930581) 79107459121152000), (mkRat (0) 1), (mkRat (4722116521) 2847868528361472000), (mkRat (0) 1), (mkRat (-968383680827) 1253062152479047680000), (mkRat (0) 1), (mkRat (14717667114151) 48869423946682859520000), (mkRat (0) 1), (mkRat (-2093660879252671) 20525158057606800998400000)],
    [(mkRat (-5461) 204047017574400), (mkRat (0) 1), (mkRat (929569) 3264752281190400), (mkRat (0) 1), (mkRat (-3202291) 4897128421785600), (mkRat (0) 1), (mkRat (221930581) 293827705307136000), (mkRat (0) 1), (mkRat (-4722116521) 8227175748599808000), (mkRat (0) 1), (mkRat (968383680827) 2961783269495930880000), (mkRat (0) 1), (mkRat (-14717667114151) 97738847893365719040000), (mkRat (0) 1), (mkRat (2093660879252671) 35576940633185121730560000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-929569) 45706531936665600), (mkRat (0) 1), (mkRat (3202291) 34279898952499200), (mkRat (0) 1), (mkRat (-221930581) 1371195958099968000), (mkRat (0) 1), (mkRat (4722116521) 28795115120099328000), (mkRat (0) 1), (mkRat (-968383680827) 8292993154588606464000), (mkRat (0) 1), (mkRat (14717667114151) 228057311751186677760000), (mkRat (0) 1), (mkRat (-2093660879252671) 71153881266370243461120000), (mkRat (0) 1), (mkRat (86125672563201181) 7471157532968875563417600000)],
    [(mkRat (929569) 1371195958099968000), (mkRat (0) 1), (mkRat (-3202291) 342798989524992000), (mkRat (0) 1), (mkRat (221930581) 8227175748599808000), (mkRat (0) 1), (mkRat (-4722116521) 123407636228997120000), (mkRat (0) 1), (mkRat (968383680827) 27643310515295354880000), (mkRat (0) 1), (mkRat (-14717667114151) 621974486594145484800000), (mkRat (0) 1), (mkRat (2093660879252671) 164201264460854407987200000), (mkRat (0) 1), (mkRat (-86125672563201181) 14942315065937751126835200000), (mkRat (0) 1)]]

def forsetiQ (k : Gimle.Asgard.Streams.Lowering.Degrees 2) : ℚ := (forsetiTable.getD (k 0) []).getD (k 1) 0

def forsetiPoint : Fin 2 → ℚ := ![(mkRat (1) 6), (mkRat (-1) 8)]

def forsetiRoot : Prop :=
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a] →
    ∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
        (Gimle.Asgard.Streams.analyticField .ogf a x) ∧
      Gimle.Asgard.Streams.analyticField .ogf a x ≤ (((mkRat (27) 50) : ℚ) : ℝ)

/-- u is the stream the Burgers circuit at viscosity 1/2 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges at every point of the box, and its sum, the analytic field, stays within the band there. The stream decider refuted it. Goal (stream): stream burgers viscosity 1/2 interpretation analytic-field basis ogf potential exponentials [1, 0], [1, -1] field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u <= 27/50 -/
theorem front_band_refuted :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2)
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/6 ∧ |x| ≤ 1/8 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 27/50 := by
  sorry

theorem front_band_refuted_refuted : ¬ (have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2)
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/6 ∧ |x| ≤ 1/8 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 27/50) := by
  have refuted : ¬ forsetiRoot := by
    unfold forsetiRoot
    intro h
    exact Gimle.Asgard.Streams.ColeHopf.front_above_of_window (hi := ((mkRat (27) 50) : ℚ)) (ε := (mkRat (1) 16384)) (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) (by decide +kernel) (Q := forsetiQ) (by decide +kernel) forsetiPoint (by decide +kernel) (by decide +kernel) fun a unused v rel x hx => (h a unused v rel x hx).2
  intro claim
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] = Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2) = Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2) := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/6 ∧ |x| ≤ 1/8 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (27) 50) : ℚ) : ℝ) = (27/50) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => refuted (bridge.mp claim)) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot
    rw [forsetiFront, forsetiCircuit]
    intro u unused u_t rel z inside
    have point : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl
    have holds := claim u unused u_t rel (z 0) (z 1) ((forsetiInside _ _).mp (point ▸ inside))
    rw [point] at holds
    set_option linter.unusedSimpArgs false in simp only [forsetiCast0]
    exact holds
  · intro lane
    unfold forsetiRoot at lane
    rw [forsetiFront, forsetiCircuit] at lane
    dsimp only
    intro u unused u_t rel t x inside
    have holds := lane u unused u_t rel ![t, x] ((forsetiInside t x).mpr inside)
    set_option linter.unusedSimpArgs false in simp only [forsetiCast0] at holds
    exact holds

end Decided_front_band_refuted


end Notebook.Burgers

/-!
## Scope and unresolved requests

Formal uniqueness does not establish convergence. The $x^2$ divergence
explanation and the affine closed form are not proved here. For the selected
Cole–Hopf front, the series, truncation and field bounds are certified on the
stated box only; the real PDE identity is not formalized here.

The tighter truncation request `front_tighter` remains unknown. The positive
band request `front_band_refuted` is refuted by a checked witness, while
`front_not_below` is a checked theorem of the negation. Neither a failed
majorant search nor a numerical estimate is a proof of failure.
-/
