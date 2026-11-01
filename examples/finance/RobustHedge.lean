import Mathlib
-- Not used below: the two hedge cards load them from this project's build, which this keeps built.
import Gimle.Asgard.Compile.RationalInterchange
import Gimle.Asgard.Model.Continuous
import Gimle.Forseti.Examples.RobustCall
import Gimle.Forseti.Hedging

/-!
# A hedge that works on every path

A desk sells an at-the-money call: strike $100$, spot $100$, expiry in $20$
trading days. It will hedge by trading the stock once a day, at the close. The
usual price comes from a model of volatility, and the usual check of the hedge
from a few thousand simulated paths. The desk asks a different question, with no
model of probability at all: if the stock never moves by more than $2\,\%$ in a
day, up or down, how much must it take in so that the hedge pays the call on
**every** such path, not on most of them? And what does a hedge sized for the
wrong band lose?

Lean answers the first question exactly, and the second in part. The least
premium from which a spot-feedback strategy, one whose holding is set by the
day and the current price, hedges the call on every path whose daily moves stay
within $\pm 2\,\%$ is $3.5549$, to four places: from it the binomial hedge ends
at or above the call's payoff on every such path, and from $3.5$ no
spot-feedback strategy does. The hedge sized for $\pm 1\,\%$ days
costs only $1.77$, and on one path of $\pm 2\,\%$ days it ends $4.11$ below the
payoff.

$$ \begin{array}{c|c} \text{claim} & \text{status} \\ \hline \text{covered from } 3.555 & \text{proved} \\ \hline \text{covered from } 3.5 & \text{refuted} \\ \hline \begin{gathered}\text{the } \pm 1\,\% \text{ hedge}\\ \text{against } \pm 2\,\% \text{ moves,}\\ \text{shortfall} \le 4\end{gathered} & \text{refuted} \\ \hline \begin{gathered}\text{the } \pm 1\,\% \text{ hedge}\\ \text{against } \pm 2\,\% \text{ moves,}\\ \text{shortfall} \le 5\end{gathered} & \text{unknown} \end{array} $$

Sampled, not proved, on $4000$ paths each with moves drawn uniformly from the
band: the hedge from the price ended above zero on every path, and the
$\pm 1\,\%$ hedge on $\pm 2\,\%$ days ended at worst $1.86$ short, not $4.11$.

- **Proved.** On every path whose $20$ daily moves stay within $\pm 2\,\%$, the
  binomial hedge started from the price, about $3.5549$
  (`RobustCall.price_wide`, `table_2_percent`), ends at least at the call's
  payoff (`RobustCall.covered`), and so from a premium of $3.555$ too
  (`Decided_covered_from_premium.covered_from_premium`, decided). The price is
  the least such premium
  (`least_premium`).
- **Refuted.** From a premium of $3.5$, no spot-feedback strategy covers the
  call on every such path (`cheaper_refuted_refuted`, decided;
  `RobustCall.not_from_seven_halves`). The hedge sized for $\pm 1\,\%$ days,
  started from its own price of about $1.7702$ (`RobustCall.price_narrow`),
  stays within $4$ of the payoff on every path of $\pm 2\,\%$ days: refuted by
  one path, the zigzag, on which it ends about $4.1129$ below the payoff
  (`narrow_hedge_loses_refuted`, decided; `RobustCall.zigzag_shortfall`,
  `zigzag_loss_decimal`).
- **Unknown.** Whether that hedge stays within $5$ of the payoff on every path
  of $\pm 2\,\%$ days (the directive `narrow_hedge_five`). No theorem here
  bounds it: the decider's search of the extreme paths, which Lean does not
  check, found none worse than about $4.1129$, and nothing bounds the other
  paths.
- **Not claimed.** The band is an assumption about the stock, the same every
  day; a path that leaves it is outside every claim, and which band real moves
  keep to is not addressed. Nothing is claimed about markets, probabilities or
  distributions: no claim depends on how likely any path is. The rate is zero;
  there is no interest, dividend, financing or borrowing cost, no transaction
  cost and no bid-offer spread. The position changes once a step, and a step is
  read as a trading day in the story only: the statements are about steps, and
  nothing is continuous. The payoffs are European, paid on the final spot, and
  convex: the call, the put and the straddle. The lower bound is for
  spot-feedback strategies, which hold a number of units set by the step and
  the current spot; a strategy that also reads the path so far is outside it.
  The cards sample paths under a law of moves chosen here, uniform on the band;
  another law, or a Gaussian with another choice of its standard deviation,
  gives other figures, and none of them is a proof.

## The hedge, as Lean states it

Write $S_k$ for the spot after $k$ steps, from $S_0 = 100$. The band of
$\pm 2\,\%$ says that each step's simple return stays within it,

$$ S_k\,(1 - d) \le S_{k+1} \le S_k\,(1 + u), \qquad u = d = \tfrac{1}{50}, $$

and nothing else: no probability is attached to a path. A seller takes in a
premium $w$ and holds $\delta_k(S_k)$ units of the stock over step $k$, a number
set by the step and the current spot, borrowing or lending the rest at zero
interest and trading for free. The seller's wealth is the premium plus the
trading gains,

$$ W_0 = w, \qquad W_{k+1} = W_k + \delta_k(S_k)\,(S_{k+1} - S_k), $$

and the strategy covers the call when $W_{20} \ge \max(S_{20} - 100, 0)$ on
every path in the band. That is `Covers wide (call 100) 20 δ w 100` in the
library, Forseti Lean's `Hedging`, with `wide` the band of $\pm 2\,\%$ from its
example module `RobustCall`; `narrow` is the band of $\pm 1\,\%$.

The price is the binomial recursion on the band's two ends, the
Cox–Ross–Rubinstein price with up factor $1 + u$ and down factor $1 - d$:

$$ P_0(S) = g(S), \qquad P_{n+1}(S) = q\,P_n\big(S(1 + u)\big) + (1 - q)\,P_n\big(S(1 - d)\big), \qquad q = \frac{d}{u + d}, $$

for the payoff $g$, with $n$ the steps still to go. The weight $q$, here $1/2$,
makes the two ends a fair bet; no statement reads it as how often the stock
rises. The hedge holds the slope of the chord of $P_n$ across the band,

$$ \Delta_n(S) = \frac{P_n\big(S(1 + u)\big) - P_n\big(S(1 - d)\big)}{S\,(u + d)}, $$

with $n + 1$ steps to go. It opens holding about $0.5176$ units of the stock
(`RobustCall.opening_ratio`).

Why it covers: the call is convex, so every $P_n$ is convex
(`price_convexOn`), and a convex function lies below its chord. For any move
inside the band, one hedged step therefore keeps the wealth at or above the
price with the steps still to go (`step_dominates`), whatever the move was;
along a path in the band the wealth never falls below it (`wealth_ge_price`),
and at expiry it is at least the payoff (`covers_hedge`). Why no spot-feedback
strategy covers from less: start below the price, and because the two ends are
a fair bet, whatever such a strategy holds over a step, one of the two ends
leaves its wealth below the price with the steps still to go. The path that takes such an end at every step
ends short of the payoff (`exists_extreme_shortfall`, `not_covers_of_lt`). The
two together make the price the least premium that covers (`isLeast_price`):
the seller's price, the bounded-move form of uncertain-volatility pricing. It is
not a fair value, and nothing here prices the call for a buyer.
-/
namespace Notebook.RobustHedge
open Gimle.Forseti.Hedging Gimle.Forseti.Examples.RobustCall

/-!
## Covered from 3.555 (proved)

The first claim is the sale itself, at a premium of $3.555$: the price rounded
up to three places. The hedging decider computes the binomial price exactly;
its price stage found the price, about $3.5549$, at most the premium, and it
proposes a proof from the library's rules: the kernel evaluates the exact price
and compares it with the premium, `covers_hedge` covers from the price and
`Covers.mono` carries that up to the premium. The block that follows the
directive is that proposal, checked by Lean as part of this file; only that
check makes it a proof.
-/

-- @decide covered_from_premium : hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 3555/1000 covers
namespace Decided_covered_from_premium

open Gimle.Forseti.Hedging

def forsetiClaim : Prop :=
  Covers (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20
    (hedge (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20)
    (711/200) 100

/-- Sold for a premium of 3.555 (711/200) and hedged at the band's binomial hedge ratio, rebalanced at each of 20 steps with zero interest and no costs, the seller's account ends at least at the payoff of the call struck at 100 on every path from a spot of 100 whose simple returns stay within −2 % and +2 % (−1/50 and +1/50) a step. The hedging decider proved it. The binomial price at the band is 177744620736998422379605070486628497811/50000000000000000000000000000000000000 (≈ 3.5549); any premium of at least the price covers the payoff, 3.5549 (the price rounded up to four places) among them. Goal (hedging): hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 711/200 covers -/
theorem covered_from_premium :
    Covers (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20
      (hedge (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20)
      (711/200) 100 := by
  have root : forsetiClaim := by
    unfold forsetiClaim
    have hq : priceQ (callQ 100) (1/50) (1/50) 20 100 ≤ 711/200 := by decide +kernel
    have hr := Rat.cast_le (K := ℝ) |>.mpr hq
    have hp := price_cast (fun S => call_cast 100 S) (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num) 20 100
    push_cast at hp hr
    rw [← hp] at hr
    exact Covers.mono hr (covers_hedge (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call_convexOn 100) 20 (by norm_num))
  refine (fun (bridge : _ ↔ forsetiClaim) => bridge.mpr root) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_covered_from_premium

/-!
The price itself is an exact rational, which the kernel evaluates in the
library's `RobustCall.price_wide`. Restated here, with its decimal: it lies
between $3.554$ and $3.555$, so the premium $3.555$ is above it, by less than a
thousandth.
-/

/-- The price of the at-the-money call over `20` steps of the band of two percent, as the
library's `RobustCall.price_wide` states it. -/
theorem exact_price : price wide (call 100) 20 100
    = 177744620736998422379605070486628497811 / 50000000000000000000000000000000000000 :=
  price_wide

/-- The price's decimal: between `3.554` and `3.555`, the kernel comparing the rationals. -/
theorem price_decimal :
    (3554 / 1000 : ℚ)
        < 177744620736998422379605070486628497811 / 50000000000000000000000000000000000000 ∧
      (177744620736998422379605070486628497811 / 50000000000000000000000000000000000000 : ℚ)
        < 3555 / 1000 := by
  decide +kernel

/-- The price is the least premium from which some spot-feedback strategy covers the call on
every path of the band of two percent: the library's `isLeast_price` for the call. -/
theorem least_premium :
    IsLeast {w | ∃ δ, Covers wide (call 100) 20 δ w 100} (price wide (call 100) 20 100) :=
  isLeast_price wide (call_convexOn 100) 20 (by norm_num)

/-!
## Covered from 3.5: refuted

Could the desk sell the call for $3.5$, and hedge it some cleverer way, with a
holding set by the day and the current price? No.
The decider refutes the claim in its strongest form: the block's theorem says
that no spot-feedback strategy at all covers the call from $3.5$ on every path
of the band. Its price stage found the premium below the binomial price, about
$3.5549$; the block has the kernel compare the two and applies the library's
`not_covers_of_lt`, which the library also states for this call as
`RobustCall.not_from_seven_halves`.
-/

-- @decide cheaper_refuted : hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 7/2 covers
namespace Decided_cheaper_refuted

open Gimle.Forseti.Hedging

def forsetiClaim : Prop :=
  ∀ δ : ℕ → ℝ → ℝ,
    ¬ Covers (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 δ (7/2) 100

/-- Some spot-feedback strategy, holding over each step a number of units set by the step and the spot, keeps the seller's account at least at the payoff of the call struck at 100 on every path from a spot of 100 whose simple returns stay within −2 % and +2 % (−1/50 and +1/50) a step, from a premium of 3.5 (7/2), rebalanced at each of 20 steps with zero interest and no costs. The hedging decider refuted it. The premium is below the binomial price at the band, 177744620736998422379605070486628497811/50000000000000000000000000000000000000 (≈ 3.5549), the least premium from which any spot-feedback strategy covers the payoff. Goal (hedging): hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 7/2 covers -/
theorem cheaper_refuted_refuted : ¬ (∃ δ : ℕ → ℝ → ℝ,
      Covers (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 δ (7/2) 100) := by
  have refuted : forsetiClaim := by
    unfold forsetiClaim
    have hq : (7/2 : ℚ) < priceQ (callQ 100) (1/50) (1/50) 20 100 := by decide +kernel
    have hr := Rat.cast_lt (K := ℝ) |>.mpr hq
    have hp := price_cast (fun S => call_cast 100 S) (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num) 20 100
    push_cast at hp hr
    rw [← hp] at hr
    exact not_covers_of_lt (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 (by norm_num) hr
  intro claim
  refine (fun (bridge : _ ↔ ∃ δ : ℕ → ℝ → ℝ, Covers (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 δ (7/2) 100) => (not_exists.mpr refuted) (bridge.mp claim)) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_cheaper_refuted

/-!
The decider's stage report adds what the block does not state: from $3.5$ the
band's own hedge ends the difference, about $0.0549$, below the payoff on every
extreme path of the band, one that moves to an end of the band at every step,
by the replication identity; it names the path of $20$ rises of $2\,\%$ as one of
them. That is the decider's arithmetic, not a theorem here. The theorems are
the library's: `exists_extreme_shortfall` finds, for every spot-feedback
strategy started below the price, an extreme path on which it ends below the
payoff, and `not_covers_of_lt` concludes that no such strategy covers.

## The hedge on sampled paths (sampled)

The card below runs the same hedge, started from the price, on $4000$ paths
of $20$ daily returns drawn uniformly from the band, from seed $7$, in float64.
Its chart is the seller's profit and loss at expiry, the wealth less the
payoff, by quantile: the x axis runs from the worst sampled path to the best,
not through time. It is evidence, not proof.
-/

-- @evidence hedge Gimle.Forseti.Hedging.call (strike := 100) (spot := 100) (down := 1/50) (up := 1/50) (steps := 20) (law := uniform) (paths := 4000) (seed := 7)

/-!
On the card, from the premium, the binomial price of about $3.5549$, which
Lean printed and the provider recomputed exactly, every one of the $4000$
sampled paths ends above zero: the least at $0.2578$, the median at $1.4796$ and the greatest
at $3.1146$. None ends below zero by more than a billionth of the spot, and the
card's $95\,\%$ Wilson interval for that fraction is $0$ to $0.096\,\%$.
Evidence, not proof, and about these $4000$ draws only.

The proven floor is $0$: no path of the band ends below it
(`RobustCall.covered`). The card's least, $0.2578$, is not a floor: no theorem
here says the hedge keeps anything above $0$. **Our reading, not proved:** on
an extreme path the hedge from the price replicates the call exactly and ends
at $0$, the replication identity of the stage report above, and a uniform draw
almost never lands on an end of the band, so the sampled paths miss the
paths on which the floor is reached.
-/

/-!
## The ±1 % hedge on ±2 % days, within 4 of the payoff: refuted

Now the band is wrong. The desk sized its hedge for days of $\pm 1\,\%$: it
takes in that band's price, about $1.7702$ (`RobustCall.price_narrow`), and
holds that band's hedge ratios. The days turn out to move by up to
$\pm 2\,\%$. The claim: on every path of the wider band, the hedge ends at most
$4$ below the call's payoff. The decider searches the wider band's extreme
paths, those that move to one of its ends at every step, for the one that
leaves this hedge furthest below the payoff. Its extreme-path stage found the
zigzag, up $2\,\%$ and down $2\,\%$ by turns, on which the hedge ends about
$4.1129$ below the payoff, more than $4$. The search is not checked; the block
is: it states the zigzag's $20$ returns, and the kernel evaluates the hedge
along them, to the exact shortfall.
-/

-- @decide narrow_hedge_loses : hedging call strike 100 spot 100 band down 1/100 up 1/100 steps 20 against down 1/50 up 1/50 shortfall <= 4
namespace Decided_narrow_hedge_loses

open Gimle.Forseti.Hedging

def forsetiReturns : List ℚ := [1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50]

def forsetiClaim : Prop :=
  ∀ S : ℕ → ℝ, S 0 = 100 →
    (∀ k < 20, (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)).InBand (S k) (S (k + 1))) →
    -4 ≤ wealth (hedge (Band.ofRat (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20)
      (price (Band.ofRat (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 100) S 20 - call 100 (S 20)

/-- The hedge built for returns within −1 % and +1 % (−1/100 and +1/100) a step, started from its own price and rebalanced at each of 20 steps with zero interest and no costs, ends at most 4 below the payoff of the call struck at 100 (the seller's account less the payoff is at least −4) on every path from a spot of 100 whose simple returns stay within −2 % and +2 % (−1/50 and +1/50) a step. The hedging decider refuted it. On the zigzag (up and down by turns) of 20 steps of +2 % (+1/50) and −2 % (−1/50), the seller's account less the payoff ends at −215634705196340256271204096412694900382147731/52428800000000000000000000000000000000000000 (≈ −4.1129), below −4. Goal (hedging): hedging call strike 100 spot 100 band down 1/100 up 1/100 steps 20 against down 1/50 up 1/50 shortfall <= 4 -/
theorem narrow_hedge_loses_refuted : ¬ (∀ S : ℕ → ℝ, S 0 = 100 →
      (∀ k < 20, (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)).InBand (S k) (S (k + 1))) →
      -4 ≤ wealth (hedge (Band.ofRat (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20)
        (price (Band.ofRat (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 100) S 20 - call 100 (S 20)) := by
  have refuted : ¬ forsetiClaim := by
    unfold forsetiClaim
    intro h
    have hr : ∀ k < 20, -(1/50 : ℚ) ≤ forsetiReturns.getD k 0 ∧ forsetiReturns.getD k 0 ≤ 1/50 := by decide +kernel
    have h0 : ((spotQ 100 (fun k => forsetiReturns.getD k 0) 0 : ℚ) : ℝ) = 100 := by norm_num [spotQ]
    have key := h (fun k => ((spotQ 100 (fun k => forsetiReturns.getD k 0) k : ℚ) : ℝ)) h0 (spotQ_inBand (S₀ := 100) (N := 20) (r := fun k => forsetiReturns.getD k 0) (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr)
    have hw := wealth_hedge_cast (fun S => call_cast 100 S) (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num) 20 100 (fun k => forsetiReturns.getD k 0) 20
    have hc := call_cast 100 (spotQ 100 (fun k => forsetiReturns.getD k 0) 20)
    have hk : wealthQ (callQ 100) (1/100) (1/100) 20 100 (fun k => forsetiReturns.getD k 0) 20 - callQ 100 (spotQ 100 (fun k => forsetiReturns.getD k 0) 20) = -215634705196340256271204096412694900382147731/52428800000000000000000000000000000000000000 := by decide +kernel
    have hs := congrArg (Rat.cast : ℚ → ℝ) hk
    push_cast at hw hc hs
    linarith
  intro claim
  refine (fun (bridge : _ ↔ forsetiClaim) => refuted (bridge.mp claim)) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_narrow_hedge_loses

/-!
The library states the same path's exact shortfall over the reals
(`RobustCall.zigzag_shortfall`) and the refutation as a theorem of its own
(`RobustCall.narrow_hedge_not_within_four`). Its decimal: the kernel puts the
exact shortfall within $0.00005$ of $-4.1129$, so the hedge ends about $4.1129$
below the payoff, more than the $1.78$ between the two bands' prices. The
zigzag ends at about $99.6007$ (`RobustCall.zigzag_ends`), below the strike: the
call expires worthless, and all of the shortfall is hedging loss.

**Our reading, not proved:** the seller is short a convex payoff, so the hedge
holds more stock after a rise and less after a fall. It buys high and sells
low, and the zigzag makes it do so at every step, with moves twice the size its
price was set for. The ratios are wrong, not only the premium: the wealth of a
fixed strategy moves one for one with its premium, so the same hedge started
from the wider band's price, $3.5549$, would still end about $2.33$ short on
the zigzag. That figure is arithmetic on the theorems' numbers, not a theorem.
-/

/-- The decimal of the shortfall on the zigzag path: within `0.00005` of `-4.1129`, the kernel
comparing the rationals. -/
theorem zigzag_loss_decimal :
    (-411295 / 100000 : ℚ)
        < -215634705196340256271204096412694900382147731
          / 52428800000000000000000000000000000000000000 ∧
      (-215634705196340256271204096412694900382147731
          / 52428800000000000000000000000000000000000000 : ℚ) < -411285 / 100000 := by
  decide +kernel

/-!
The card below runs the hedge sized for $\pm 1\,\%$, from its own price, on
$4000$ paths of $20$ returns drawn uniformly from the wider band of $\pm 2\,\%$,
from seed $7$: the sampled counterpart of the claim. Evidence, not proof.
-/

-- @evidence hedge Gimle.Forseti.Hedging.call (strike := 100) (spot := 100) (down := 1/100) (up := 1/100) (steps := 20) (against_down := 1/50) (against_up := 1/50) (law := uniform) (paths := 4000) (seed := 7)

/-!
On the card, from the narrower band's price of about $1.7702$, the hedge ends
below zero by more than a billionth of the spot on $3548$ of the $4000$ paths
drawn from the wider band (the card's
$95\,\%$ Wilson interval for that fraction is $87.7\,\%$ to $89.6\,\%$); the
median ends at $-0.2534$, the least at $-1.8567$ and the greatest at $0.9453$.
Evidence, not proof. The worst of the $4000$ sampled paths ends $1.86$ short,
less than half of the $4.11$ that the zigzag costs, a shortfall that is
proved: drawn uniformly from the band, no sampled path came near the one that
refutes a budget of $4$, and the sample alone would have passed it.
-/

/-!
## The same hedge, within 5 of the payoff: unknown

The last claim gives the mis-sized hedge a budget of $5$. The decider's
extreme-path stage reports that the worst extreme path is again the zigzag,
which ends about $4.1129$ below the payoff, within the claimed $5$: it refutes
only budgets below $4.1129$. No theorem bounds the shortfall of a hedge sized
for a narrower band on the wider band's other paths, those that do not move to
its ends, and the decider says so instead of guessing (`gap`). Its reason
names the `hedge` card that samples those paths, as the second card above
does. No block follows.

**Our reading, not proved:** the worst case over the extreme paths is $4.11$.
That is the decider's search, which Lean does not check, and the card's worst
sampled path, $1.86$, lies well inside it; neither bounds the paths that do
not move to the band's ends.
-/

-- @decide narrow_hedge_five : hedging call strike 100 spot 100 band down 1/100 up 1/100 steps 20 against down 1/50 up 1/50 shortfall <= 5

/-!
## Price tables (proved)

The same price, by band at $20$ steps and by horizon in the band of
$\pm 2\,\%$, each row an exact rational of the library rounded to four places.
Each theorem below states its rounding as a bracket on the real price: the
price lies within $0.00005$ of the decimal shown.

$$ \begin{array}{c|c|c} \text{band} & \text{steps} & \text{price} \\ \hline \pm 1\,\% & 20 & 1.7702 \\ \pm 2\,\% & 20 & 3.5549 \\ \pm 3\,\% & 20 & 5.3506 \\ \hline \pm 2\,\% & 5 & 1.8745 \\ \pm 2\,\% & 60 & 6.1922 \\ \pm 2\,\% & 250 & 12.5705 \end{array} $$

At the money the put costs what the call does, $3.5549$, and the straddle,
which pays both, twice that, $7.1098$.
-/

/-- One percent a step over `20` steps: about `1.7702` (`RobustCall.price_narrow`). -/
theorem table_1_percent :
    (177015 / 100000 : ℝ) < price narrow (call 100) 20 100 ∧
      price narrow (call 100) 20 100 < 177025 / 100000 := by
  rw [price_narrow]
  norm_num

/-- Two percent a step over `20` steps: about `3.5549` (`RobustCall.price_wide`). -/
theorem table_2_percent :
    (355485 / 100000 : ℝ) < price wide (call 100) 20 100 ∧
      price wide (call 100) 20 100 < 355495 / 100000 := by
  rw [price_wide]
  norm_num

/-- Three percent a step over `20` steps: about `5.3506` (`RobustCall.price_three_percent`). -/
theorem table_3_percent :
    (535055 / 100000 : ℝ)
        < price (Band.ofRat (3 / 100) (3 / 100) (by norm_num) (by norm_num) (by norm_num))
          (call 100) 20 100 ∧
      price (Band.ofRat (3 / 100) (3 / 100) (by norm_num) (by norm_num) (by norm_num))
          (call 100) 20 100 < 535065 / 100000 := by
  rw [price_three_percent]
  norm_num

/-- Two percent a step over `5` steps: about `1.8745` (`RobustCall.price_five_days`). -/
theorem table_5_steps :
    (187445 / 100000 : ℝ) < price wide (call 100) 5 100 ∧
      price wide (call 100) 5 100 < 187455 / 100000 := by
  rw [price_five_days]
  norm_num

/-- Two percent a step over `60` steps: about `6.1922` (`RobustCall.price_sixty_days`). -/
theorem table_60_steps :
    (619215 / 100000 : ℝ) < price wide (call 100) 60 100 ∧
      price wide (call 100) 60 100 < 619225 / 100000 := by
  rw [price_sixty_days]
  norm_num

/-- Two percent a step over `250` steps: about `12.5705` (`RobustCall.price_year`). -/
theorem table_250_steps :
    (1257045 / 100000 : ℝ) < price wide (call 100) 250 100 ∧
      price wide (call 100) 250 100 < 1257055 / 100000 := by
  rw [price_year]
  norm_num

/-- The put at the money costs what the call does (`RobustCall.put_eq_call`): about `3.5549`. -/
theorem table_put :
    (355485 / 100000 : ℝ) < price wide (put 100) 20 100 ∧
      price wide (put 100) 20 100 < 355495 / 100000 := by
  rw [put_eq_call, price_wide]
  norm_num

/-- The straddle at the money: about `7.1098` (`RobustCall.price_straddle`). -/
theorem table_straddle :
    (710975 / 100000 : ℝ) < price wide (straddle 100) 20 100 ∧
      price wide (straddle 100) 20 100 < 710985 / 100000 := by
  rw [price_straddle]
  norm_num

/-!
**Our reading, not proved:** the price grows about in proportion to the band,
$1.77$, $3.55$, $5.35$ for $1$, $2$ and $3\,\%$, and about as the square root
of the steps: $5$ steps to $20$ is four times the steps and $1.9$ times the
price, $20$ to $250$ is $12.5$ times the steps and $3.5$ times the price. That
is how an option's value grows with volatility and with time; the band plays
the part of the volatility. The comparison is ours, not Lean's.

## What is and is not in the picture

A band of daily moves buys a price that holds on every path inside it, the
awkward ones included, and the same theorems say that nothing cheaper can, for
any spot-feedback strategy, one whose holding is set by the step and the
current spot. It also shows what a wrong band costs: the hedge sized for
$\pm 1\,\%$ days is short by more than $4$ on one path of $\pm 2\,\%$ days,
while the worst of $4000$ sampled paths was short by $1.86$. How short it can be
on the rest of the wider band is unknown here. The band itself is the
assumption that carries everything, and **Not claimed**, at the top, lists what
none of these statements covers.
-/

#print axioms exact_price
#print axioms price_decimal
#print axioms least_premium
#print axioms zigzag_loss_decimal
#print axioms table_1_percent
#print axioms table_2_percent
#print axioms table_3_percent
#print axioms table_5_steps
#print axioms table_60_steps
#print axioms table_250_steps
#print axioms table_put
#print axioms table_straddle

end Notebook.RobustHedge
