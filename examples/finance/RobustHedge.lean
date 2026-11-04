import Mathlib
-- Not used below: the two hedge cards load them from this project's build, which this keeps built.
import Gimle.Asgard.Compile.RationalInterchange
import Gimle.Asgard.Model.Continuous
import Gimle.Forseti.Examples.RobustCall
import Gimle.Forseti.Hedging

/-!
# A hedge that holds on every path in a band

A desk sells an at-the-money call: the right to buy one share of a stock at
$100$, the strike, when it trades at $100$ today, the spot. The call can be
exercised only at expiry, $20$ trading days away. The desk will hedge by
trading the stock once a day. The usual price comes from a model of
volatility, and the usual check of the hedge from a few thousand simulated
paths. The desk asks a different question, with no model of probability: if
the stock never moves by more than $2\,\%$ in a day, up or down, how much must
it take in so that its hedge pays the call on **every** such path, not on most
of them? And how much can a hedge sized for the wrong limit lose? Every price
below is per call on one share, in the units of the spot: a price of $1$ is
$1\,\%$ of the spot.

Call that limit on each day's move the band. For spot-feedback strategies,
those whose holding each day is set by the day and the stock's current price,
Lean settles the first question. The least premium from which a spot-feedback
strategy covers the call on every path in the band is $3.5549$, to four
places. From that premium the binomial hedge, defined below, ends at or above
the payoff on every such path; from $3.5$ no spot-feedback strategy does. The
second question stays partly open. A hedge sized for a band of $\pm 1\,\%$,
priced at $1.77$, leaves the seller's account $4.11$ below the payoff on the
zigzag, the path that rises and falls $2\,\%$ by turns, and more than $4.75$
below on another path of the $\pm 2\,\%$ band. How far short it can end is not
settled here.

**Sampled, not proved:** judged on its sample alone, that hedge would have
passed a loss limit of $4$: on $4000$ paths drawn uniformly from the
$\pm 2\,\%$ band, the seller's profit and loss at expiry was never worse than
$-1.86$. Yet the two paths above are proved to end $4.11$ and more than $4.75$
below the payoff. Under the same law, the seller's profit and loss with the
correctly sized hedge ended above zero on all $4000$ paths.

$$ \begin{array}{c|c} \text{claim} & \text{status} \\ \hline \begin{gathered}\text{covered from } 3.555,\\ \text{the price rounded up}\end{gathered} & \text{proved} \\ \hline \text{covered from } 3.5 & \text{refuted} \\ \hline \begin{gathered}\text{the } \pm 1\,\% \text{ hedge on}\\ \pm 2\,\% \text{ days, at most } 4\\ \text{below the payoff}\end{gathered} & \text{refuted} \\ \hline \begin{gathered}\text{the } \pm 1\,\% \text{ hedge on}\\ \pm 2\,\% \text{ days, at most } 5\\ \text{below the payoff}\end{gathered} & \text{unknown} \end{array} $$

- **Proved.** On every path whose $20$ daily moves stay within $\pm 2\,\%$, the
  binomial hedge started from the band's binomial price, about $3.5549$
  (`RobustCall.price_wide`, `table_2_percent`), ends at least at the call's
  payoff (`RobustCall.covered`), and so does the same hedge from a premium of
  $3.555$ (`covers_at_premium`, decided). That price is the least premium from
  which any spot-feedback strategy covers the call (`least_premium`).
- **Refuted.** That some spot-feedback strategy covers the call on every such
  path from a premium of $3.5$: none does (`covers_from_seven_halves_refuted`,
  decided; `RobustCall.not_from_seven_halves`). That the hedge sized for
  $\pm 1\,\%$ days, started from its own binomial price of about $1.7702$
  (`RobustCall.price_narrow`), ends at most $4$ below the payoff on every path
  of $\pm 2\,\%$ days: one path, the zigzag, leaves it about $4.1129$ below
  (`narrow_within_four_refuted`, decided; `RobustCall.zigzag_shortfall`,
  `zigzag_shortfall_decimal`). And that it ends at most $4.75$ below: another
  path of the band, one that is not extreme (an extreme path moves a full
  $2\,\%$, up or down, every day), leaves it about $4.7882$ below
  (`narrow_hedge_not_within_4_75`, by hand; `offset_shortfall`,
  `offset_shortfall_decimal`).
- **Unknown.** That the same hedge ends at most $5$ below the payoff on every
  path of $\pm 2\,\%$ days (the directive `narrow_within_five`). No theorem in
  the pinned forseti-lean settles it. Glitnir's hedging decider searched the
  extreme paths and found none worse than about $4.1129$, a search Lean does
  not check; a path that is not extreme is proved worse than $4.75$; and
  $4.7882$ is still short of $5$.
- **Not claimed.** Markets: the band is an assumption about the stock, the
  same every day; which band real moves keep to is not addressed, and a path
  that leaves it is outside every claim. Probability: no claim depends on how
  likely any path is, and none is about a distribution. Costs: the rate is
  zero, with no interest, dividend, financing or borrowing cost, no
  transaction cost and no bid-offer spread; holdings may be any real number,
  short or fractional, and cash is borrowed or lent without limit at the zero
  rate. Time: the position changes once a step, and a step is read as a
  trading day in the story only; nothing is continuous. Payoffs: European and
  convex, paid on the final spot: the call, the put and the straddle.
  Strategies: the lower bound is for spot-feedback strategies; a strategy that
  also reads the path so far is outside it. Cards: they sample moves under one
  law chosen here, uniform on the band, from one seed; another law gives other
  figures, and none of them is a proof.

## The hedge, as Lean states it

Write $S_k$ for the spot after $k$ steps, from $S_0 = 100$. The band of
$\pm 2\,\%$ says that each step's simple return stays within it,

$$ S_k\,(1 - d) \le S_{k+1} \le S_k\,(1 + u), \qquad u = d = \tfrac{1}{50}, $$

and nothing else: no probability is attached to a path. A seller takes in a
premium $w$ and holds $\delta_k(S_k)$ units of the stock over step $k$, a
spot-feedback strategy, borrowing or lending the rest at zero interest and
trading for free. The seller's wealth is the premium plus the trading gains,

$$ W_0 = w, \qquad W_{k+1} = W_k + \delta_k(S_k)\,(S_{k+1} - S_k), $$

and the strategy covers the call when $W_{20} \ge \max(S_{20} - 100, 0)$ on
every path in the band. That is `Covers wide (call 100) 20 δ w 100` in the
library, Forseti Lean's `Hedging`, with `wide` the band of $\pm 2\,\%$ from its
example module `RobustCall`; `narrow` is the band of $\pm 1\,\%$.

The binomial price is the recursion on the band's two ends, the
Cox–Ross–Rubinstein price with up factor $1 + u$ and down factor $1 - d$, for
the payoff $g$ with $n$ steps still to go:

$$ \begin{aligned} P_0(S) &= g(S), \\ P_{n+1}(S) &= q\,P_n\big(S(1 + u)\big) \\ &\quad + (1 - q)\,P_n\big(S(1 - d)\big), \\ q &= \frac{d}{u + d}. \end{aligned} $$

The weight $q$, here $1/2$, makes the two ends a fair bet; no statement reads
it as how often the stock rises. The binomial hedge ratio with $n + 1$ steps to
go is the slope of the chord of $P_n$ across the band,

$$ \Delta_n(S) = \frac{P_n\big(S(1 + u)\big) - P_n\big(S(1 - d)\big)}{S\,(u + d)}, $$

and the binomial hedge holds it over each step. It opens holding about
$0.5176$ units of the stock (`RobustCall.opening_ratio`).

Why it covers: the call is convex, so every $P_n$ is convex
(`price_convexOn`), and a convex function lies below its chord. For any move
inside the band, one hedged step therefore keeps the wealth at or above the
price with the steps still to go (`step_dominates`), whatever the move was.
Along a path in the band the wealth never falls below it (`wealth_ge_price`),
and at expiry it is at least the payoff (`covers_hedge`).

Why nothing cheaper: start a spot-feedback strategy below the price. Because
the two ends are a fair bet, whatever it holds over a step, one of the two ends
leaves its wealth below the price with the steps still to go, and the extreme
path that takes such an end at every step ends short of the payoff
(`exists_extreme_shortfall`, `not_covers_of_lt`). The two together make the
price the least premium from which a spot-feedback strategy covers
(`isLeast_price`): the seller's price, not a fair value, and nothing here
prices the call for a buyer. **Our reading, not proved:** it is the
bounded-move form of uncertain-volatility pricing.
-/
namespace Notebook.RobustHedge
open Gimle.Forseti.Hedging Gimle.Forseti.Examples.RobustCall

/-!
## Covered from 3.555 (proved)

The first claim is the sale itself, at a premium of $3.555$: the price rounded
up to three places. The hedging decider computes the binomial price exactly.
Its price stage found that the price, about $3.5549$, is at most the premium.
In the block it proposes, the kernel evaluates the exact price and compares it
with the premium; `covers_hedge` covers from the price, and `Covers.mono`
carries that up to the premium. The block that follows the directive is that
proposal, checked by Lean as part of this file; only that check makes it a
proof.
-/

-- @decide covers_at_premium : hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 3555/1000 covers
namespace Decided_covers_at_premium

open Gimle.Forseti.Hedging

def forsetiClaim : Prop :=
  Covers (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20
    (hedge (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20)
    (711/200) 100

/-- Sold for a premium of 3.555 (711/200) and hedged at the band's binomial hedge ratio, rebalanced at each of 20 steps with zero interest and no costs, the seller's account ends at least at the payoff of the call struck at 100 on every path from a spot of 100 whose simple returns stay within −2 % and +2 % (−1/50 and +1/50) a step. The hedging decider proved it. The binomial price at the band is 177744620736998422379605070486628497811/50000000000000000000000000000000000000 (≈ 3.5549); any premium of at least the price covers the payoff, 3.5549 (the price rounded up to four places) among them. Goal (hedging): hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 711/200 covers -/
theorem covers_at_premium :
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

end Decided_covers_at_premium

/-!
The price itself is an exact rational, which the kernel evaluates in the
library's `RobustCall.price_wide`, restated below with its decimal: between
$3.554$ and $3.555$. The premium is above it by about $0.0001$
(`table_2_percent` puts the price within $0.00005$ of $3.5549$). That cushion
is proved. **Our reading, not proved:** a realistic transaction cost or a
day's carry would exceed it.
-/

/-- The price of the at-the-money call over `20` steps of the band of two percent, as the
library's `RobustCall.price_wide` states it. -/
theorem exact_price : price wide (call 100) 20 100
    = 177744620736998422379605070486628497811 / 50000000000000000000000000000000000000 :=
  price_wide

/-- The price's decimal: between `3.554` and `3.555`. -/
theorem price_decimal :
    (3554 / 1000 : ℝ) < price wide (call 100) 20 100 ∧
      price wide (call 100) 20 100 < 3555 / 1000 := by
  rw [price_wide]
  norm_num

/-- The price is the least premium from which some spot-feedback strategy covers the call on
every path of the band of two percent: the library's `isLeast_price` for the call. -/
theorem least_premium :
    IsLeast {w | ∃ δ, Covers wide (call 100) 20 δ w 100} (price wide (call 100) 20 100) :=
  isLeast_price wide (call_convexOn 100) 20 (by norm_num)

/-!
## Covered from 3.5: refuted

Could the desk sell the call for $3.5$ and cover it with some cleverer
spot-feedback strategy? No. The decider refutes the claim in its strongest
form: the block's theorem says that no spot-feedback strategy covers the call
from $3.5$ on every path of the band. Its price stage found the premium below
the binomial price, about $3.5549$. In the block, the kernel compares the two,
and the library's `not_covers_of_lt` concludes; the library also states it for
this call as `RobustCall.not_from_seven_halves`.
-/

-- @decide covers_from_seven_halves : hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 7/2 covers
namespace Decided_covers_from_seven_halves

open Gimle.Forseti.Hedging

def forsetiClaim : Prop :=
  ∀ δ : ℕ → ℝ → ℝ,
    ¬ Covers (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 δ (7/2) 100

/-- Some spot-feedback strategy, holding over each step a number of units set by the step and the spot, keeps the seller's account at least at the payoff of the call struck at 100 on every path from a spot of 100 whose simple returns stay within −2 % and +2 % (−1/50 and +1/50) a step, from a premium of 3.5 (7/2), rebalanced at each of 20 steps with zero interest and no costs. The hedging decider refuted it. The premium is below the binomial price at the band, 177744620736998422379605070486628497811/50000000000000000000000000000000000000 (≈ 3.5549), the least premium from which any spot-feedback strategy covers the payoff. Goal (hedging): hedging call strike 100 spot 100 band down 1/50 up 1/50 steps 20 premium 7/2 covers -/
theorem covers_from_seven_halves_refuted : ¬ (∃ δ : ℕ → ℝ → ℝ,
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

end Decided_covers_from_seven_halves

/-!
The decider's stage report adds what the block does not state. The stage
invokes the replication identity (from the price, the band's own hedge ends
exactly at the payoff on every extreme path), and so reports that from $3.5$
the hedge ends about $0.0549$ below the payoff on each of them, the gap between
$3.5$ and the price. It names the path of $20$ rises of $2\,\%$ as one of
them. That is the decider's arithmetic, not a theorem here. The theorems are the library's:
`exists_extreme_shortfall` finds, for every spot-feedback strategy started
below the price, an extreme path on which it ends below the payoff, and
`not_covers_of_lt` concludes that no such strategy covers.

## The hedge on random paths (sampled)

The card below runs the same hedge, from the price, on $4000$ paths of $20$
daily returns. The card's own code runs it, not Lean: a float64
reimplementation of the library's hedge ratio, checked against Lean only
through the premium, which Lean prints exactly and the card recomputes. Each
day's return is drawn independently and uniformly from the band, the card's
default law and the simplest one on the band, by the card's seeded
generator, seed $7$. The chart is the seller's profit and loss at expiry, the
wealth less the payoff, by quantile: the x axis runs from the worst sampled
path to the best, not through time. Evidence, not proof.
-/

-- @evidence hedge Gimle.Forseti.Hedging.call (strike := 100) (spot := 100) (down := 1/50) (up := 1/50) (steps := 20) (law := uniform) (paths := 4000) (seed := 7)

/-!
On the card, from the premium, the binomial price of about $3.5549$, the
seller's profit and loss ended above zero on all $4000$ paths: the least at
$0.2578$, the median at $1.4796$ and the greatest at $3.1146$. The card's
$95\,\%$ Wilson interval, $0$ to $0.096\,\%$, is for the fraction of paths that
end below zero by more than a billionth of the spot under this law, computed
from this seed's $4000$ draws. `RobustCall.covered` already proves that no
path in the band ends below the payoff, so the interval adds nothing to the
proof; it is shown because the card reports it.

The proven floor is $0$. The card's least, $0.2578$, is not a floor: no theorem
here says the hedge keeps anything above $0$. **Our reading, not proved:** by
the replication identity the hedge ends at $0$ on every extreme path, and a
uniform draw almost never lands on an end of the band, so the sampled paths
miss the paths on which the floor is reached.

## The ±1 % hedge on ±2 % days, at most 4 below the payoff: refuted

Now the band is wrong. The desk sized its hedge for days of $\pm 1\,\%$: it
takes in that band's binomial price, about $1.7702$
(`RobustCall.price_narrow`), and holds that band's hedge ratios. The days turn
out to move by up to $\pm 2\,\%$. The shortfall on a path is how far the
seller's account ends below the payoff. The claim: on every path of the
$\pm 2\,\%$ band, the hedge ends at most $4$ below the payoff. The decider
searches the band's extreme paths for the one that leaves this hedge furthest
below the payoff. Its extreme-path stage found the zigzag, on which the
seller's account ends about $4.1129$ below the payoff. The search is not
checked; the block is: it states the zigzag's $20$ returns, and the kernel
evaluates the hedge along them, to the exact shortfall.
-/

-- @decide narrow_within_four : hedging call strike 100 spot 100 band down 1/100 up 1/100 steps 20 against down 1/50 up 1/50 shortfall <= 4
namespace Decided_narrow_within_four

open Gimle.Forseti.Hedging

def forsetiReturns : List ℚ := [1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50, 1/50, -1/50]

def forsetiClaim : Prop :=
  ∀ S : ℕ → ℝ, S 0 = 100 →
    (∀ k < 20, (Band.ofRat (1/50) (1/50) (by norm_num) (by norm_num) (by norm_num)).InBand (S k) (S (k + 1))) →
    -4 ≤ wealth (hedge (Band.ofRat (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20)
      (price (Band.ofRat (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num)) (call 100) 20 100) S 20 - call 100 (S 20)

/-- The hedge built for returns within −1 % and +1 % (−1/100 and +1/100) a step, started from its own price and rebalanced at each of 20 steps with zero interest and no costs, ends at most 4 below the payoff of the call struck at 100 (the seller's account less the payoff is at least −4) on every path from a spot of 100 whose simple returns stay within −2 % and +2 % (−1/50 and +1/50) a step. The hedging decider refuted it. On the zigzag (up and down by turns) of 20 steps of +2 % (+1/50) and −2 % (−1/50), the seller's account less the payoff ends at −215634705196340256271204096412694900382147731/52428800000000000000000000000000000000000000 (≈ −4.1129), below −4. Goal (hedging): hedging call strike 100 spot 100 band down 1/100 up 1/100 steps 20 against down 1/50 up 1/50 shortfall <= 4 -/
theorem narrow_within_four_refuted : ¬ (∀ S : ℕ → ℝ, S 0 = 100 →
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

end Decided_narrow_within_four

/-!
The library states the same path's exact shortfall over the reals
(`RobustCall.zigzag_shortfall`) and the refutation as a theorem of its own
(`RobustCall.narrow_hedge_not_within_four`); the decimal below puts the
account less the payoff within $0.00005$ of $-4.1129$, more than the $1.78$
between the two bands' prices. That $4.1129$ is net: the account starts with
the premium, about $+1.7702$; its trading gains are about $-5.8832$; and the
payoff is $0$, since the zigzag ends at about $99.6007$
(`RobustCall.zigzag_ends`), below the strike. That decomposition is arithmetic
on `zigzag_shortfall`, `price_narrow` and `zigzag_ends`, not a theorem.

**Our reading, not proved:** the seller is short a convex payoff, so the hedge
holds more stock after a rise and less after a fall. It buys high and sells
low, and the zigzag makes it do so at every step, with moves twice the size its
price was set for. The ratios are wrong, not only the premium: the wealth of a
fixed strategy moves one for one with its premium, so the same hedge started
from the wider band's price, $3.5549$, would still end about $2.33$ below the
payoff on the zigzag. That figure is arithmetic on the theorems' numbers, not a
theorem.
-/

/-- The account less the payoff on the zigzag path, as a decimal: within `0.00005` of
`-4.1129`. -/
theorem zigzag_shortfall_decimal :
    (-411295 / 100000 : ℝ)
        < wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
            (fun k => (zigzagSpot k : ℝ)) 20 - call 100 (zigzagSpot 20) ∧
      wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
            (fun k => (zigzagSpot k : ℝ)) 20 - call 100 (zigzagSpot 20)
        < -411285 / 100000 := by
  rw [zigzag_shortfall]
  norm_num

/-!
The zigzag is the worst extreme path the decider found, not the worst path of
the band. The path below first rises $1.35\,\%$, then falls and rises $2\,\%$ by
turns. Every return lies within $\pm 2\,\%$, so it is a path of the band, but
its first move does not reach an end, so it is not extreme. On it the
seller's account ends about $4.7882$ below the payoff, so a budget of $4.75$
fails too. The proof follows the library's `narrow_hedge_not_within_four`: the
returns lie in the band (`offset_inBand`, then `spotQ_inBand`), and the kernel
evaluates the hedge along them over the rationals (`wealth_hedge_cast`,
`call_cast`). The zigzag, a checked path of the band, gives a proved lower
bound of $4.1129$ on the worst case, and this path raises it past $4.75$; the
decider's search of the extreme paths gives no upper bound. By arithmetic on
the returns, not a theorem here, the path ends at about $98.966$, below the
strike.
-/

/-- Returns of `+1.35 %` at the first step, then `-2 %` and `+2 %` by turns. -/
def offsetZigzag (k : ℕ) : ℚ :=
  if k = 0 then 27 / 2000 else if k % 2 = 1 then -(1 / 50) else 1 / 50

/-- The first twenty of these returns lie within two percent. -/
theorem offset_inBand : ∀ k < 20, -(1 / 50 : ℚ) ≤ offsetZigzag k ∧ offsetZigzag k ≤ 1 / 50 := by
  decide +kernel

/-- Hedged for the narrow band from its price, the book ends about `4.7882` below the call
payoff on the path of these returns. -/
theorem offset_shortfall :
    wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
        (fun k => (spotQ 100 offsetZigzag k : ℝ)) 20 - call 100 (spotQ 100 offsetZigzag 20)
      = -5020803849242416135129911003500656238480441941
        / 1048576000000000000000000000000000000000000000 := by
  unfold narrow
  have hw := wealth_hedge_cast (fun S => call_cast 100 S) (1 / 100) (1 / 100) (by norm_num)
    (by norm_num) (by norm_num) 20 100 offsetZigzag 20
  have hc := call_cast 100 (spotQ 100 offsetZigzag 20)
  simp only [Rat.cast_ofNat] at hw hc
  rw [hw, hc]
  have hk : wealthQ (callQ 100) (1 / 100) (1 / 100) 20 100 offsetZigzag 20
      - callQ 100 (spotQ 100 offsetZigzag 20)
      = -5020803849242416135129911003500656238480441941
        / 1048576000000000000000000000000000000000000000 := by
    decide +kernel
  have := congrArg (Rat.cast : ℚ → ℝ) hk
  push_cast at this
  exact this

/-- The account less the payoff on that path, as a decimal: within `0.00005` of
`-4.7882`. -/
theorem offset_shortfall_decimal :
    (-478825 / 100000 : ℝ)
        < wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
            (fun k => (spotQ 100 offsetZigzag k : ℝ)) 20 - call 100 (spotQ 100 offsetZigzag 20) ∧
      wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
            (fun k => (spotQ 100 offsetZigzag k : ℝ)) 20 - call 100 (spotQ 100 offsetZigzag 20)
        < -478815 / 100000 := by
  rw [offset_shortfall]
  norm_num

/-- The hedge built for the narrow band does not end at most `4.75` below the call's payoff
on every path of the wide band: on the path of `offsetZigzag`, whose returns stay within
two percent, it ends more than `4.75` below. -/
theorem narrow_hedge_not_within_4_75 :
    ¬ ∀ S : ℕ → ℝ, S 0 = 100 → (∀ k < 20, wide.InBand (S k) (S (k + 1))) →
      -(475 / 100) ≤ wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100) S 20
        - call 100 (S 20) := by
  intro h
  have h0 : ((spotQ 100 offsetZigzag 0 : ℚ) : ℝ) = 100 := by norm_num [spotQ]
  have key := h (fun k => (spotQ 100 offsetZigzag k : ℝ)) h0
    (spotQ_inBand (S₀ := 100) (r := offsetZigzag) (N := 20) (1 / 50) (1 / 50) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) offset_inBand)
  rw [offset_shortfall] at key
  norm_num at key

/-!
The card below runs the hedge sized for $\pm 1\,\%$, from its own price, on
$4000$ paths of $20$ returns drawn independently and uniformly from the
$\pm 2\,\%$ band, seed $7$, in float64, as the first card does: the sampled
counterpart of the claim. Evidence, not proof.
-/

-- @evidence hedge Gimle.Forseti.Hedging.call (strike := 100) (spot := 100) (down := 1/100) (up := 1/100) (steps := 20) (against_down := 1/50) (against_up := 1/50) (law := uniform) (paths := 4000) (seed := 7)

/-!
On the card, from the narrower band's price of about $1.7702$, the seller's
profit and loss ends below zero by more than a billionth of the spot on $3548$
of the $4000$ paths; the card's $95\,\%$ Wilson interval for that fraction
under this law, computed from this seed's $4000$ draws, is $87.7\,\%$ to
$89.6\,\%$. The median ends at $-0.2534$, the least at $-1.8567$ and the
greatest at $0.9453$.

**Our reading, not proved:** a return uniform on $\pm 2\,\%$ has a standard
deviation of $2\,\%/\sqrt{3} \approx 1.15\,\%$ a step, close to the $1\,\%$ the
narrow hedge was priced for. This sample, under this law, would have passed a
budget of $4$: its worst path ended $1.86$ short. One path of the band is
proved to end $4.11$ below the payoff, and another more than $4.75$ below.

## The ±1 % hedge on ±2 % days, at most 5 below the payoff: unknown

The last claim gives the mis-sized hedge a budget of $5$. The decider's
search, not checked: its extreme-path stage reports that the worst extreme
path is again the zigzag, about $4.1129$ below the payoff, within $5$. The
stage on its own refutes only budgets below $4.1129$. It also names a `hedge`
card that samples the band's other paths; the second card above is one. The
decider's reason is `gap`. The path proved above to end $4.7882$ below the
payoff does not reach $5$ either, and no theorem in the pinned forseti-lean
bounds the shortfall over all paths of the band. So the claim stays unknown,
and no block follows.
-/

-- @decide narrow_within_five : hedging call strike 100 spot 100 band down 1/100 up 1/100 steps 20 against down 1/50 up 1/50 shortfall <= 5

/-!
## Price tables (proved)

The same price, by band at $20$ steps and by horizon in the band of
$\pm 2\,\%$, each row an exact rational of the library rounded to four places.
Each theorem below states its rounding as a bracket on the real price: the
price lies within $0.00005$ of the decimal shown.

$$ \begin{array}{c|c|c} \text{band} & \text{steps} & \text{price} \\ \hline \pm 1\,\% & 20 & 1.7702 \\ \pm 2\,\% & 20 & 3.5549 \\ \pm 3\,\% & 20 & 5.3506 \\ \hline \pm 2\,\% & 5 & 1.8745 \\ \pm 2\,\% & 60 & 6.1922 \\ \pm 2\,\% & 250 & 12.5705 \end{array} $$

At the money the put's binomial price is the call's, $3.5549$, and the
straddle's, which pays both, is twice that, $7.1098$.
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

/-- The put's binomial price at the money is the call's (`RobustCall.put_eq_call`): about
`3.5549`. -/
theorem table_put :
    (355485 / 100000 : ℝ) < price wide (put 100) 20 100 ∧
      price wide (put 100) 20 100 < 355495 / 100000 := by
  rw [put_eq_call, price_wide]
  norm_num

/-- The straddle's binomial price at the money: about `7.1098` (`RobustCall.price_straddle`). -/
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
is how an option's value grows with volatility and with time, and the band
plays the part of the volatility. In those terms, by arithmetic and the
standard Black–Scholes formula, with no claim about markets: moves to the
band's ends of $2\,\%$ a step are a volatility of $2\,\%$ a step, about
$31.7\,\%$ a year over $252$ steps; $\pm 1\,\%$ is about $15.9\,\%$ a year, and
the cards' uniform law on $\pm 2\,\%$ about $18.3\,\%$. The Black–Scholes price
of the $20$-step at-the-money call at $2\,\%$ a step and zero rate,
$S\,\big(N(d_1) - N(-d_1)\big)$ with $d_1 = 0.02\sqrt{20}/2$, is about $3.567$,
with delta $N(d_1)$ about $0.518$, against the band's $3.5549$ and $0.5176$.
So the mis-sized hedge is a hedge sized for about $16\,\%$ volatility, run on
paths that can move like $32\,\%$.

## What is and is not in the picture

Assuming nothing about the stock but a band on each day's move, in the
frictionless model of **Not claimed**, Lean proves a price from which the
binomial hedge covers the call on every path in the band, the awkward ones
included, and proves that no spot-feedback strategy covers from less. Lean
also proves that a wrong band can be costly: the hedge sized for $\pm 1\,\%$
days ends more than $4.75$ below the payoff on one path of $\pm 2\,\%$ days,
while the worst of $4000$ sampled paths ended $1.86$ short. How far short that
hedge can end over all paths of the band is unknown here. The band is the
assumption that carries everything, and **Not claimed**, at the top, lists what
none of these statements covers.
-/

#print axioms exact_price
#print axioms price_decimal
#print axioms least_premium
#print axioms zigzag_shortfall_decimal
#print axioms offset_inBand
#print axioms offset_shortfall
#print axioms offset_shortfall_decimal
#print axioms narrow_hedge_not_within_4_75
#print axioms table_1_percent
#print axioms table_2_percent
#print axioms table_3_percent
#print axioms table_5_steps
#print axioms table_60_steps
#print axioms table_250_steps
#print axioms table_put
#print axioms table_straddle

end Notebook.RobustHedge
