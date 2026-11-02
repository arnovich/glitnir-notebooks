import Mathlib
import Gimle.Asgard.Streams.ColeHopf

/-!
# Two more Burgers fronts: certificates, counterexamples and open requests

[Burgers](Burgers.lean) certifies one Cole–Hopf front. Here the same decider
handles two other cases: the potential $1+e^{-x}$ at viscosity $\nu=1$
(the fast front), and $1+e^{-x}+e^{-2x}$ at $\nu=\tfrac12$.

**Checked.** For the fast front, a $16\times16$ truncation reaches tolerance
$10^{-6}$ on $|t|\le\tfrac{1}{12}$, $|x|\le\tfrac{1}{16}$. Its field lies in
$[\tfrac{7}{10},\tfrac{13}{10}]$ on $|t|\le\tfrac16$, $|x|\le\tfrac18$ and in
$[\tfrac45,\tfrac65]$ on the smaller box. The two-exponential front lies in
$[\tfrac12,\tfrac32]$ on $|t|,|x|\le\tfrac{1}{16}$.

**Refuted.** The fast front's upper bound $u\le1$ on the larger box has a
checked counterexample at $(t,x)=(\tfrac16,-\tfrac18)$.

**Unknown.** On the larger box, the fast front's $[\tfrac45,\tfrac65]$ band
and the two-exponential front's $[\tfrac12,\tfrac32]$ band remain undecided.
Neither request has a claim card; neither is refuted.

**Route and scope.** Expand each case to compare its certificates and limits.
The proofs concern the formal front's analytic field on the specified boxes.
Closed-form explanations and numerical estimates below are not checked
identifications, and no real PDE identity, shocks or $\nu\to0$ limit are proved.
-/

namespace Notebook.BurgersFronts

/-!
## Inspect the fast front {fold}

At $\nu=1$, truncation and two field bands are certified on their stated
boxes. On the larger box, $u\le1$ is refuted and the narrower
$[\tfrac45,\tfrac65]$ band remains unknown.

### Understand the model and certificate method {fold}

The classical formula explains the example but is not identified by Lean
here. The decider uses general series certificates, not that closed form.

**The fast front.** The same potential $1 + e^{-x}$ at $\nu = 1$. The front
is $u = -2\nu\,\varphi_x/\varphi$ with $\varphi = 1 + e^{\nu t - x}$, so
classically $u = 2/(1 + e^{x - t})$: twice as high as at $\nu = \tfrac12$ and
moving twice as fast, with $u(0, 0) = 1$. (That closed form is not identified
by Lean on this page; it is here so that the reader can see what the
decider's bounds are bounds of. The decider never uses it.)

This page has no library example behind it. Nothing below restates a theorem
someone proved by hand about these fronts; every generated claim comes from
a `@decide` directive the stream decider answered from a one-line goal, with
proofs or refutations checked by Lean and saved observations retained for
replay. The roots it has,
asgard-lean's `front_truncation`, `front_band_of_window`,
`front_above_of_window` and `front_below_of_window`, quantify over the
viscosity and the exponential sum, so the decider can be asked about any
potential $\sum_i c_i e^{a_i x}$ with $\sum_i c_i \ne 0$ at any $\nu > 0$.
What it answers depends on where its conservative bound lands, and the page
shows that too.

### Certify truncation on the smaller box {fold}

On $|t|\le\tfrac{1}{12}$, $|x|\le\tfrac{1}{16}$, the $16\times16$ window
has error at most $10^{-6}$. The certificate's bound is about $4\cdot10^{-7}$.

The same goal shape as `front_decided` in `Burgers.lean`, at $\nu = 1$ and on
a smaller box, with a tolerance a hundred times tighter, the one `front_tighter`
could not reach on the larger box: the decider chooses
$\rho = 1$ and the inverse's radii $(\tfrac12, \tfrac13)$, and the certified
error is about $4 \cdot 10^{-7}$.
-/

-- @decide fast_truncation : stream burgers viscosity 1 interpretation analytic-tail
--   basis ogf potential exponentials [1, 0], [1, -1] truncation u window 16, 16
--   radius 1/12, 1/16 epsilon 1/1000000

namespace Decided_fast_truncation

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 12), (mkRat (1) 16)], by decide +kernel⟩

def forsetiRoot : Prop :=
  (∃ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a]) ∧
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a] →
    (∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
      (Gimle.Asgard.Streams.analyticField .ogf a x)) ∧
    Gimle.Asgard.Streams.TruncationBound .ogf a forsetiBox ![16, 16] (mkRat (1) 1000000)

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (1) 2), (mkRat (1) 3)]

/-- u is the stream the Burgers circuit at viscosity 1 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges on the box, and its window (16, 16) is within 1/1000000 of the sum there. The stream decider proved it. Goal (stream): stream burgers viscosity 1 interpretation analytic-tail basis ogf potential exponentials [1, 0], [1, -1] truncation u window 16, 16 radius 1/12, 1/16 epsilon 1/1000000 -/
theorem fast_truncation :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf 1
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)])
    (∃ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u]) ∧
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/12 ∧ |x| ≤ 1/16 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        |Gimle.Asgard.Streams.analyticField .ogf u ![t, x] -
          Gimle.Asgard.Streams.windowField .ogf ![16, 16] u ![t, x]| ≤ 1/1000000 := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    refine ⟨⟨_, 0, _, Gimle.Asgard.Streams.ColeHopf.circuit_front ((mkRat (1) 1) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) 0⟩, fun a unused v rel => ⟨fun x hx => ?_, ?_⟩⟩
    · have hc : MvPowerSeries.constantCoeff (Gimle.Asgard.Streams.ColeHopf.expSumHeat ((mkRat (1) 1) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]) ≠ 0 := by
        rw [Gimle.Asgard.Streams.ColeHopf.constantCoeff_expSumHeat]
        decide +kernel
      simp only [Gimle.Asgard.Streams.ColeHopf.front] at rel
      rw [Gimle.Asgard.Streams.ColeHopf.candidate_quotient ((mkRat (1) 1) : ℚ) _ hc (Gimle.Asgard.Streams.ColeHopf.heatSeries_pde ((mkRat (1) 1) : ℚ) _) a unused v rel]
      exact (Gimle.Asgard.Streams.ColeHopf.certificate (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel)).hasSum hx
    · exact Gimle.Asgard.Streams.ColeHopf.front_truncation (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) a unused v rel
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] = Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1) = Gimle.Asgard.Streams.Burgers.circuit .ogf 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/12 ∧ |x| ≤ 1/16 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 1000000) : ℚ) : ℝ) = (1/1000000) := by norm_num [Rat.mkRat_eq_div]
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

end Decided_fast_truncation


/-!
### Certify the wide band on the larger box {fold}

On $|t|\le\tfrac16$, $|x|\le\tfrac18$, the field lies in
$[\tfrac{7}{10},\tfrac{13}{10}]$. A narrower request remains unknown,
while the upper bound $1$ has a counterexample.

On the large box the certified error is $0.139$ and the window's bound is
$[0.71, 1.29]$. The wide band is checked; the narrower requested band
$[\tfrac45, \tfrac65]$ is left undecided, with the decider's interval in its
reason; and $u \le 1$
is refuted at the corner $(\tfrac16, -\tfrac18)$, where the window is $1.145$.
-/

-- @decide fast_band : stream burgers viscosity 1 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1]
--   field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u >= 7/10 and u <= 13/10

namespace Decided_fast_band

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 6), (mkRat (1) 8)], by decide +kernel⟩

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (1) 2), (mkRat (1) 3)]

def forsetiTable : List (List ℚ) := [
    [(mkRat (1) 2), (mkRat (1) 4), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (1) 480), (mkRat (0) 1), (mkRat (-17) 80640), (mkRat (0) 1), (mkRat (31) 1451520), (mkRat (0) 1), (mkRat (-691) 319334400), (mkRat (0) 1), (mkRat (5461) 24908083200), (mkRat (0) 1), (mkRat (-929569) 41845579776000)],
    [(mkRat (-1) 4), (mkRat (0) 1), (mkRat (1) 16), (mkRat (0) 1), (mkRat (-1) 96), (mkRat (0) 1), (mkRat (17) 11520), (mkRat (0) 1), (mkRat (-31) 161280), (mkRat (0) 1), (mkRat (691) 29030400), (mkRat (0) 1), (mkRat (-5461) 1916006400), (mkRat (0) 1), (mkRat (929569) 2789705318400), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-1) 16), (mkRat (0) 1), (mkRat (1) 48), (mkRat (0) 1), (mkRat (-17) 3840), (mkRat (0) 1), (mkRat (31) 40320), (mkRat (0) 1), (mkRat (-691) 5806080), (mkRat (0) 1), (mkRat (5461) 319334400), (mkRat (0) 1), (mkRat (-929569) 398529331200), (mkRat (0) 1), (mkRat (3202291) 10461394944000)],
    [(mkRat (1) 48), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (17) 2304), (mkRat (0) 1), (mkRat (-31) 17280), (mkRat (0) 1), (mkRat (691) 1935360), (mkRat (0) 1), (mkRat (-5461) 87091200), (mkRat (0) 1), (mkRat (929569) 91968307200), (mkRat (0) 1), (mkRat (-3202291) 2092278988800), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (1) 96), (mkRat (0) 1), (mkRat (-17) 2304), (mkRat (0) 1), (mkRat (31) 11520), (mkRat (0) 1), (mkRat (-691) 967680), (mkRat (0) 1), (mkRat (5461) 34836480), (mkRat (0) 1), (mkRat (-929569) 30656102400), (mkRat (0) 1), (mkRat (3202291) 597793996800), (mkRat (0) 1), (mkRat (-221930581) 251073478656000)],
    [(mkRat (-1) 480), (mkRat (0) 1), (mkRat (17) 3840), (mkRat (0) 1), (mkRat (-31) 11520), (mkRat (0) 1), (mkRat (691) 691200), (mkRat (0) 1), (mkRat (-5461) 19353600), (mkRat (0) 1), (mkRat (929569) 13934592000), (mkRat (0) 1), (mkRat (-3202291) 229920768000), (mkRat (0) 1), (mkRat (221930581) 83691159552000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-17) 11520), (mkRat (0) 1), (mkRat (31) 17280), (mkRat (0) 1), (mkRat (-691) 691200), (mkRat (0) 1), (mkRat (5461) 14515200), (mkRat (0) 1), (mkRat (-929569) 8360755200), (mkRat (0) 1), (mkRat (3202291) 114960384000), (mkRat (0) 1), (mkRat (-221930581) 35867639808000), (mkRat (0) 1), (mkRat (4722116521) 3766102179840000)],
    [(mkRat (17) 80640), (mkRat (0) 1), (mkRat (-31) 40320), (mkRat (0) 1), (mkRat (691) 967680), (mkRat (0) 1), (mkRat (-5461) 14515200), (mkRat (0) 1), (mkRat (929569) 6502809600), (mkRat (0) 1), (mkRat (-3202291) 73156608000), (mkRat (0) 1), (mkRat (221930581) 19313344512000), (mkRat (0) 1), (mkRat (-4722116521) 1757514350592000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (31) 161280), (mkRat (0) 1), (mkRat (-691) 1935360), (mkRat (0) 1), (mkRat (5461) 19353600), (mkRat (0) 1), (mkRat (-929569) 6502809600), (mkRat (0) 1), (mkRat (3202291) 58525286400), (mkRat (0) 1), (mkRat (-221930581) 12875563008000), (mkRat (0) 1), (mkRat (4722116521) 1004293914624000), (mkRat (0) 1), (mkRat (-968383680827) 843606888284160000)],
    [(mkRat (-31) 1451520), (mkRat (0) 1), (mkRat (691) 5806080), (mkRat (0) 1), (mkRat (-5461) 34836480), (mkRat (0) 1), (mkRat (929569) 8360755200), (mkRat (0) 1), (mkRat (-3202291) 58525286400), (mkRat (0) 1), (mkRat (221930581) 10534551552000), (mkRat (0) 1), (mkRat (-4722116521) 695280402432000), (mkRat (0) 1), (mkRat (968383680827) 506164132970496000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-691) 29030400), (mkRat (0) 1), (mkRat (5461) 87091200), (mkRat (0) 1), (mkRat (-929569) 13934592000), (mkRat (0) 1), (mkRat (3202291) 73156608000), (mkRat (0) 1), (mkRat (-221930581) 10534551552000), (mkRat (0) 1), (mkRat (4722116521) 579400335360000), (mkRat (0) 1), (mkRat (-968383680827) 361545809264640000), (mkRat (0) 1), (mkRat (14717667114151) 18981154986393600000)],
    [(mkRat (691) 319334400), (mkRat (0) 1), (mkRat (-5461) 319334400), (mkRat (0) 1), (mkRat (929569) 30656102400), (mkRat (0) 1), (mkRat (-3202291) 114960384000), (mkRat (0) 1), (mkRat (221930581) 12875563008000), (mkRat (0) 1), (mkRat (-4722116521) 579400335360000), (mkRat (0) 1), (mkRat (968383680827) 305923377070080000), (mkRat (0) 1), (mkRat (-14717667114151) 13919513656688640000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (5461) 1916006400), (mkRat (0) 1), (mkRat (-929569) 91968307200), (mkRat (0) 1), (mkRat (3202291) 229920768000), (mkRat (0) 1), (mkRat (-221930581) 19313344512000), (mkRat (0) 1), (mkRat (4722116521) 695280402432000), (mkRat (0) 1), (mkRat (-968383680827) 305923377070080000), (mkRat (0) 1), (mkRat (14717667114151) 11931011705733120000), (mkRat (0) 1), (mkRat (-2093660879252671) 5011024916407910400000)],
    [(mkRat (-5461) 24908083200), (mkRat (0) 1), (mkRat (929569) 398529331200), (mkRat (0) 1), (mkRat (-3202291) 597793996800), (mkRat (0) 1), (mkRat (221930581) 35867639808000), (mkRat (0) 1), (mkRat (-4722116521) 1004293914624000), (mkRat (0) 1), (mkRat (968383680827) 361545809264640000), (mkRat (0) 1), (mkRat (-14717667114151) 11931011705733120000), (mkRat (0) 1), (mkRat (2093660879252671) 4342888260886855680000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-929569) 2789705318400), (mkRat (0) 1), (mkRat (3202291) 2092278988800), (mkRat (0) 1), (mkRat (-221930581) 83691159552000), (mkRat (0) 1), (mkRat (4722116521) 1757514350592000), (mkRat (0) 1), (mkRat (-968383680827) 506164132970496000), (mkRat (0) 1), (mkRat (14717667114151) 13919513656688640000), (mkRat (0) 1), (mkRat (-2093660879252671) 4342888260886855680000), (mkRat (0) 1), (mkRat (86125672563201181) 456003267393119846400000)],
    [(mkRat (929569) 41845579776000), (mkRat (0) 1), (mkRat (-3202291) 10461394944000), (mkRat (0) 1), (mkRat (221930581) 251073478656000), (mkRat (0) 1), (mkRat (-4722116521) 3766102179840000), (mkRat (0) 1), (mkRat (968383680827) 843606888284160000), (mkRat (0) 1), (mkRat (-14717667114151) 18981154986393600000), (mkRat (0) 1), (mkRat (2093660879252671) 5011024916407910400000), (mkRat (0) 1), (mkRat (-86125672563201181) 456003267393119846400000), (mkRat (0) 1)]]

def forsetiQ (k : Gimle.Asgard.Streams.Lowering.Degrees 2) : ℚ := (forsetiTable.getD (k 0) []).getD (k 1) 0

def forsetiRoot : Prop :=
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a] →
    ∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
        (Gimle.Asgard.Streams.analyticField .ogf a x) ∧
      (((mkRat (7) 10) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.analyticField .ogf a x ∧ Gimle.Asgard.Streams.analyticField .ogf a x ≤ (((mkRat (13) 10) : ℚ) : ℝ)

/-- u is the stream the Burgers circuit at viscosity 1 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges at every point of the box, and its sum, the analytic field, stays within the band there. The stream decider proved it. Goal (stream): stream burgers viscosity 1 interpretation analytic-field basis ogf potential exponentials [1, 0], [1, -1] field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u >= 7/10 and u <= 13/10 -/
theorem fast_band :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf 1
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/6 ∧ |x| ≤ 1/8 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        7/10 ≤ Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 13/10 := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    intro a unused v rel x hx
    refine ⟨?_, (Gimle.Asgard.Streams.ColeHopf.front_band_of_window (lo := ((mkRat (7) 10) : ℚ)) (hi := ((mkRat (13) 10) : ℚ)) (ε := (mkRat (2134495165562497) 15407021574586368)) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) (by decide +kernel) (Q := forsetiQ) (by decide +kernel) (by decide +kernel) (by decide +kernel) a unused v rel x hx)⟩
    have hc : MvPowerSeries.constantCoeff (Gimle.Asgard.Streams.ColeHopf.expSumHeat ((mkRat (1) 1) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]) ≠ 0 := by
      rw [Gimle.Asgard.Streams.ColeHopf.constantCoeff_expSumHeat]
      decide +kernel
    simp only [Gimle.Asgard.Streams.ColeHopf.front] at rel
    rw [Gimle.Asgard.Streams.ColeHopf.candidate_quotient ((mkRat (1) 1) : ℚ) _ hc (Gimle.Asgard.Streams.ColeHopf.heatSeries_pde ((mkRat (1) 1) : ℚ) _) a unused v rel]
    exact (Gimle.Asgard.Streams.ColeHopf.certificate (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel)).hasSum hx
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] = Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1) = Gimle.Asgard.Streams.Burgers.circuit .ogf 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/6 ∧ |x| ≤ 1/8 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (7) 10) : ℚ) : ℝ) = (7/10) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (13) 10) : ℚ) : ℝ) = (13/10) := by norm_num [Rat.mkRat_eq_div]
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
### Refute the upper bound of one {fold}

At $(t,x)=(\tfrac16,-\tfrac18)$, the fast front exceeds $1$ by a
kernel-checked window estimate and its error bound. The positive claim is
refuted; its `sorry` is not a proof.
-/

end Decided_fast_band


-- @decide fast_crosses_one : stream burgers viscosity 1 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1]
--   field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u <= 1

namespace Decided_fast_crosses_one

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 6), (mkRat (1) 8)], by decide +kernel⟩

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (1) 2), (mkRat (1) 3)]

def forsetiTable : List (List ℚ) := [
    [(mkRat (1) 2), (mkRat (1) 4), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (1) 480), (mkRat (0) 1), (mkRat (-17) 80640), (mkRat (0) 1), (mkRat (31) 1451520), (mkRat (0) 1), (mkRat (-691) 319334400), (mkRat (0) 1), (mkRat (5461) 24908083200), (mkRat (0) 1), (mkRat (-929569) 41845579776000)],
    [(mkRat (-1) 4), (mkRat (0) 1), (mkRat (1) 16), (mkRat (0) 1), (mkRat (-1) 96), (mkRat (0) 1), (mkRat (17) 11520), (mkRat (0) 1), (mkRat (-31) 161280), (mkRat (0) 1), (mkRat (691) 29030400), (mkRat (0) 1), (mkRat (-5461) 1916006400), (mkRat (0) 1), (mkRat (929569) 2789705318400), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-1) 16), (mkRat (0) 1), (mkRat (1) 48), (mkRat (0) 1), (mkRat (-17) 3840), (mkRat (0) 1), (mkRat (31) 40320), (mkRat (0) 1), (mkRat (-691) 5806080), (mkRat (0) 1), (mkRat (5461) 319334400), (mkRat (0) 1), (mkRat (-929569) 398529331200), (mkRat (0) 1), (mkRat (3202291) 10461394944000)],
    [(mkRat (1) 48), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (17) 2304), (mkRat (0) 1), (mkRat (-31) 17280), (mkRat (0) 1), (mkRat (691) 1935360), (mkRat (0) 1), (mkRat (-5461) 87091200), (mkRat (0) 1), (mkRat (929569) 91968307200), (mkRat (0) 1), (mkRat (-3202291) 2092278988800), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (1) 96), (mkRat (0) 1), (mkRat (-17) 2304), (mkRat (0) 1), (mkRat (31) 11520), (mkRat (0) 1), (mkRat (-691) 967680), (mkRat (0) 1), (mkRat (5461) 34836480), (mkRat (0) 1), (mkRat (-929569) 30656102400), (mkRat (0) 1), (mkRat (3202291) 597793996800), (mkRat (0) 1), (mkRat (-221930581) 251073478656000)],
    [(mkRat (-1) 480), (mkRat (0) 1), (mkRat (17) 3840), (mkRat (0) 1), (mkRat (-31) 11520), (mkRat (0) 1), (mkRat (691) 691200), (mkRat (0) 1), (mkRat (-5461) 19353600), (mkRat (0) 1), (mkRat (929569) 13934592000), (mkRat (0) 1), (mkRat (-3202291) 229920768000), (mkRat (0) 1), (mkRat (221930581) 83691159552000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-17) 11520), (mkRat (0) 1), (mkRat (31) 17280), (mkRat (0) 1), (mkRat (-691) 691200), (mkRat (0) 1), (mkRat (5461) 14515200), (mkRat (0) 1), (mkRat (-929569) 8360755200), (mkRat (0) 1), (mkRat (3202291) 114960384000), (mkRat (0) 1), (mkRat (-221930581) 35867639808000), (mkRat (0) 1), (mkRat (4722116521) 3766102179840000)],
    [(mkRat (17) 80640), (mkRat (0) 1), (mkRat (-31) 40320), (mkRat (0) 1), (mkRat (691) 967680), (mkRat (0) 1), (mkRat (-5461) 14515200), (mkRat (0) 1), (mkRat (929569) 6502809600), (mkRat (0) 1), (mkRat (-3202291) 73156608000), (mkRat (0) 1), (mkRat (221930581) 19313344512000), (mkRat (0) 1), (mkRat (-4722116521) 1757514350592000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (31) 161280), (mkRat (0) 1), (mkRat (-691) 1935360), (mkRat (0) 1), (mkRat (5461) 19353600), (mkRat (0) 1), (mkRat (-929569) 6502809600), (mkRat (0) 1), (mkRat (3202291) 58525286400), (mkRat (0) 1), (mkRat (-221930581) 12875563008000), (mkRat (0) 1), (mkRat (4722116521) 1004293914624000), (mkRat (0) 1), (mkRat (-968383680827) 843606888284160000)],
    [(mkRat (-31) 1451520), (mkRat (0) 1), (mkRat (691) 5806080), (mkRat (0) 1), (mkRat (-5461) 34836480), (mkRat (0) 1), (mkRat (929569) 8360755200), (mkRat (0) 1), (mkRat (-3202291) 58525286400), (mkRat (0) 1), (mkRat (221930581) 10534551552000), (mkRat (0) 1), (mkRat (-4722116521) 695280402432000), (mkRat (0) 1), (mkRat (968383680827) 506164132970496000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-691) 29030400), (mkRat (0) 1), (mkRat (5461) 87091200), (mkRat (0) 1), (mkRat (-929569) 13934592000), (mkRat (0) 1), (mkRat (3202291) 73156608000), (mkRat (0) 1), (mkRat (-221930581) 10534551552000), (mkRat (0) 1), (mkRat (4722116521) 579400335360000), (mkRat (0) 1), (mkRat (-968383680827) 361545809264640000), (mkRat (0) 1), (mkRat (14717667114151) 18981154986393600000)],
    [(mkRat (691) 319334400), (mkRat (0) 1), (mkRat (-5461) 319334400), (mkRat (0) 1), (mkRat (929569) 30656102400), (mkRat (0) 1), (mkRat (-3202291) 114960384000), (mkRat (0) 1), (mkRat (221930581) 12875563008000), (mkRat (0) 1), (mkRat (-4722116521) 579400335360000), (mkRat (0) 1), (mkRat (968383680827) 305923377070080000), (mkRat (0) 1), (mkRat (-14717667114151) 13919513656688640000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (5461) 1916006400), (mkRat (0) 1), (mkRat (-929569) 91968307200), (mkRat (0) 1), (mkRat (3202291) 229920768000), (mkRat (0) 1), (mkRat (-221930581) 19313344512000), (mkRat (0) 1), (mkRat (4722116521) 695280402432000), (mkRat (0) 1), (mkRat (-968383680827) 305923377070080000), (mkRat (0) 1), (mkRat (14717667114151) 11931011705733120000), (mkRat (0) 1), (mkRat (-2093660879252671) 5011024916407910400000)],
    [(mkRat (-5461) 24908083200), (mkRat (0) 1), (mkRat (929569) 398529331200), (mkRat (0) 1), (mkRat (-3202291) 597793996800), (mkRat (0) 1), (mkRat (221930581) 35867639808000), (mkRat (0) 1), (mkRat (-4722116521) 1004293914624000), (mkRat (0) 1), (mkRat (968383680827) 361545809264640000), (mkRat (0) 1), (mkRat (-14717667114151) 11931011705733120000), (mkRat (0) 1), (mkRat (2093660879252671) 4342888260886855680000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-929569) 2789705318400), (mkRat (0) 1), (mkRat (3202291) 2092278988800), (mkRat (0) 1), (mkRat (-221930581) 83691159552000), (mkRat (0) 1), (mkRat (4722116521) 1757514350592000), (mkRat (0) 1), (mkRat (-968383680827) 506164132970496000), (mkRat (0) 1), (mkRat (14717667114151) 13919513656688640000), (mkRat (0) 1), (mkRat (-2093660879252671) 4342888260886855680000), (mkRat (0) 1), (mkRat (86125672563201181) 456003267393119846400000)],
    [(mkRat (929569) 41845579776000), (mkRat (0) 1), (mkRat (-3202291) 10461394944000), (mkRat (0) 1), (mkRat (221930581) 251073478656000), (mkRat (0) 1), (mkRat (-4722116521) 3766102179840000), (mkRat (0) 1), (mkRat (968383680827) 843606888284160000), (mkRat (0) 1), (mkRat (-14717667114151) 18981154986393600000), (mkRat (0) 1), (mkRat (2093660879252671) 5011024916407910400000), (mkRat (0) 1), (mkRat (-86125672563201181) 456003267393119846400000), (mkRat (0) 1)]]

def forsetiQ (k : Gimle.Asgard.Streams.Lowering.Degrees 2) : ℚ := (forsetiTable.getD (k 0) []).getD (k 1) 0

def forsetiPoint : Fin 2 → ℚ := ![(mkRat (1) 6), (mkRat (-1) 8)]

def forsetiRoot : Prop :=
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a] →
    ∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
        (Gimle.Asgard.Streams.analyticField .ogf a x) ∧
      Gimle.Asgard.Streams.analyticField .ogf a x ≤ (((mkRat (1) 1) : ℚ) : ℝ)

/-- u is the stream the Burgers circuit at viscosity 1 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges at every point of the box, and its sum, the analytic field, stays within the band there. The stream decider refuted it. Goal (stream): stream burgers viscosity 1 interpretation analytic-field basis ogf potential exponentials [1, 0], [1, -1] field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u <= 1 -/
theorem fast_crosses_one :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf 1
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/6 ∧ |x| ≤ 1/8 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 1 := by
  sorry

theorem fast_crosses_one_refuted : ¬ (have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf 1
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/6 ∧ |x| ≤ 1/8 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 1) := by
  have refuted : ¬ forsetiRoot := by
    unfold forsetiRoot
    intro h
    exact Gimle.Asgard.Streams.ColeHopf.front_above_of_window (hi := ((mkRat (1) 1) : ℚ)) (ε := (mkRat (2134495165562497) 15407021574586368)) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) (by decide +kernel) (Q := forsetiQ) (by decide +kernel) forsetiPoint (by decide +kernel) (by decide +kernel) fun a unused v rel x hx => (h a unused v rel x hx).2
  intro claim
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] = Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1) = Gimle.Asgard.Streams.Burgers.circuit .ogf 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/6 ∧ |x| ≤ 1/8 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
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

/-!
### Keep the narrower band unresolved on the larger box {fold}

The request $\tfrac45\le u\le\tfrac65$ on
$|t|\le\tfrac16$, $|x|\le\tfrac18$ remains unknown. The certificate is too
coarse to prove it, and the tested points do not refute it.

The classical formula suggests a range about $[0.86,1.14]$, a numerical
estimate rather than a checked theorem here. The certificate's interval is
about $[0.71,1.29]$, with error about $0.139$; that interval alone cannot
settle the request. No claim card is generated for this unresolved directive.
-/

end Decided_fast_crosses_one


-- @decide fast_band_large_box : stream burgers viscosity 1 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1]
--   field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u >= 4/5 and u <= 6/5

/-!
### Certify that narrower band on the smaller box {fold}

On $|t|\le\tfrac{1}{12}$, $|x|\le\tfrac{1}{16}$, the field does satisfy
$\tfrac45\le u\le\tfrac65$. Shrinking the box makes the certificate sufficient.

On the small box the same window has the bound $[0.927, 1.073]$ and the error
$4 \cdot 10^{-7}$: the band that was out of reach above is checked here.
-/

-- @decide fast_true_band_small_box : stream burgers viscosity 1 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1]
--   field u over t in [-1/12, 1/12], x in [-1/16, 1/16] : u >= 4/5 and u <= 6/5

namespace Decided_fast_true_band_small_box

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 12), (mkRat (1) 16)], by decide +kernel⟩

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (1) 2), (mkRat (1) 3)]

def forsetiTable : List (List ℚ) := [
    [(mkRat (1) 2), (mkRat (1) 4), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (1) 480), (mkRat (0) 1), (mkRat (-17) 80640), (mkRat (0) 1), (mkRat (31) 1451520), (mkRat (0) 1), (mkRat (-691) 319334400), (mkRat (0) 1), (mkRat (5461) 24908083200), (mkRat (0) 1), (mkRat (-929569) 41845579776000)],
    [(mkRat (-1) 4), (mkRat (0) 1), (mkRat (1) 16), (mkRat (0) 1), (mkRat (-1) 96), (mkRat (0) 1), (mkRat (17) 11520), (mkRat (0) 1), (mkRat (-31) 161280), (mkRat (0) 1), (mkRat (691) 29030400), (mkRat (0) 1), (mkRat (-5461) 1916006400), (mkRat (0) 1), (mkRat (929569) 2789705318400), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-1) 16), (mkRat (0) 1), (mkRat (1) 48), (mkRat (0) 1), (mkRat (-17) 3840), (mkRat (0) 1), (mkRat (31) 40320), (mkRat (0) 1), (mkRat (-691) 5806080), (mkRat (0) 1), (mkRat (5461) 319334400), (mkRat (0) 1), (mkRat (-929569) 398529331200), (mkRat (0) 1), (mkRat (3202291) 10461394944000)],
    [(mkRat (1) 48), (mkRat (0) 1), (mkRat (-1) 48), (mkRat (0) 1), (mkRat (17) 2304), (mkRat (0) 1), (mkRat (-31) 17280), (mkRat (0) 1), (mkRat (691) 1935360), (mkRat (0) 1), (mkRat (-5461) 87091200), (mkRat (0) 1), (mkRat (929569) 91968307200), (mkRat (0) 1), (mkRat (-3202291) 2092278988800), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (1) 96), (mkRat (0) 1), (mkRat (-17) 2304), (mkRat (0) 1), (mkRat (31) 11520), (mkRat (0) 1), (mkRat (-691) 967680), (mkRat (0) 1), (mkRat (5461) 34836480), (mkRat (0) 1), (mkRat (-929569) 30656102400), (mkRat (0) 1), (mkRat (3202291) 597793996800), (mkRat (0) 1), (mkRat (-221930581) 251073478656000)],
    [(mkRat (-1) 480), (mkRat (0) 1), (mkRat (17) 3840), (mkRat (0) 1), (mkRat (-31) 11520), (mkRat (0) 1), (mkRat (691) 691200), (mkRat (0) 1), (mkRat (-5461) 19353600), (mkRat (0) 1), (mkRat (929569) 13934592000), (mkRat (0) 1), (mkRat (-3202291) 229920768000), (mkRat (0) 1), (mkRat (221930581) 83691159552000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-17) 11520), (mkRat (0) 1), (mkRat (31) 17280), (mkRat (0) 1), (mkRat (-691) 691200), (mkRat (0) 1), (mkRat (5461) 14515200), (mkRat (0) 1), (mkRat (-929569) 8360755200), (mkRat (0) 1), (mkRat (3202291) 114960384000), (mkRat (0) 1), (mkRat (-221930581) 35867639808000), (mkRat (0) 1), (mkRat (4722116521) 3766102179840000)],
    [(mkRat (17) 80640), (mkRat (0) 1), (mkRat (-31) 40320), (mkRat (0) 1), (mkRat (691) 967680), (mkRat (0) 1), (mkRat (-5461) 14515200), (mkRat (0) 1), (mkRat (929569) 6502809600), (mkRat (0) 1), (mkRat (-3202291) 73156608000), (mkRat (0) 1), (mkRat (221930581) 19313344512000), (mkRat (0) 1), (mkRat (-4722116521) 1757514350592000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (31) 161280), (mkRat (0) 1), (mkRat (-691) 1935360), (mkRat (0) 1), (mkRat (5461) 19353600), (mkRat (0) 1), (mkRat (-929569) 6502809600), (mkRat (0) 1), (mkRat (3202291) 58525286400), (mkRat (0) 1), (mkRat (-221930581) 12875563008000), (mkRat (0) 1), (mkRat (4722116521) 1004293914624000), (mkRat (0) 1), (mkRat (-968383680827) 843606888284160000)],
    [(mkRat (-31) 1451520), (mkRat (0) 1), (mkRat (691) 5806080), (mkRat (0) 1), (mkRat (-5461) 34836480), (mkRat (0) 1), (mkRat (929569) 8360755200), (mkRat (0) 1), (mkRat (-3202291) 58525286400), (mkRat (0) 1), (mkRat (221930581) 10534551552000), (mkRat (0) 1), (mkRat (-4722116521) 695280402432000), (mkRat (0) 1), (mkRat (968383680827) 506164132970496000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-691) 29030400), (mkRat (0) 1), (mkRat (5461) 87091200), (mkRat (0) 1), (mkRat (-929569) 13934592000), (mkRat (0) 1), (mkRat (3202291) 73156608000), (mkRat (0) 1), (mkRat (-221930581) 10534551552000), (mkRat (0) 1), (mkRat (4722116521) 579400335360000), (mkRat (0) 1), (mkRat (-968383680827) 361545809264640000), (mkRat (0) 1), (mkRat (14717667114151) 18981154986393600000)],
    [(mkRat (691) 319334400), (mkRat (0) 1), (mkRat (-5461) 319334400), (mkRat (0) 1), (mkRat (929569) 30656102400), (mkRat (0) 1), (mkRat (-3202291) 114960384000), (mkRat (0) 1), (mkRat (221930581) 12875563008000), (mkRat (0) 1), (mkRat (-4722116521) 579400335360000), (mkRat (0) 1), (mkRat (968383680827) 305923377070080000), (mkRat (0) 1), (mkRat (-14717667114151) 13919513656688640000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (5461) 1916006400), (mkRat (0) 1), (mkRat (-929569) 91968307200), (mkRat (0) 1), (mkRat (3202291) 229920768000), (mkRat (0) 1), (mkRat (-221930581) 19313344512000), (mkRat (0) 1), (mkRat (4722116521) 695280402432000), (mkRat (0) 1), (mkRat (-968383680827) 305923377070080000), (mkRat (0) 1), (mkRat (14717667114151) 11931011705733120000), (mkRat (0) 1), (mkRat (-2093660879252671) 5011024916407910400000)],
    [(mkRat (-5461) 24908083200), (mkRat (0) 1), (mkRat (929569) 398529331200), (mkRat (0) 1), (mkRat (-3202291) 597793996800), (mkRat (0) 1), (mkRat (221930581) 35867639808000), (mkRat (0) 1), (mkRat (-4722116521) 1004293914624000), (mkRat (0) 1), (mkRat (968383680827) 361545809264640000), (mkRat (0) 1), (mkRat (-14717667114151) 11931011705733120000), (mkRat (0) 1), (mkRat (2093660879252671) 4342888260886855680000), (mkRat (0) 1)],
    [(mkRat (0) 1), (mkRat (-929569) 2789705318400), (mkRat (0) 1), (mkRat (3202291) 2092278988800), (mkRat (0) 1), (mkRat (-221930581) 83691159552000), (mkRat (0) 1), (mkRat (4722116521) 1757514350592000), (mkRat (0) 1), (mkRat (-968383680827) 506164132970496000), (mkRat (0) 1), (mkRat (14717667114151) 13919513656688640000), (mkRat (0) 1), (mkRat (-2093660879252671) 4342888260886855680000), (mkRat (0) 1), (mkRat (86125672563201181) 456003267393119846400000)],
    [(mkRat (929569) 41845579776000), (mkRat (0) 1), (mkRat (-3202291) 10461394944000), (mkRat (0) 1), (mkRat (221930581) 251073478656000), (mkRat (0) 1), (mkRat (-4722116521) 3766102179840000), (mkRat (0) 1), (mkRat (968383680827) 843606888284160000), (mkRat (0) 1), (mkRat (-14717667114151) 18981154986393600000), (mkRat (0) 1), (mkRat (2093660879252671) 5011024916407910400000), (mkRat (0) 1), (mkRat (-86125672563201181) 456003267393119846400000), (mkRat (0) 1)]]

def forsetiQ (k : Gimle.Asgard.Streams.Lowering.Degrees 2) : ℚ := (forsetiTable.getD (k 0) []).getD (k 1) 0

def forsetiRoot : Prop :=
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]), unused] ![v, a] →
    ∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
        (Gimle.Asgard.Streams.analyticField .ogf a x) ∧
      (((mkRat (4) 5) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.analyticField .ogf a x ∧ Gimle.Asgard.Streams.analyticField .ogf a x ≤ (((mkRat (6) 5) : ℚ) : ℝ)

/-- u is the stream the Burgers circuit at viscosity 1 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges at every point of the box, and its sum, the analytic field, stays within the band there. The stream decider proved it. Goal (stream): stream burgers viscosity 1 interpretation analytic-field basis ogf potential exponentials [1, 0], [1, -1] field u over t in [-1/12, 1/12], x in [-1/16, 1/16] : u >= 4/5 and u <= 6/5 -/
theorem fast_true_band_small_box :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf 1
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/12 ∧ |x| ≤ 1/16 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        4/5 ≤ Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 6/5 := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    intro a unused v rel x hx
    refine ⟨?_, (Gimle.Asgard.Streams.ColeHopf.front_band_of_window (lo := ((mkRat (4) 5) : ℚ)) (hi := ((mkRat (6) 5) : ℚ)) (ε := (mkRat (2134495165562497) 5048572829560461066240)) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) (by decide +kernel) (Q := forsetiQ) (by decide +kernel) (by decide +kernel) (by decide +kernel) a unused v rel x hx)⟩
    have hc : MvPowerSeries.constantCoeff (Gimle.Asgard.Streams.ColeHopf.expSumHeat ((mkRat (1) 1) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))]) ≠ 0 := by
      rw [Gimle.Asgard.Streams.ColeHopf.constantCoeff_expSumHeat]
      decide +kernel
    simp only [Gimle.Asgard.Streams.ColeHopf.front] at rel
    rw [Gimle.Asgard.Streams.ColeHopf.candidate_quotient ((mkRat (1) 1) : ℚ) _ hc (Gimle.Asgard.Streams.ColeHopf.heatSeries_pde ((mkRat (1) 1) : ℚ) _) a unused v rel]
    exact (Gimle.Asgard.Streams.ColeHopf.certificate (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 1) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel)).hasSum hx
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 1) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1))] = Gimle.Asgard.Streams.ColeHopf.front 1 [(1, 0), (1, -1)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 1) = Gimle.Asgard.Streams.Burgers.circuit .ogf 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/12 ∧ |x| ≤ 1/16 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (4) 5) : ℚ) : ℝ) = (4/5) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (6) 5) : ℚ) : ℝ) = (6/5) := by norm_num [Rat.mkRat_eq_div]
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

end Decided_fast_true_band_small_box


/-!
## Inspect the two-exponential front {fold}

At $\nu=\tfrac12$, the potential $1+e^{-x}+e^{-2x}$ yields a certified
$[\tfrac12,\tfrac32]$ band on $|t|,|x|\le\tfrac{1}{16}$. The same band on
$|t|\le\tfrac16$, $|x|\le\tfrac18$ remains unknown: the search finds no radii.

**Two exponentials.** The potential $1 + e^{-x} + e^{-2x}$ at $\nu = \tfrac12$,
whose front is a sum of two steps and starts at $u(0, 0) = 1$. The second
exponential doubles the decay rate the majorant must absorb, which halves the
radius $\rho$ the profile fits and shrinks the box the certificate can hold.

### Certify the band on the smaller box {fold}

The coefficient window and its certified error establish
$\tfrac12\le u\le\tfrac32$ on $|t|,|x|\le\tfrac{1}{16}$.

With $a = -2$ in the potential, the profile fits only $\rho \le \tfrac12$, the
heat radii are $(\tfrac12, \tfrac12)$, and the inverse is majorized at radii
inside them only for a box of about $\tfrac{1}{16}$ a side. There the certified
error is $0.32$ and the window's bound $[0.59, 1.41]$: the wide band is
checked. On the large box the majorant finds no radii, and the directive
stays undecided with that reason.
-/

-- @decide two_exponentials_band : stream burgers viscosity 1/2 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1], [1, -2]
--   field u over t in [-1/16, 1/16], x in [-1/16, 1/16] : u >= 1/2 and u <= 3/2

namespace Decided_two_exponentials_band

def forsetiBox : Gimle.Asgard.Streams.Box 2 :=
  ⟨![(mkRat (1) 16), (mkRat (1) 16)], by decide +kernel⟩

def forsetiRadii : Fin 2 → ℚ := ![(mkRat (1) 6), (mkRat (1) 6)]

def forsetiTable : List (List ℚ) := [
    [(mkRat (1) 3), (mkRat (1) 3), (mkRat (1) 18), (mkRat (-1) 18), (mkRat (-1) 72), (mkRat (13) 1080), (mkRat (7) 2160), (mkRat (-41) 15120), (mkRat (-809) 1088640), (mkRat (671) 1088640), (mkRat (1847) 10886400), (mkRat (-50443) 359251200), (mkRat (-7943) 205286400), (mkRat (597871) 18681062400), (mkRat (6921461) 784604620800), (mkRat (-28621321) 3923023104000)],
    [(mkRat (-5) 18), (mkRat (-1) 18), (mkRat (17) 108), (mkRat (1) 36), (mkRat (-79) 1296), (mkRat (-7) 720), (mkRat (259) 12960), (mkRat (809) 272160), (mkRat (-39037) 6531840), (mkRat (-1847) 2177280), (mkRat (330937) 195955200), (mkRat (7943) 34214400), (mkRat (-566099) 1231718400), (mkRat (-6921461) 112086374400), (mkRat (573361897) 4707627724800), (mkRat (126235201) 7846046208000)],
    [(mkRat (-1) 216), (mkRat (-11) 72), (mkRat (-1) 432), (mkRat (53) 432), (mkRat (7) 5184), (mkRat (-59) 960), (mkRat (-163) 466560), (mkRat (26959) 1088640), (mkRat (1061) 26127360), (mkRat (-230051) 26127360), (mkRat (1337) 111974400), (mkRat (27949) 9676800), (mkRat (-1081433) 103464345600), (mkRat (-401633971) 448345497600), (mkRat (90621439) 18830510899200), (mkRat (75319134959) 282457663488000)],
    [(mkRat (65) 1296), (mkRat (-31) 1296), (mkRat (-949) 7776), (mkRat (217) 7776), (mkRat (3185) 31104), (mkRat (-8893) 466560), (mkRat (-161989) 2799360), (mkRat (194171) 19595520), (mkRat (2489045) 94058496), (mkRat (-292633) 67184640), (mkRat (-7126049) 671846400), (mkRat (88464697) 51732172800), (mkRat (482460893) 124157214720), (mkRat (-4997574431) 8070218956800), (mkRat (-104333480939) 78219045273600), (mkRat (153333509773) 726319706112000)],
    [(mkRat (389) 31104), (mkRat (1861) 31104), (mkRat (-8057) 186624), (mkRat (-6209) 62208), (mkRat (108511) 2239488), (mkRat (104647) 1244160), (mkRat (-2340937) 67184640), (mkRat (-23984761) 470292480), (mkRat (31454699) 1612431360), (mkRat (13663601) 537477120), (mkRat (-1048823539) 112870195200), (mkRat (-511599961) 45984153600), (mkRat (58906784917) 14898865766400), (mkRat (2578485580703) 581055764889600), (mkRat (-5396628871213) 3486334589337600), (mkRat (-9594041874101) 5810557648896000)],
    [(mkRat (-2155) 186624), (mkRat (2737) 103680), (mkRat (105953) 1866240), (mkRat (-109493) 1866240), (mkRat (-1760231) 22394880), (mkRat (2345731) 37324800), (mkRat (132777779) 2015539200), (mkRat (-10449299) 223948800), (mkRat (-4711968293) 112870195200), (mkRat (1040620817) 37623398400), (mkRat (24955365611) 1128701952000), (mkRat (-58228511431) 4138573824000), (mkRat (-13854001305493) 1340897918976000), (mkRat (590839526551) 92231073792000), (mkRat (97659962797529) 22185765568512000), (mkRat (-363586522111031) 135579678474240000)],
    [(mkRat (-67249) 11197440), (mkRat (-194257) 11197440), (mkRat (2655413) 67184640), (mkRat (3143671) 67184640), (mkRat (-18805697) 268738560), (mkRat (-231666691) 4031078400), (mkRat (1747818373) 24186470400), (mkRat (1150123459) 24186470400), (mkRat (-74194079731) 1354442342400), (mkRat (-41846539579) 1354442342400), (mkRat (459140403437) 13544423424000), (mkRat (22845467011013) 1340897918976000), (mkRat (-41759547742853) 2298682146816000), (mkRat (-249314910121733) 29882867908608000), (mkRat (25605825354387493) 2928521055043584000), (mkRat (18222778309534157) 4880868425072640000)],
    [(mkRat (204319) 94058496), (mkRat (-6731477) 470292480), (mkRat (-47339063) 2821754880), (mkRat (15715531) 313528320), (mkRat (222798797) 6772211712), (mkRat (-206861137) 2687385600), (mkRat (-5311512449) 145118822400), (mkRat (183064443859) 2370274099200), (mkRat (66986517209) 2275463135232), (mkRat (-375239602351) 6320730931200), (mkRat (-98059737739223) 5119792054272000), (mkRat (33938806530359) 893931945984000), (mkRat (207121757113259) 19308930033254400), (mkRat (-62122655800657477) 2928521055043584000), (mkRat (-220281320463897101) 40999294770610176000), (mkRat (18725483104138669) 1752106614128640000)],
    [(mkRat (49370023) 22574039040), (mkRat (23625229) 7524679680), (mkRat (-340769771) 15049359360), (mkRat (-507212123) 45148078080), (mkRat (1478260859) 25798901760), (mkRat (15361505149) 902961561600), (mkRat (-1295650420433) 16253308108800), (mkRat (-624008973163) 37924385587200), (mkRat (23701151184173) 303395084697600), (mkRat (32738023743469) 2730555762278400), (mkRat (-236408132852893) 3900793946112000), (mkRat (-2152916539335803) 300361133850624000), (mkRat (429842146364522999) 10813000818622464000), (mkRat (5247024878092733) 1419888996384768000), (mkRat (-1674267140186665699) 72887635147751424000), (mkRat (-5559553451179390681) 3279943581648814080000)],
    [(mkRat (-5500417) 27088846848), (mkRat (799358059) 135444234240), (mkRat (1296945577) 812665405440), (mkRat (-3417421051) 116095057920), (mkRat (-120910411) 51597803520), (mkRat (2958193985617) 48759924326400), (mkRat (5659311131) 10835538739200), (mkRat (-53522101136557) 682638940569600), (mkRat (119114770539763) 49150003721011200), (mkRat (528631445772317) 7021429103001600), (mkRat (-100495064075081) 23404763676672000), (mkRat (-952687832916580471) 16219501227933696000), (mkRat (289577464850388907) 64878004911734784000), (mkRat (334651624925838601) 8519333978308608000), (mkRat (-42009279725078015981) 11807796893935730688000), (mkRat (-28098087241300700831) 1204877234075074560000)],
    [(mkRat (-5521185401) 8126654054400), (mkRat (1631604647) 8126654054400), (mkRat (69524113211) 6965703475200), (mkRat (-5729723981) 2321901158400), (mkRat (-19745601469339) 585119091916800), (mkRat (2736223336829) 325066162176000), (mkRat (352241626620239) 5851190919168000), (mkRat (-1901397622681603) 122875009302528000), (mkRat (-30913605337360471) 421285746180096000), (mkRat (390750836038141) 20061226008576000), (mkRat (6118569297849271357) 88470006697820160000), (mkRat (-2045720222422980667) 108130008186224640000), (mkRat (-70176382889478881251) 1297560098234695680000), (mkRat (256449860732282794589) 16868281277051043840000), (mkRat (3713276666716143528857) 101209687662306263040000), (mkRat (-1782581697050336844127) 168682812770510438400000)],
    [(mkRat (-8008258217) 107271833518080), (mkRat (-51470619593) 25540912742400), (mkRat (1896825400091) 1072718335180800), (mkRat (14329658648297) 1072718335180800), (mkRat (-21755185952089) 2574524004433920), (mkRat (-83682221616439) 2383818522624000), (mkRat (22899554267143553) 1158535801995264000), (mkRat (21669322142450173) 386178600665088000), (mkRat (-15613619557101395) 519024039293878272), (mkRat (-4223539199340742751) 64878004911734784000), (mkRat (66564104068457175611) 1946340147352043520000), (mkRat (47757713693803671553) 792953393365647360000), (mkRat (-538536352945951416467) 17127793296697982976000), (mkRat (-356278562971156699733) 7573514042757611520000), (mkRat (383195862702130303378457) 15586291899995164508160000), (mkRat (22590428568986400280415051) 701383135499782402867200000)],
    [(mkRat (338092725347) 1838945717452800), (mkRat (-84895787447) 167176883404800), (mkRat (-275388600241417) 77235720133017600), (mkRat (354601316679373) 77235720133017600), (mkRat (4713855682482437) 308942880532070400), (mkRat (-71891090842088017) 4634143207981056000), (mkRat (-132697210271365471) 3972122749698048000), (mkRat (121620977354142311) 3972122749698048000), (mkRat (228022896591570109693) 4671216353644904448000), (mkRat (-198899146361907791659) 4671216353644904448000), (mkRat (-2528580265185225666659) 46712163536449044480000), (mkRat (718728734231583452941) 15570721178816348160000), (mkRat (14403604113572605316177) 293619313657679708160000), (mkRat (-158393189379459788752399) 3817051077549836206080000), (mkRat (-29588024735401124474386967) 776916703938220507791360000), (mkRat (1627570164679007756483137879) 50499585755984333006438400000)],
    [(mkRat (11662766762917) 200812872345845760), (mkRat (577388306538313) 1004064361729228800), (mkRat (-9198986649306221) 6024386170375372800), (mkRat (-9589113369549893) 2008128723458457600), (mkRat (607195761637150267) 72292634044504473600), (mkRat (87377313837234613) 5737510638452736000), (mkRat (-7056266541996574843) 309825574476447744000), (mkRat (-437717370750049215037) 15181453149345939456000), (mkRat (14606082005171235464801) 364354875584302546944000), (mkRat (429079958979017968201) 11041056835887955968000), (mkRat (-63649516708765532662309) 1214516251947675156480000), (mkRat (-95825551969580814721) 2330312013156188160000), (mkRat (1260379551304975984852709) 22902306465299017236480000), (mkRat (680193413113890586157580779) 18756988995079895116677120000), (mkRat (-38454013630558366206389632183) 787793537793355594900439040000), (mkRat (-36408948706106228528481202079) 1312989229655592658167398400000)],
    [(mkRat (-3566079404486147) 84341406385255219200), (mkRat (2754616292751221) 9371267376139468800), (mkRat (170688929235688133) 168682812770510438400), (mkRat (-535426741176382169) 168682812770510438400), (mkRat (-1492996569356786933) 289170536178017894400), (mkRat (42871563624736424623) 3373656255410208768000), (mkRat (2390309078904316774079) 182177437792151273472000), (mkRat (-1389263167233871909123) 47231187575742922752000), (mkRat (-222104903540532471843113) 10201936516360471314432000), (mkRat (53821511103745914962887) 1133548501817830146048000), (mkRat (14529624897137467560259) 539785000865633402880000), (mkRat (-7378456840336538921829041) 124690335199961316065280000), (mkRat (-3245210687058782647124997433) 121199005814362399215452160000), (mkRat (10612984696565534766907454543) 175065230620745687755653120000), (mkRat (496509644560980183110049211039) 22058219058213956657212293120000), (mkRat (-1957104283251206122245371032169) 36763698430356594428687155200000)],
    [(mkRat (-197071793465713) 7785360589408174080), (mkRat (-326310427039894117) 2530242191557656576000), (mkRat (941702021213083709) 1167804088411226112000), (mkRat (2686896956354371477) 2168779021335134208000), (mkRat (-64310725840899641) 12133029489986764800), (mkRat (-4019816473627806222751) 910887188960756367360000), (mkRat (92606518891900180385737) 5465323133764538204160000), (mkRat (345728641557728073206857) 38257261936351767429120000), (mkRat (-32707835260230461865587) 941717216894812736716800), (mkRat (-8861953765357516456079) 694009286827242946560000), (mkRat (692978497624232447169383) 13249268203065547161600000), (mkRat (4154267476262986560102417497) 302997514535905998038630400000), (mkRat (-45565463486901024045346934467) 727194034886174395292712960000), (mkRat (-559109398892749095864825351551) 47267612267601335694026342400000), (mkRat (290922828414002823463112298439) 4627598403821109788226355200000), (mkRat (3999603031417317977291355828997) 472676122676013356940263424000000)]]

def forsetiQ (k : Gimle.Asgard.Streams.Lowering.Degrees 2) : ℚ := (forsetiTable.getD (k 0) []).getD (k 1) 0

def forsetiRoot : Prop :=
  ∀ a unused v : Gimle.Asgard.Streams.Stream 2,
      (Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2)).Rel
        ![a, Gimle.Asgard.Streams.ColeHopf.zeroSlice (Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1)), ((mkRat (1) 1), (mkRat (-2) 1))]), unused] ![v, a] →
    ∀ x, forsetiBox.Mem x →
      HasSum (Gimle.Asgard.Streams.seriesTerm .ogf a x)
        (Gimle.Asgard.Streams.analyticField .ogf a x) ∧
      (((mkRat (1) 2) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.analyticField .ogf a x ∧ Gimle.Asgard.Streams.analyticField .ogf a x ≤ (((mkRat (3) 2) : ℚ) : ℝ)

/-- u is the stream the Burgers circuit at viscosity 1/2 rebuilds from the t = 0 slice of the Cole–Hopf front −2ν φ_x/φ of the potential Σ cᵢ·e^(aᵢx) given by the pairs (cᵢ, aᵢ), u_t its other output; its series converges at every point of the box, and its sum, the analytic field, stays within the band there. The stream decider proved it. Goal (stream): stream burgers viscosity 1/2 interpretation analytic-field basis ogf potential exponentials [1, 0], [1, -1], [1, -2] field u over t in [-1/16, 1/16], x in [-1/16, 1/16] : u >= 1/2 and u <= 3/2 -/
theorem two_exponentials_band :
    have circuit := Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2)
    have slice := Gimle.Asgard.Streams.ColeHopf.zeroSlice
      (Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1), (1, -2)])
    ∀ u unused u_t : Gimle.Asgard.Streams.Stream 2,
      circuit.Rel ![u, slice, unused] ![u_t, u] →
      ∀ t x : ℝ, |t| ≤ 1/16 ∧ |x| ≤ 1/16 →
        HasSum (Gimle.Asgard.Streams.seriesTerm .ogf u ![t, x])
          (Gimle.Asgard.Streams.analyticField .ogf u ![t, x]) ∧
        1/2 ≤ Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ∧
        Gimle.Asgard.Streams.analyticField .ogf u ![t, x] ≤ 3/2 := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    intro a unused v rel x hx
    refine ⟨?_, (Gimle.Asgard.Streams.ColeHopf.front_band_of_window (lo := ((mkRat (1) 2) : ℚ)) (hi := ((mkRat (3) 2) : ℚ)) (ε := (mkRat (43046721) 134217728)) (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1)), ((mkRat (1) 1), (mkRat (-2) 1))] (show Gimle.Asgard.Streams.ColeHopf.constantTerm [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1)), ((mkRat (1) 1), (mkRat (-2) 1))] ≠ 0 by decide +kernel) (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel) ![16, 16] (by decide +kernel) (by decide +kernel) (Q := forsetiQ) (by decide +kernel) (by decide +kernel) (by decide +kernel) a unused v rel x hx)⟩
    have hc : MvPowerSeries.constantCoeff (Gimle.Asgard.Streams.ColeHopf.expSumHeat ((mkRat (1) 2) : ℚ) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1)), ((mkRat (1) 1), (mkRat (-2) 1))]) ≠ 0 := by
      rw [Gimle.Asgard.Streams.ColeHopf.constantCoeff_expSumHeat]
      decide +kernel
    simp only [Gimle.Asgard.Streams.ColeHopf.front] at rel
    rw [Gimle.Asgard.Streams.ColeHopf.candidate_quotient ((mkRat (1) 2) : ℚ) _ hc (Gimle.Asgard.Streams.ColeHopf.heatSeries_pde ((mkRat (1) 2) : ℚ) _) a unused v rel]
    exact (Gimle.Asgard.Streams.ColeHopf.certificate (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) (show (0 : ℚ) < ((mkRat (1) 2) : ℚ) by decide +kernel) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1)), ((mkRat (1) 1), (mkRat (-2) 1))] (by decide +kernel) (r := forsetiRadii) (by decide +kernel) (by decide +kernel) (by decide +kernel) forsetiBox (by decide +kernel)).hasSum hx
  have forsetiFront : Gimle.Asgard.Streams.ColeHopf.front (mkRat (1) 2) [((mkRat (1) 1), (mkRat (0) 1)), ((mkRat (1) 1), (mkRat (-1) 1)), ((mkRat (1) 1), (mkRat (-2) 1))] = Gimle.Asgard.Streams.ColeHopf.front (1/2) [(1, 0), (1, -1), (1, -2)] := by norm_num [Rat.mkRat_eq_div]
  have forsetiCircuit : Gimle.Asgard.Streams.Burgers.circuit .ogf (mkRat (1) 2) = Gimle.Asgard.Streams.Burgers.circuit .ogf (1/2) := by norm_num [Rat.mkRat_eq_div]
  have forsetiInside : ∀ t x : ℝ, forsetiBox.Mem ![t, x] ↔ |t| ≤ 1/16 ∧ |x| ≤ 1/16 := by
    intro t x
    norm_num [Gimle.Asgard.Streams.Box.Mem, Fin.forall_fin_two, forsetiBox, Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 2) : ℚ) : ℝ) = (1/2) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (3) 2) : ℚ) : ℝ) = (3/2) := by norm_num [Rat.mkRat_eq_div]
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
### Leave the larger-box request unresolved {fold}

For $|t|\le\tfrac16$, $|x|\le\tfrac18$, the majorant search finds no
admissible radii below the heat radii $(\tfrac12,\tfrac12)$. The band
request remains unknown; this neither refutes the band nor proves divergence.
-/

end Decided_two_exponentials_band


-- @decide two_exponentials_large_box : stream burgers viscosity 1/2 interpretation analytic-field
--   basis ogf potential exponentials [1, 0], [1, -1], [1, -2]
--   field u over t in [-1/6, 1/6], x in [-1/8, 1/8] : u >= 1/2 and u <= 3/2

end Notebook.BurgersFronts

/-!
## Scope and unresolved requests

Every certified band includes convergence of the formal front's series on
its specified box. No result extends convergence outside those boxes or
identifies the prose's classical formulas with these analytic fields.

The requests `fast_band_large_box` and `two_exponentials_large_box` remain
unknown and have no claim cards. The separate request `fast_crosses_one` is
refuted at a checked point. Failure to find a certificate is not a refutation.
-/
