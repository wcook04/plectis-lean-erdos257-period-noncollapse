# Erdős #243: weighted-record octuple criteria (second return batch, 2026-09-05)

Status: proof note. Return batch `erdos243_20260905_weighted_record_octuple_returns_02`
(packet `erdos243_weighted_record_octuple_2026_09_05`, eight desks on the digest
`17e64d67…`). Lean authority for the finite cores is recorded per section below and
in `RecordIncrementBarrier.lean`, `SaturatedSquareTransport.lean`,
`TwoModulusRecordCut.lean` and `ProtectedEpochEnergy.lean`; the global statements are
ordinary proofs audited in this pass over the Lean core of
`ReciprocalTailRigidity.lean`, `DynamicCancellation.lean`,
`PrimitiveRecordBarrier.lean` and `CumulativeLcmTransfer.lean`. Exact finite replay:
`scripts/check_erdos243_weighted_record_octuple.py`. Nothing here settles Erdős #243;
every one of the eight returns says so, and the audit agrees.

The first batch of the day (`EightReturnRigidityCriteria.md`) is the baseline. Its
§0 dictionary is assumed; §11 of that note named the surviving regime as "cofinally
many clean primitive record jumps of size at least three". This batch attacks that
regime from eight coordinates. The verified additions are: two new exact equivalences
for the endpoint in primitive coordinates with arbitrary cancellation (record
increments at most one; bounded record-amplified error), a quantitative energy per
protected epoch that closes the `OPEN` r07 Theorem 8 target of
`PrimitiveRecordBarrier.lean`, a saturated square transport modulo the whole next
numerator, a two-modulus cut reaching jumps of size four with a `4/3` cancellation
alternative, a cumulative square cost for historical prime erasure, uniform
quadratic anti-shadowing with constant `1/4`, and the exclusion of rising-factorial
cubic profiles with a new irrationality criterion at the cubic rate. One return
(r05) rests on an external lemma this pass could not verify and is recorded as
`blocked_external`.

## 0. Additional dictionary

Beyond `EightReturnRigidityCriteria.md` §0 (primitive `u_n, v_n, e_n, h_n, w_n`,
`R_n = max_{k≤n} u_k`, `G_n`, `M_n`, `Λ_n`, `ρ_n`, `ℓ(x) = log₂ log₂ max(4, x)`):

- true record increment `s_n = R_{n+1} − R_n`; record-setting jump
  `u_{n+1} − u_n = s_n + (R_n − u_n)` (increment plus drawdown recovery);
- record-amplified negative error `m_n = (−e_n)_+`, `A_n = R_n m_n / u_n`;
- `d_n = u_{n+1} − u_n` at a strict rise; every late strict rise is clean
  (`h_n = 1`) under centring;
- protected epoch: `Q = p^ℓ ∣ v_s` with `p` odd, `L = pQ/2`, barriers
  `ℋ = {(2k+1)p : L/2 < (2k+1)p ≤ L}`, first crossing `τ` of `L`;
- energy `𝓔 = Σ_{n record} (1_{d_n≥3}/√u_n + (d_n − 2)_+/u_n)`;
- `K = limsup s_n/ℓ(R_n)`, `Γ = liminf ℓ(G_n)/ℓ(R_n)`;
- fresh source `j` (`ρ_j = 1`); a prime of `a_j` has *disappeared by* `N` if it fails
  to divide some `v_t`, `j < t ≤ N`; the source is *fully retired* by `N` if all its
  primes have disappeared (a historical property, not `gcd(a_j, v_N) = 1`);
- `κ_n = G_n/M_n = Λ_n/v_n`, so `U_n = κ_n u_n`, `V_n = κ_n e_n`.

## 1. Historical square payment and true record increments (r01)

**Lemma 1.1 (per-step square cost).** On one primitive step with full content,
for every prime `p`,
`ν_p(h) ≥ 2 (ν_p(v) − ν_p(v'))_+`.
*Proof.* `ν_p(v') = ν_p(a) + ν_p(v) − ν_p(h)`, so a drop of size `δ` means
`ν_p(h) = ν_p(a) + δ`. Since `h ∣ gcd(w, av) = gcd(w, a²) ∣ a²`
(`rawNext_gcd_eq_gcd_sq`), `ν_p(h) ≤ 2ν_p(a)`, hence `ν_p(a) ≥ δ` and
`ν_p(h) ≥ 2δ`. ∎ Equivalently, in the normal form `h = bc²`, `v' = (a/d)(v/c)`,
the drop is at most `ν_p(c)` and `ν_p(h) ≥ 2ν_p(c)`.

**Lemma 1.2 (historical square payment; r01 Lemma 1, r06 Corollary 2).** If
`p^b ∣ v_T` and `p ∤ v_s` for some `s > T`, then `p^{2b} ∣ ∏_{T≤n<s} h_n = G_s/G_T`,
and the divisibility persists in `G_N` for every `N ≥ s` even if `p` later re-enters
the reduced denominator. For a fresh source `j` with `p^e ∥ a_j`, freshness puts
`p^e ∥ v_{j+1}` exactly (`EightReturnRigidityCriteria.md` Lemma 22), so a source
fully retired by `N` costs `a_j² ∣ G_N`, and distinct fresh sources have disjoint
prime support, so
`(∏_{j ∈ J} a_j)² ∣ G_N` for every finite set `J` of fully retired fresh sources. ∎
Lean: `valuation_drop_le_half_cancellation`, `cumulative_erasure_square`
(`RecordIncrementBarrier.lean`).

**Theorem 1.3 (finite record–retirement dichotomy; r01 Theorem 2).** Let
`j_1 < ⋯ < j_m < T < N` be fresh with `a_{j_i} > 1`, `Q = ∏ a_{j_i}`, `J_ret` the
subset fully retired by `N`, `k = m − |J_ret|`. If `R_N ≥ R_T + Q` then
`(∏_{J_ret} a_j)² ∣ G_N` and there is `n ∈ [T, N)` with `R_n < R_T + Q` and
`s_n ≥ k + 1`. *Proof.* From each non-retired source select a prime `p_i` that never
disappeared; then `p_i ∣ v_t` for `T ≤ t ≤ N`. CRT gives `x ∈ (R_T, R_T + P]`,
`P = ∏ p_i ≤ Q`, with `x + i ≡ 0 (mod p_i)`; primitivity forbids
`u_t ∈ {x, …, x+k−1}` on `[T, N]`. At the first crossing `t` of `x` after `T`,
`R_{t−1} ≤ x − 1` and `u_t ≥ x + k`, so `s_{t−1} = u_t − R_{t−1} ≥ k + 1`. ∎
Consequently, if `s_n ≤ b` on `[T, N)` then at least `m − b + 1` of the sources are
fully retired and `G_N ≥ (a_{j_1} ⋯ a_{j_{m−b+1}})²`.

**Theorem 1.4 (record increments versus cancellation; r01 Theorem 3).** On a
non-Sylvester orbit, `K + Γ ≥ 1`. In particular `s_n = o(ℓ(R_n))` forces
`G_n ≥ 2^{(log₂ R_n)^{1−η}}` eventually for every `η > 0`. *Audit.* Assume
`K + Γ < 1`, pick `κ > K`, `γ > Γ`, `γ < α < β < 1` with `β − α > κ`. Along horizons
`N` with `ℓ(G_N) ≤ γL`, `L = ℓ(R_N)`: the fresh indices in `[αL, βL)` number
`(β−α)L − o(L)` (the nonfresh count below `T = βL` is `≤ log₂ C_T = o(T)`); each has
`2 log₂ a_j ≥ c 2^{αL} > 2^{γL} ≥ log₂ G_N`, so none is fully retired (Lemma 1.2);
`Q ≤ D_T = exp(O(2^{βL})) = R_N^{o(1)}` and `R_T = exp(o(T)) = R_N^{o(1)}`, so
`R_N ≥ R_T + Q`, and `T < N` because `L = O(log N)`. Theorem 1.3 with `k = m` gives
`s_n ≥ m + 1 > κL ≥ κ ℓ(R_n)` for some `n ∈ [T, N)`, against `κ > K`. ∎

**Theorem 1.5 (unit record increments force the recurrence; r01 Theorem 4).**
Under (H), if `R_{n+1} − R_n ≤ 1` for all large `n` then `a_{n+1} = a_n² − a_n + 1`
eventually. No hypothesis on drawdowns, on record-setting jumps, or on `h_n`.
*Proof.* Otherwise `u_n → ∞`. For a late fresh `j` put `B = R_{j+1} + 2`; if every
exact prime power of `a_j` were `≤ B` then `a_j ∣ lcm(1..B)` and
`log a_j ≤ B log B = exp(o(j))`, against `log a_j ≥ c 2^j`; so some
`P = p^e ∥ a_j` has `P > R_s + 2`, `s = j + 1`, and `P ∣ v_s`. Let `H` be the least
multiple of `p` above `R_s`, so `R_s < H ≤ R_s + p`. At the first `t > s` with
`u_t ≥ H`, `R_{t−1} ≤ H − 1` and `u_t = R_t ≤ R_{t−1} + 1 ≤ H`, so `u_t = H`.
Before `t`, `w_n < (3/2)u_n < (3/2)H ≤ (3/2)(R_s + p) < p·P` (using
`P ≥ R_s + 3`, `p ≥ 2`), so `P ∣ v_t` by the valuation threshold, and `p ∣ u_t = H`
contradicts primitivity. ∎ Hence the exact equivalence
`(S) ⟺ #{n : R_{n+1} − R_n ≥ 2} < ∞` (the converse is `u_n = 1` on a Sylvester
tail). Lean: `unit_recordIncrement_cut`,
`recordIncrementOne_sylvesterNext_eventually` (`RecordIncrementBarrier.lean`), with
the prime-power supply an explicit hypothesis; the supply is discharged at every late
index by Lemma 2.3 below.

**Relation.** Theorem 1.5 is incomparable with the two-unit theorem
(`primitive_record_two_unit_rigidity`): a record-setting jump of size `≤ 2` bounds
`s_n ≤ 2`, not `≤ 1`, and `s_n ≤ 1` allows arbitrarily large record-setting jumps
after a drawdown. The fixture
`(8,177) →[a=23] (7,4071) →[a=583] (10, 2373393)` has records `8, 10` (increment
`2`, jump `3`, `gcd(8,10) = 2`), which is why the odd-cut parity step does not
transfer from jumps to increments and why `s_n ≤ 2` is not covered by either
theorem. In the unreduced `C` coordinates the corpus already had bounded record
increments ⟹ Sylvester through the rescaling clause of the record-excess dichotomy;
the new content of Theorem 1.5 is the primitive coordinate with arbitrary
cancellation and the elementary landing argument. Theorem 1.4 is new.

**Fixture (r01 §6, exact).** `u = d²k − 1`, `v = (d−1)u − 1`: `a = d`, `e = −1`,
`w = d²k`, `h = d²`, `u' = k`, `v' = k(d² − d) − 1`, `a' = d² − d + 1`, `e' = −1`;
`|e|/u = 1/(d²k − 1)`, `|e'|/u' = 1/k`, `a'/a² = 1 − 1/d + 1/d²`. Tiny normalised
errors and near-quadratic growth coexist with a square payment `d²`, and with
`k = d` the state after the step has `ℓ(G')/ℓ(R') → 1`: local centring cannot
exclude the cancellation regime left open by Theorem 1.4.

## 2. Reusable odd prime-power barriers and the epoch energy (r02)

**Lemma 2.1 (protection; r02 Lemma 1)** is `primitive_valuation_no_drop` /
`protectedPrimePower_persists`: `p^ℓ ∣ v_n` and `0 < w_n < p^{ℓ+1}` give
`p^ℓ ∣ v_{n+1}` and `p ∤ u_{n+1}`, through paid steps as well as clean ones.

**Theorem 2.2 (finite epoch inequality; r02 Lemma 2).** Let the orbit satisfy the
primitive cocycle and `2|e_n| < u_n` from `s`; let `p ≥ 3` be prime,
`Q = p^ℓ ∣ v_s`, `Q ≥ 16`, `L = pQ/2`, `R_s < L/2`, and let `τ` be the first index
with `u_τ ≥ L`. Let `J` be the set of steps in `[s, τ)` that first cross at least one
barrier of `ℋ`, `K = |J|`, `X = Σ_{n∈J}(d_n − 2)`. Then every `n ∈ J` is a clean
record with `d_n ≥ 3`, and
`(1 + 1/p) K + X/(2p) ≥ Q/8 − 1`, i.e. in integers `pQ ≤ (8p + 8)K + 4X + 8p`.
Consequently `Σ_{n∈J} (1/√u_n + (d_n − 2)/u_n) ≥ 1/16`.
*Audit.* For `s ≤ n < τ`, `u_n < L` so `w_n < (3/2)L = (3/4)pQ < p^{ℓ+1}`, and
Lemma 2.1 keeps `Q ∣ v_t`, `p ∤ u_t` on `[s, τ]`. Each barrier `H ∈ ℋ` exceeds `R_s`
and is reached by `τ`; its first crossing `n+1` has `R_n < H ≤ u_{n+1}`, a record,
hence `h_n = 1`; `d_n ≤ 2` would need the landing `H` (killed by `p ∣ v_{n+1}`) or
the pair `(H−1, H+1)`, both even against `gcd(u_n, u_{n+1}) = 1`. The barriers
first crossed at step `n` lie in `(u_n, u_n + d_n]` with spacing `2p`, so their
number is `≤ 1 + d_n/(2p)`; summing over `J`, `|ℋ| ≤ (1 + 1/p)K + X/(2p)`, and
`|ℋ| ≥ (L/2)/(2p) − 1 = Q/8 − 1`. For the energy, `u_n < L` on `J`,
`(1 + 1/p)√L ≤ Q` (⟺ `(p+1)² ≤ 2pQ`, true for `p ≥ 3`, `Q ≥ p`) and
`L/(2p) = Q/4 ≤ Q`, so `Q/16 ≤ Q/8 − 1 ≤ |ℋ| ≤ Q Σ_J(1/√u_n + (d_n − 2)/u_n)`. ∎
Lean: `barrierIdx`, `barrierIdx_card_lower`, `fibre_card_le_spacing`,
`protected_epoch_energy_integer` (`ProtectedEpochEnergy.lean`, kernel rc `0`, axioms
`propext`, `Classical.choice`, `Quot.sound`). The Lean form needs no minimality of
`τ`: any index with `pQ ≤ 2u_τ` works, each barrier taking its own first crossing,
so the statement holds at every index after the orbit has reached `pQ/2`; and it
derives `h_n = 1` at every strict rise from `2w_n ≤ 3u_n` alone. The barrier count
in integers is `Q ≤ 8|ℋ| + 8` with `ℋ` indexed by `[(Q+4)/8, (Q−2)/4]`; the naive
lower index `Q/8 + 1` loses one barrier and is insufficient. This is the quantitative
record-excess obligation left `OPEN` in `PrimitiveRecordBarrier.lean` (r07
Theorem 8), in a sharper form: one protected odd prime power is reused across
`≈ Q/8` barriers with no CRT product of moduli in the denominator, at the price of
stopping at the protection scale `pQ/2`. The real-valued `1/16` corollary is an
ordinary proof over the integer theorem.

**Lemma 2.3 (odd prime-power supply at every late index; r02 Lemma 3).** With
`Q_n = max{p^{ν_p(v_n)} : p odd, p ∣ v_n}`, for every fixed `A > 0`,
`Q_n / R_n^A → ∞`. *Audit.* At most one fresh digit is even (after the first even
digit, `2 ∣ Λ_n`), and nonfresh indices number `o(n)`, so every large `n` has an odd
fresh `j ∈ [n/2, n)`; `h_j = 1` and `a_j ∣ v_n ∏_{j<k<n} h_k`, so the odd part `S_n`
of `v_n` has `S_n G_n ≥ a_j`, hence `log S_n ≥ c 2^{n/2} − o(n)`. Since `S_n` has at
most `Q_n` prime-power components each `≤ Q_n`, `log S_n ≤ Q_n log Q_n`, so
`Q_n ≥ e^{ηn}`, while `R_n ≤ C_n = e^{o(n)}`. ∎ **Relation.** This strengthens the
supply hypothesis `hsupply` of `recordRiseTwo_sylvesterNext_eventually` (arbitrarily
late `s` with `3R_s < p^ℓ`) to *every* late index with any polynomial margin; it
also discharges the supply of Theorem 1.5 (`R_s + 3 ≤ p^ℓ`), which needs no oddness.

**Theorem 2.4 (energy criterion; r02 (9), (11)).** Under (H),
`𝓔 < ∞ ⟺ (S)`, and `Σ_{n record} (d_n − 2)_+/√u_n < ∞ ⟺ (S)`. *Proof.* On a
Sylvester tail `u_n = 1` and there are no late records. Otherwise `u_n → ∞`; for every
late `s`, Lemma 2.3 supplies `Q ∣ v_s` odd with `Q ≥ 16` and `R_s < pQ/4`, the first
crossing of `pQ/2` exists, and Theorem 2.2 puts energy `≥ 1/16` in `[s, τ)`; tails of
a convergent series tend to zero. The second form follows from
`1/√u + (d−2)/u ≤ 2(d−2)/√u` for `d ≥ 3`. ∎ **Relation.** The corpus's weighted
LCM record theorem (`LcmRecordExcess.md` (E)) gives divergence of
`Σ_{U-records} (−V_n − B)_+ f(U_n)` for every decreasing `f` with divergent
integral, including `1/√t`, but in the LCM coordinates `U = C/M` where old
divisors persist; Theorem 2.4 is the primitive-coordinate statement with arbitrary
cancellation, where old divisors can be deleted, and the `√` weight is the price of
protecting one prime power at a time. The unweighted primitive divergence
`Σ_{n record}(−e_n − 2)_+ = ∞` of `EightReturnRigidityCriteria.md` §3 is the `f ≡ 1`
case; the `1/√u_n` weight is new.

**Fixtures (r02 §8, exact).** `(u₀, v₀) = (19, 1792818711)`, `a₀ = 94358881`,
`27 ∣ v₀`: the steps `(19,−9,1,28), (28,−9,1,37), (37,−9,1,46)` are clean; with
`p = 3`, `Q = 27`, `L = 81/2`, the barriers `21, 27, 33, 39` are first crossed at
steps `0, 0, 1, 2`: one jump crosses two barriers, which is why the per-step
capacity `1 + d/(2p)` and not `1` enters. The projection-only walk avoiding
multiples of a large prime `p` with unit steps except `H−1 → H+1` (H even),
`H−1 → H+2` or `H−2 → H+1` (H odd) has `Σ_{3-jumps} (d−2)/u = O(log p / p)` up to
height `p²/2` while `Σ_{3-jumps} u^{−1/2}` stays of constant order: the `1/√u`
incidence term cannot be dropped from `𝓔`.

## 3. Global prime retention and first-contact counting (r03)

**Theorem 3.1 (sandwich).** `M_n ∣ G_n ∣ M_n²`; equivalently `J_n = M_n²/G_n ∈ ℕ`
with `J_n ∣ J_{n+1}`. *Proof.* `h_n ∣ d_n²` for `d_n = gcd(a_n, v_n)` (normal form
`h = bc² ∣ (bc)²`), and `d_n ∣ ρ_n = gcd(Λ_n, a_n)` since `v_n ∣ Λ_n`; so
`h_n ∣ ρ_n²` and `J_{n+1}/J_n = ρ_n²/h_n ∈ ℕ`, with `J_1 = 1`. The lower bound
`M_n ∣ G_n` is `cumulativeOverlapDebt_dvd_tailNumerator` (`G_n = κ'_n M_n`). ∎
New exact sandwich; the upper bound is the first inequality in the corpus bounding
`G` by `M` rather than the reverse. It transfers every lower bound on `G_N` below
into a lower bound `M_N ≥ √G_N` on the LCM overlap debt (§10).

**Theorem 3.2 (retention; r03 Theorem 1).** With `𝓕_N` the fresh sources below `N`
with `a_j > 1`, `𝓧_N` those with `gcd(a_j, v_N) = 1` and `𝓨_N` those whose support
was entirely absent at some time `≤ N`:
`A_N/gcd(A_N, κ_N) ∣ v_N`, `∏_{𝓧_N} a_j ∣ κ_N`, `∏_{𝓨_N} a_j ∣ M_N`,
`|𝓧_N| ≤ log₂ log(3 + κ_N) + B`, `|𝓨_N| ≤ log₂ log(3 + M_N) + B`, hence
`ω(v_N) ≥ N − 2 − log₂ M_N − |𝓧_N| = N − o(N)`, and `P⁺(v_N)/N → ∞` (an actual
limit, from `π(x) = o(x)`). Complete erasure of fresh `a_j` at time `t_j` needs
`t_j / 2^j → ∞`. *Audit* straightforward from `A_N ∣ Λ_N = κ_N v_N`, pairwise
coprimality of fresh digits and `log a_j ≥ c 2^j`. **Relation.** Strengthens the
prime-height dichotomy (`primitive_height_prime_height_dichotomy` (b)) from a
subsequential to an actual limit in the linear-numerator branch; `ω(v_N) ≥ N − o(N)`
is the denominator-side form of the conductor's roughness lemma.

**Theorem 3.3 (first-contact count; r03 Theorem 2).** With `P_j` a largest exact
prime power of a fresh `a_j`, `p_j` its prime, `τ_j` the first `t > j` with
`p_j ∣ U_t`, and `K_N = #{j ∈ 𝓕_N : τ_j ≤ N}`:
`∏_{τ_j ≤ N} P_j ∣ M_N`, `∏_{τ_j ≤ N} p_j P_j ∣ G_N`, and
`K_N ≤ A + √(2 log₂ M_N) = o(√N)`. *Audit.* The first-contact resonance of
`R2CumulativePayment.md` gives `ν_p(a_s) = ν_p(Λ_s) = ℓ ≥ e` at `s = τ_j − 1` and
`p^{ℓ+1} ∣ h_s`; contact times may coincide, the factors then multiply inside the
same `ρ_s`, `h_s`. From `a_j ∣ lcm(1..P_j)` and `log lcm(1..m) ≤ 4 m log 2`,
`log₂ P_j ≥ j − b`; a sum of `k` distinct birth indices is `≥ k(k+1)/2`, giving the
square root. ∎ Incremental over R2 (which had the product divisibility); the count is
new.

**Construction 3.4 (simultaneous erasure; r03 Theorem 3).** Sylvester prefix
`s_1, …, s_m` (`2, 3, 7, 43, …`), `P = ∏ s_j`, `Q = P(P−1) + 1`, digits
`s_1, …, s_m, P, Q+1, Sylvester tail of 1/Q`; the sum is `1 + 1/Q`, the sequence is
strictly increasing with `a_{n+1}/a_n² → 1`, the first `m` digits are fresh, and at
the step with multiplier `P` all their primes leave the reduced denominator at once
with `ρ = P`, `h = P²`, `M = P`, `G = P²`, `κ = P`, `sup |θ_n| ≤ 1/(P−1)`. For
`m = 2`: `32/31 →[2] 33/62 →[3] 37/186 →[6, h=36] 1/31`, after which the prime `2`
re-enters (`M: 6 → 12`, `κ: 6 → 3`). This is a genuine sequence satisfying (H) that is
eventually Sylvester; it rules out any universal surcharge for many simultaneous
contacts beyond the exact `ρ = P`, `h = P²`, and shows `κ` measures current missing
content while `M` retains past erasure. Replayed exactly for `2 ≤ m ≤ 8`.

## 4. Square deletion and record-amplified rigidity (r04)

**Proposition 4.1 (saturated square transport; r04 Proposition 1).** At every
primitive step, in the normal form `h = bc²`, `a = bcℓ`, `v = bcs`, `v' = bℓs`,
`b e e' ≡ (v/c)² = (bs)² (mod u')`, and `b`, `s`, `ℓ` are units modulo `u'`.
*Proof.* `v − ae = (a−1)w` so `ae ≡ v (mod w)`; `h e' = av − (a'−1)w` so
`h e' ≡ av (mod w)`; multiplying, `w ∣ v² − h e e'`, i.e.
`bc²u' ∣ bc²(bs² − ee')`, and cancelling `bc²` gives `u' ∣ bs² − ee'`; multiply by
`b`. Units: `v' = bℓs` is coprime to `u'`. ∎ **Relation.** Strictly stronger than
`unconditional_square_transport_legendre_defect_charge` Lemma S1, which worked
modulo the largest divisor of `u'` coprime to `G_{n+1}`; here the modulus is the
whole `u'` and the pure-square part `c²` of the payment has been divided out.
Corollary: for every odd prime `p ∣ u_{n+1}`, `(e_n e_{n+1} ∣ p) = (b_n ∣ p)`, so a
Legendre defect forces `b_n`, hence `h_n`, to be a non-square, `h_n ≥ 2`, and the
defect count below `N` is `≤ log₂(G_N/G_0)`. **Limitation (exact).** A pure-square
payment `h = c²` has `b = 1` and is invisible: the family
`u = p²k − 1`, `a = pz`, `v = (a−1)u − 1` (`z ≡ 1 (k)`, `z ≡ 0 (k+1)`, `p ∤ z`) has
`e = −1`, `h = p²`, `c = p`, `b = 1`, `u' = k`, `e' = −1`, `ee' = 1 ≡ (v/c)² (mod k)`,
then `h' = k + 1`, `u'' = 1`. Lean (`SaturatedSquareTransport.lean`, kernel rc `0`,
axioms clean): `squareTransport_core_identity` (the ring identity
`h e e' − v² = w·κ` with explicit `κ`, no hypotheses), `saturated_square_transport_raw`
(`u' ∣ h e e' − v²` from the two cocycle equations alone, no normal form, any next
multiplier), `saturated_square_transport_explicit` and the gcd wrapper
`saturated_square_transport` (`d = gcd(a,v)`, `c = gcd(w/d, d)`, `b = d/c`,
`ℓ = a/d`, `s = v/d`, via `gcd_multiplier_rawNumerator : gcd(a, w) = gcd(a, v)`),
`isSquare_content_defect_mod_prime`, `legendre_defect_forces_nonsquare_content`
(`b ≠ 1`), `isSquare_error_product_of_isSquare_content`,
`not_isSquare_payment_of_not_isSquare_content` (`h` not a perfect square, through
`c² ∣ k² ⟹ c ∣ k`). The raw form shows the saturation itself needs neither the
normal form nor the next raw-numerator relation `w' + v' = a'u'`; the factorisation
only normalises the defect and supplies the unit clauses.

**Lemma 4.2 (a cancellation is visible at the next negative error; r04 Lemma 2).**
If `t` is the first index after `s` with `e_t < 0`, then `u_t ≤ u_{s+1}` and
`A_t ≥ u_s/u_{s+1} = h_s/(1 − e_s/u_s)`; in integers
`u_s u_t ≤ R_t m_t u_{s+1}`. Equality in the family above:
`A_1 = (p²k − 1)/k = p² − 1/k = h_0/(1 − e_0/u_0)`. Lean:
`recordAmplified_error_after_cancellation` (`SaturatedSquareTransport.lean`); the
step `u_{n+1} ≤ w_n` needs `w_n > 0`, carried as an explicit hypothesis, and the
conclusion compares `u_t` with `u_{s+1}`, the paying step `s` lying outside the
nonnegative window.

**Theorem 4.3 (finite CRT-or-deletion alternative; r04 Theorem 3).** With
`|e_n/u_n| ≤ η < 1` from `N`, `T ≥ N`, distinct primes `p_0, …, p_{B−1} ∣ v_T` with
`E_i = ν_{p_i}(v_T)`, `P = ∏ p_i`, `x ∈ (R_T, R_T + P]` the CRT representative with
`p_i ∣ x + i`, and `τ` the first `n > T` with `u_n ≥ x`:
`max_{T≤n<τ} A_n ≥ min{B + 1, min_i p_i^{E_i+1}/(1 + η)}`.
*Audit.* If `u_τ ≥ x + B` the record-setting jump is `≥ B + 1 ≤ m_{τ−1} ≤ A_{τ−1}`.
Otherwise `u_τ = x + i`, `p_i ∣ u_τ`, so `p_i` left `v` at a first drop step
`s ∈ [T, τ−1]` with `p_i^{E_i+1} ∣ h_s` (Lemma 7 of the first batch), `h_s ≥ 4`,
`u_{s+1} ≤ (1+η)u_s/4 < x`; a negative error must occur in `[s+1, τ−1]` (else `u` is
nonincreasing up to `τ`), and Lemma 4.2 at the first one gives
`A_t ≥ h_s/(1−ε_s) ≥ p_i^{E_i+1}/(1+η)`. ∎ A landing inside the forbidden block is
allowed, but only through a valuation drop whose cost is charged to the next
negative error before the crossing. This is the mechanism the first batch said was
capped at jump `2`: it does not protect the primes, it prices their deletion.

**Lemma 4.4 (supply; r04 Lemma 4).** For every `B` and `y` there are arbitrarily late
`T` with `B` distinct primes `> y` dividing `v_T`: paid steps have density zero, so
arbitrarily late blocks of `B + π(y)` consecutive clean steps exist, on which the
multipliers are pairwise coprime and all divide the final denominator, and at most
`π(y)` of them are `y`-smooth. ∎

**Theorem 4.5 (record-amplified rigidity; r04 Theorem 5 and (1)).** Under (H),
`(S) ⟺ limsup A_n < ∞ ⟺ limsup R_n δ_n < ∞`, where `δ_n = (a_n²/a_{n+1} − 1)_+` and
`R_n = max_{N≤j≤n} u_j`; both limsups are `0` or `+∞`. *Proof.* On a non-Sylvester
orbit, for every `B` take `y > √((1+η)(B+1))`, `T` from Lemma 4.4, and `x` from
Theorem 4.3; the crossing exists since `u_n → ∞`, and `p_i^{E_i+1}/(1+η) ≥ p_i²/(1+η)
> B + 1`, so some `A_n ≥ B + 1`. The transfer uses `|δ_n − m_n/u_n| ≤ 3/a_n` and
`R_n/a_n → 0`. ∎ **Corollary 4.6.** Under (H) and `δ_n = O(1/n)` (no convergence of
`nδ_n` assumed), `(S) ⟺ u_n = O(n) ⟺ (−e_n)_+ = O(1)`; so a counterexample at the
critical rate has `limsup u_n/n = ∞` and `limsup (−e_n)_+ = ∞`. This removes the
convergence hypothesis of the first batch's Proposition 24. **Relation.** New
criterion with arbitrary cancellation and no bound on the jump size; it is
incomparable with the two-unit theorem (bounded `A_n` implies bounded jumps, but
bounded jumps do not bound `A_n` through deep drawdowns) and strictly generalises the
clean bounded-rise barrier along the `A_n` axis. Structural consequence: on a
counterexample either record-setting jumps are unbounded or infinitely many distinct
primes occur among the deleted factors `c_n`.

**Fixture (r04 §6, exact).** `15/134 = 1/10 + 1/85 + 1/5695` with primitive steps
`(15,134) →[a=10, e=−1, h=4] (4,335) →[a=85, e=−1, h=5] (1,5695)`; `A_1 = 15/4` meets
Lemma 4.2 with equality. The family shows arbitrarily large finite record-amplified
errors with all normalised errors `≤ 1/k`, none of which extends to an infinite orbit.

## 5. The continuation defect (r05) — external dependency

r05 defines the Kovač–Tang terminal-decomposition payoff
`𝓑(P, Q, L) = sup 2^{−r} H(T)` over decompositions `P/Q = Σ_{i≤r} 1/b_i + 1/T`,
`L < b_1 < ⋯ < b_r < T`, with `H(t) = lim 2^{−k} log Φ^{∘k}(t)`, `Φ(t) = t(t+1)`, and
the loss `𝓛_n = 2𝓑_n − 𝓑_{n+1}` along the orbit. Verified here without external
input: `H(t) = log t + χ(t)` with `0 < χ(t) ≤ log(1 + 1/t)` and `H(Φ(t)) = 2H(t)`;
the greedy lower bound `𝓑(P, Q, L) ≥ H(Q/P)`; `𝓛_n ≥ 0`; the counterfactual lower
bound `𝓑_n − λ_n ≥ ½ log(u_n/m_n) − o(1)` at negative indices, where
`λ_n = lim 2^{−k} log a_{n+k}` satisfies `λ_{n+1} = 2λ_n`, `λ_n − log a_n → 0`; the
exact family `4/43 = 1/12 + 1/104 + 1/13416` and its parameters (40)–(48). **Not
verified here:** the sharp upper envelope `𝓑(u, v, L) − H(v/u) < ½ log u` (r05
Theorem 1), which rests on Lemma 11 of Kovač–Tang, arXiv:2607.28387v2, a paper this
pass could not access (and the return itself could not reach the pinned repository).
Everything downstream of that envelope (the clean-step loss bound
`𝓛_n ≥ log(√(h(u+m))/m) − 3/a_n`, the discounted identity
`𝓑_n − λ_n = Σ 2^{−j−1}𝓛_{n+j}`, and the equivalence `(S) ⟺ 𝓛_n eventually bounded`)
is therefore recorded as `blocked_external` with re-entry condition: verify or
reprove the first-descent comparison (if the cleared numerator never falls below `P`
the reciprocal remainder is `≤ Φ^{∘r}(Q/P)`; at a first descent to `d < P`,
`t_r < (P/d)Φ^{∘r}(Q/P)` and `t_r > b_r`). The conditional chain is a genuinely new
coordinate (an optimisation payoff whose loss is positive on clean negative steps,
unlike every gcd or Legendre charge), and its missing implication (53) is again
exactly the parent.

## 6. Two-modulus cut and the `4/3` alternative (r06)

**Lemma 6.1 (two-modulus cut; r06 Lemma 3).** Let `H ≡ 5 (mod 6)`, `m ∣ H`,
`ℓ ∣ H + 2`, with `m, ℓ > 1` dividing both `v` and `v'` at one primitive step. Then
no step has `u < H ≤ u'` with `u' − u ≤ 4`. *Proof.* Landings `H` and `H + 2` are
killed by `m ∣ v'`, `ℓ ∣ v'` and primitivity; landing `H + 1` from `H − 3` or `H − 1`
has both endpoints even, from `H − 2` both divisible by `3` (`H + 1 ≡ 0`,
`H − 2 ≡ 3 (mod 6)`); landing `H + 3` from `H − 1` has both endpoints even; all
against `gcd(u, u') = 1`. ∎ Exhaustive over `H < 2400`. The cut does not extend to
`5`: `(u, v) = (33, 5·37·41)`, `a = 231`, `e = −5`, `u' = 38`, `h = 1`, with
`H = 35`, `5 ∣ 35`, `37 ∣ 37`, is a genuine primitive step crossing both forbidden
landings with coprime endpoints. Lean: `two_modulus_cut`, `two_modulus_record_cut`
(`TwoModulusRecordCut.lean`, kernel rc `0`, axioms clean; the escape fixture is
checked by `norm_num`). The Lean cut uses only `m ∣ v'`, `ℓ ∣ v'`, `gcd(u', v') = 1`
and `gcd(u, u') = 1`; the hypotheses `m, ℓ ∣ v` and `gcd(u, v) = 1` of the return
are unused, and only four landings arise since `u' = H + 4` needs `u = H`.

**Theorem 6.2 (all but one old modulus must pay; r06 Theorem 4).** Let
`2 ≤ m_1 < ⋯ < m_L`, `L ≥ 2`, be pairwise coprime divisors of `v_T` coprime to `6`,
and suppose every record-setting step in `[T, N)` has jump `≤ 4` and
`u_N ≥ R_T + 6 m_{L−1} m_L + 4`. Then there is `i₀` with
`(∏_{i≠i₀} m_i)² ∣ G_N/G_T`, hence `G_N/G_T ≥ (m_1 ⋯ m_{L−1})²`. *Audit.* Let
`K_i` be the product of the primes of `m_i` dividing every `v_t`, `T ≤ t ≤ N`. If
`K_i, K_j > 1` for `i ≠ j`, CRT gives `H ≡ 0 (K_i)`, `H ≡ −2 (K_j)`, `H ≡ 5 (6)` in
`(R_T, R_T + 6K_iK_j]`; the first crossing of `H` is a record with jump `≤ 4`,
contradicting Lemma 6.1. So all but one `m_i` have every prime disappear at some
time in `(T, N]`, and Lemma 1.2 charges `m_i²` to `G_N/G_T`; the moduli are pairwise
coprime. ∎ The historical `K_i` is essential: replacing it by `gcd(m_i, v_N)` would
forget a prime that disappeared and returned.

**Theorem 6.3 (jumps `≤ 4` force `4/3` cancellation at records; r06 Theorem 5).**
Under (H) on a non-Sylvester orbit whose late record-setting jumps are `≤ 4`,
`limsup_{records} log G_n / log u_n ≥ 4/3`, hence
`limsup_{records} log G_n / log C_n ≥ 4/7`. *Audit.* Take a late fresh block
`a_t, …, a_{t+L−1}` coprime to `6` (density one; `2` and `3` occur in at most one
fresh multiplier each), all dividing `v_T`, `T = t + L`; `Z_t = R_T + 6a_{t+L−2}a_{t+L−1} + 4`;
the first `N` with `u_N ≥ Z_t` is a record with `u_N ≤ Z_t + 3`; Theorem 6.2 gives
`G_N ≥ (∏_{j=t}^{t+L−2} a_j)²`; with `log a_j = κ2^j + o(1)` and `R_T = e^{o(T)}`,
`log u_N = κ 2^t · 3 · 2^{L−2}(1 + o(1))` and `log G_N ≥ 2κ 2^t (2^{L−1} − 1)(1 + o(1))`,
ratio `→ (4/3)(1 − 2^{1−L})`; let `L → ∞` after `t → ∞`. ∎ **Corollary 6.4
(unconditional alternative).** A counterexample has infinitely many record-setting
jumps `≥ 5`, or `limsup_{records} log G_n / log u_n ≥ 4/3`. Sufficient criterion:
jumps eventually `≤ 4` and `G_n ≤ u_n^{4/3 − η}` at late records force (S).
**Relation.** Extends the reach of the two-unit barrier from `2` to `4` at the cost
of a cancellation conclusion instead of the endpoint; the first batch's "cap at two
is structural" referred to simultaneous protection of `B` moduli, which this theorem
does not need.

**Fixture (r06 §6, exact).** `u = P²t + 1`, `v = (P−1)u + 1 = P(P(P−1)t + 1)`,
`P = p^b`: `a = P`, `e = 1`, `h = P²`, `u' = t`, `p ∤ v'`, `a' = P(P−1) + 1`,
`e' = 1`; the whole prime power is erased with payment `P²` while `e/u = 1/(P²t+1)`
and `e'/u' = 1/t` are arbitrarily small and `a'/a² = 1 − 1/P + 1/P²`.

## 7. Uniform quadratic anti-shadowing (r07)

**Theorem 7.1 (r07 Theorem 1).** For every exact integer orbit
`C_{n+1} = a_n C_n − D_n`, `D_{n+1} = a_n D_n` (no positivity or growth needed),
every monic `Q ∈ ℤ[X]` of degree two and every `λ ∈ ℚ^×`, with
`W_4 = {n : C_{n+j} = λQ(n+j), 0 ≤ j < 4}`:
`lim_{L→∞} sup_M #(W_4 ∩ [M, M+L))/L = 0`, and every interval of length `≥ L₀(ε)`
has at least `(1/4 − ε)` of its indices with `C_n ≠ λQ(n)`. Unless
`Δ = b² − 4c = 4k² + 1` (`k ≥ 1`), the same holds with `W_3` and `1/3`. *Audit.*
With `t² = Δ`, `α = (−b+t)/2`, `Q(α + j) = j² + jt`, so `−Q(α−1)Q(α+1) = Δ − 1 =: K`.
Chebotarev (Sutherland 18.785 Thm 28.9) supplies a positive-Dirichlet-density set of
primes with a degree-one place of `ℚ(√Δ)` at which a given nonsquare of that field
(or two simultaneously) reduces to a nonresidue; at the class `n ≡ (−b+t)/2 (mod p)`
a three-term agreement gives `D_{n−1}² ≡ λ²K (mod p)` (from the identity
`D_{n−1}² ≡ −C_{n−1}C_{n+1}` at a numerator zero), impossible when `K` is a
nonresidue. `K` is a square in `ℚ(√Δ)` only if `K` or `K/Δ` is a rational square;
`(Δ−1)/Δ` never is (consecutive integers), so the exception is `K = 4k²`,
`Δ = 4k² + 1`; `Δ = 1` gives the word `(0, 0, 2λ)` against absorbing double zeros.
In the exception, four-term agreement `(4−2t, 1−t, 0, 1+t)·λ` forces
`D_{n−1} = ±2kλ` and, one step earlier via `C_{n−2}D_{n−1} = D_{n−2}(D_{n−2} + C_{n−1})`,
`z² + (1−t)z − 2sk(4−2t) = 0` with discriminants
`L_s = (4k²+2+32sk) + (−2−16sk)t`, `N(L_s) = −16k(63k³ − 48k − 4s) < 0`, so both are
nonsquares in the real quadratic field; Chebotarev again supplies infinitely many
primes forbidding both signs. Fix a finite set `𝓕` of such primes; the indices
avoiding all forbidden classes number `≤ (∏_{𝓕}(1 − 1/p)) L + ∏_{𝓕} p` in any
interval of length `L`; `Σ 1/p = ∞` over the supply lets the density tend to `0`
before `L → ∞`. Replayed: `k = 1`, `p = 11`, `t = 4` gives the corpus word
`(7,8,0,5)` with discriminants `10, 8`, both nonresidues mod `11`; the norm identity
holds for `k ≤ 12`. ∎ **r4 (2026-09-07).** The negative-norm step uses
`k ∈ ℤ_{≥1}`. At `k = 1/2`, `N(L₊) = 161 > 0` and `N(L₋) = 97 > 0`, so that
sign argument does not transfer unchanged to monic `Q ∈ ℚ[X]`. Both particular
norms are nonsquares, so the examples do not defeat a square-class obstruction;
they defeat only the verbatim-transfer claim. **Corollary 7.2.** Under (H), the same density statements hold
for the primitive `u_n` and the LCM `U_n` in natural density, after discarding the
density-zero set of windows containing a paid step (`h_n > 1`, resp. `ρ_n > 1`).
**Relation.** Strict strengthening of `polynomial_profile_rigidity` (C): the
single-certificate lower density `1/m` becomes `1/4` (`1/3` generically), uniform
over the interval's position, for every rational multiple of every monic integer
quadratic; the corpus's "density version at prime moduli is structurally blocked"
concerns forbidden residue words on the orbit's own residues, not agreement with a
fixed template, and is not contradicted. Not Lean-landable (Chebotarev).

## 8. Rising-factorial cubic profiles and the cubic-rate irrationality (r08)

**Theorem 8.1 (r08 Theorem 1).** For every exact positive integer orbit and every
`A ∈ ℚ_{>0}`, `B ∈ ℚ`, `liminf_X #{n ≤ X : C_n ≠ A n(n+1)(n+2) + B}/X > 0`. *Audit.*
Lower density zero of exceptions gives four consecutive agreements arbitrarily late,
so `Δ³C = 6A` there and `G_n ∣ 6A`; `G` stabilises at `g`; the primitive tail has
`gcd(u_n, u_{n+1}) = 1` and `Q = P/g` integer-valued, `Q(n) = (m/6)n(n+1)(n+2) + c`
with `m = 6A/g ∈ ℕ`, `c = B/g ∈ ℤ`; a prime `ℓ ∣ c` (or `c = 0`) makes
`ℓ ∣ Q(n), Q(n+1)` on `n ≡ −1 (mod 6ℓ)`, so `c = ±1`; a rational root forces
positive lower density of exceptions (corpus rational-root exclusion); for
irreducible `f(T) = T³ − T + 6c/m` (`Q(n) = (m/6) f(n+1)`), a numerator zero at
`k ≡ r − 1` gives `−Q(k−1)Q(k+1) = 9(m/6)² r²(r² − 1)` a square mod `ℓ`
(from `u_{k+1} ≡ −a_{k−1}² u_{k−1}` at `u_k ≡ 0`), so by Chebotarev square
specialisation `α² − 1 ∈ ℚ(α)^{×2}` for a root `α`. With `β² = α² − 1`, `z = α + β`,
`α = (z + z^{−1})/2`, and `Z³ + bZ² + dZ + w` the minimal polynomial of `z`: the
trace conditions `Tr α = 0`, `Tr α² = 2`, `Tr α³ = −3η` give `d = −bw`,
`(bw − 1)(b + w) = 0`, `η = (b²+1)(w + w^{−1})/8`, hence
`m = 48c·rs³/(r²+s²)²` or `48c·r³s/(r²+s²)²` for `w = r/s`, and
`gcd(r² + s², rs) = 1` forces `(r² + s²)² ∣ 48`, so `|r| = s = 1` and `m = 12`. The
two survivors `2n(n+1)(n+2) ± 1` have the numerator words `(1,6,0,2)` and
`(4,5,0,1)` mod `7`; a middle zero forces `d_1² ≡ −c_1c_3 ≡ 2`, so `d_1 ∈ {3,4}`,
while `d_1 = d_0(d_0 + c_1)/c_0` has image `{0,2,5,6}` over `d_0 ∈ 𝔽_7`; neither word
is realizable, giving lower density `≥ 1/7` **only for these two primitive
profiles** by disjoint four-index blocks (plus starts `n ≡ 0 (mod 7)`, minus
starts `n ≡ 1 (mod 7)`). The factor `1/(4·7) = 1/28` is word-period accounting,
not a stronger uniform constant. An unrestricted “no four consecutive
agreements” wording is false: the plus profile admits a primitive four-step
state at indices `1,2,3,4`. The reductions assume lower density zero; the
supported conclusion for a general rational cubic `A n(n+1)(n+2)+B` is
**positive** lower density of exceptions, not a uniform `1/7` or `1/28` over
all `A, B`. ∎ All finite claims replayed
exactly. **r2 density repair (2026-09-06).** A universal `1/28` was an illicit
quantifier shift: Chebotarev/gcd reductions are under the density-zero
hypothesis, so they yield positivity per fixed profile. Keep `1/28` only as
word-period accounting after the trace calculation has reduced to
`2n(n+1)(n+2)±1`. **r3 (2026-09-07).** Terminal-profile `1/7` landed; do not
restore a universal density.

**Lemma 8.2 (integer extraction at a regular rate; r08 Lemma 4).** If positive
integers satisfy `C_{n+1}/C_n = 1 + λ/n + o(n^{−λ})` with `λ > 1`, then `λ = d ∈ ℕ`
and `C_n = A n(n+1)⋯(n+d−1) + B` eventually. *Audit.* With `F_{n+1}/F_n = 1 + λ/n`,
`C_n/F_n → K` at rate `o(n^{1−λ})`, so `d_n = C_n − KF_n = o(n)` and
`Δd_n = (λ/n)d_n + ε_nC_n = o(1)`; for integer `j > λ`, `Δ^jF_n → 0` and
`Δ^jd_n → 0`, so the integer `Δ^jC_n` vanishes eventually; degree comparison gives
`λ = d` and `F_n` is a constant times the rising factorial; the `o(n)` difference of
two polynomials is constant. ∎ The `o(n^{−λ})` is sharp: `n(n+1)(n+2) + (−1)^n` has
ratio `1 + 3/n + O(n^{−3})` and is not eventually polynomial (replayed).

**Corollary 8.3 (cubic-rate irrationality).** If strictly increasing positive
integers satisfy `a_n²/a_{n+1} = 1 + 3/n + o(n^{−3})` then `Σ 1/a_n` is irrational.
*Proof.* Rationality gives the canonical orbit with
`C_{n+1}/C_n = a_n²/a_{n+1} + O(1/a_n)` (exact growth-defect identity) and
`1/a_n ≪ n^{−3}`; Lemma 8.2 gives an exact rising-factorial cubic, against
Theorem 8.1. ∎ New; the corpus's rate results live at `λ ≤ 1`
(`critical_boundary_integer_rounding_rigidity`), and the exact-profile exclusions at
degree two. **Derived (this pass, not landed as a row):** the same composition at
`λ = 2` gives `2C_n = A'n(n+1) + 2B` with integers `A', B`; the exact-quadratic
exclusion (`polynomial_profile_rigidity` (A)) covers `A'(n² + n) + 2B` when
`A' ∣ 2B`, and Theorem 7.1's proof (not its statement, which takes `Q ∈ ℤ[X]`)
covers the general rational constant term; so `a_n²/a_{n+1} = 1 + 2/n + o(n^{−2})`
⟹ irrational holds once Theorem 7.1 is restated for monic `Q ∈ ℚ[X]`. The
negative-norm step does **not** transfer verbatim at rational `k = 1/2`. Captured
as a residual, not claimed.

## 9. Corrections and boundary notes on the returns

- r01 §5 uses the weaker centring `w_n < 2u_n`; with the corpus centring
  `2w_n ≤ 3u_n` the protection condition `pP > (3/2)H` holds under `P ≥ R_s + 3`, so
  the Lean form takes `runningMax u s + 3 ≤ p^ℓ`. r01 Theorem 3's freshness count in
  the window `[αL, βL)` uses the budget `#{j < T : ρ_j > 1} ≤ log₂ C_T = o(T)` at
  `T = βL`, which is what makes the window count `(β−α)L − o(L)`; the return states
  "nonfresh indices have density zero", which alone would not control a window at
  index scale `log N`.
- r02's per-step capacity `1 + d_n/(2p)` counts barriers spaced `2p`; the first
  batch's sharp per-jump capacity `⌊(d−1)/2⌋` counts odd multiples of a *single*
  prime at spacing `2` and is a different object; both are correct.
- r03's `J_n = M_n²/G_n` needs `h_n ∣ d_n²` and `d_n ∣ ρ_n`, both exact; the return's
  `|𝓧_N| ≤ log₂ log(3 + κ_N) + B` hides a constant depending on `c` in
  `log a_j ≥ c2^j`.
- r04 Proposition 1 divides the divisibility `bc²u' ∣ bc²(bs² − ee')` by `bc²` as an
  integer statement, never a congruence modulo `u'` where `c` need not be a unit; the
  order of operations is essential and is how the Lean form is stated.
- r05's Theorem 1 upper bound is external (Kovač–Tang Lemma 11); the strictness
  argument and the lower bound are self-contained.
- r06 Theorem 4 needs the moduli coprime to `6` only for the CRT with the residue
  `5 (mod 6)`; fresh multipliers are eventually coprime to `6` because `2`, `3` each
  appear in at most one fresh multiplier.
- r07's uniform density statement is about agreement with a *fixed* polynomial
  template; it neither contradicts nor removes the corpus's structural block on
  prime-modulus forbidden-word densities along the orbit's own residues.
- r08's mod-`7` table is exhaustive over `d_0 ∈ 𝔽_7` with `c_0 ∈ {1, 4}` a unit, so
  `a_0` is determined; the argument lives on the stabilised primitive tail where
  `h = 1`.
- r02 Lemma 2 assumes `τ` is the first crossing of `L`; the Lean theorem shows the
  hypothesis is redundant (each barrier has its own first crossing below `τ`), so the
  inequality holds at every index where `2u_τ ≥ pQ`.
- r04 Proposition 1 carries the next raw-numerator relation `w' + v' = a'u'` and the
  normal form as hypotheses; the saturation `u' ∣ h e e' − v²` needs neither (Lean
  `saturated_square_transport_raw`), and the stated reach of (13) is `b` a
  non-residue, hence `b ≠ 1` and `h ≠ c²`; "`h` not a perfect square" needs the extra
  step   `c² ∣ k² ⟹ c ∣ k`, supplied in Lean.

## 9.5 Type B r2 corrections (2026-09-06)

- **Density.** Theorem 8.1 does not prove a universal lower density `1/28`. The
  Chebotarev/gcd reductions assume lower density zero of exceptions. Supported
  conclusion: positive lower density for each fixed rational cubic profile;
  `1/28` only for `2n(n+1)(n+2)±1`.
- **Global record iff.** Theorem 4.5's global `limsup A_n < ∞ ⇔ (S)` and
  Theorem 2.4's global energy iff are demoted to problems in the paper. Lean
  retains `recordAmplified_error_after_cancellation` and
  `protected_epoch_energy_integer`.
- **Scalar finite mass.** Normalised vanishing is redundant for the product
  bound: `eventually_zero_of_summable_negativeRelativeMass_scalar` in
  `SparseResetRecovery.lean`.
- **Maximal-gap `1/σ`.** Occupied by EightReturnRigidityCriteria.md Proposition 16
  (Fermat witness `σ → 1/2` included). Not a new landing.
- **Degrees 4–6.** `scripts/check_erdos243_higher_degree_certificates.py` replays
  412 Type B certificates exactly. Positive lower density of exceptions per
  listed primitive profile is an ordinary composition; irrationality at rates
  4–6 is **not** claimed (extraction plus certificates not composed into a
  parent-facing rate theorem here).
- **Slow-negative attack.** Type B attacked a compressed short-note paragraph.
  Live `SlowNegativePartRigidity.md` §4 defines poor/rich/burn primes and gives
  an ordinary proof. Not demoted.
- **Sign trichotomy / real windows.** Type B's `res:classicalhalfspace` and
  integer-endpoint window bugs are in the reviewed short note, not in this
  paper. No live-paper repair.
- **Cubic as paper lead.** Rejected as a parent-progress replacement for
  bounded-negative rigidity. Cubic-rate is an additional original-coordinate
  theorem at `λ = 3`.

## 9.6 Type B r4 corrections (2026-09-07)

- **Variable-rise envelope.** The candidate `o(ω(u))` for every unbounded
  nondecreasing `ω` is false even under full coprimality to the prime family.
  Ordinary Theorem A in `VariableRiseCounterexample.md`; not a reciprocal-tail
  counterexample and not a parent theorem.
- **Cubic interface.** `CubicNeighbourIdentity.lean` now checks the
  denominator-cleared ring identities over any commutative ring, and exact
  three-step transport impossibility of the two mod-7 words. Word evaluation is
  not orbit exclusion. Divided `α : ℚ` identities are retained as corollaries.
- **Quadratic `k = 1/2`.** Negative-norm proof transfer to monic `Q ∈ ℚ[X]` is
  withheld; see Theorem 7.1 r4 note.
- **Signed drift identity.** Exact decomposition
  `∑_{j<n} γ_j − log M_n = log U_n − log(q/a_1) − log(1+r_n) + ∑ J(γ_j)`
  separates signed growth, overlap cancellation, and quadratic error. Ordinary;
  not a parent substitute for weighted-record summability.
- **Signed Duverney algebra.** Square-summable `∑η_n² < ∞` specialisation is
  the safe ordinary criterion; Lean checks only the algebraic recurrences and
  cleared telescoping in `SignedDuverneyAlgebra.lean`.
- **Weighted-record residual.** Unchanged: `∃ B: liminf F_B(X)/X = 0` is still
  unproved from the parent hypotheses. Do not fake it.

## 10. Cross-return compositions

1. **Supply.** Lemma 2.3 (odd `Q_n ≥ R_n^A` at every late `n`) discharges the
   `hsupply` hypothesis of both `recordRiseTwo_sylvesterNext_eventually` and
   `recordIncrementOne_sylvesterNext_eventually` at every late index, not merely
   along a subsequence; the Lean consumers keep the supply as a hypothesis because
   its proof uses `log a_n = κ2^n + o(1)` and the freshness budget.
2. **Defect charge on the whole numerator.** Proposition 4.1 with the first batch's
   Theorem 26 gives: a Legendre defect at any odd prime of `u_{n+1}`, including primes
   dividing `G_{n+1}`, forces `h_n` non-square and `h_n ≥ 2`; the defect count below
   `N` stays `≤ log₂ C_N`.
3. **Cancellation lower bounds transferred to the LCM debt.** Theorem 3.1 gives
   `M_N ≥ √G_N`. Hence Theorem 1.4 yields
   `log₂ M_N ≥ ½ (log₂ R_N)^{1 − K − η}` when `K < 1`, and Theorem 6.3 yields
   `M_n ≥ u_n^{2/3 − η}` at infinitely many records when jumps are `≤ 4`. These are
   the first lower bounds on the overlap debt `M_n` charged to record behaviour; they
   live in the coordinates of the weighted LCM record theorem (`U_n = C_n/M_n`), where
   `weighted_lcm_record_summability` remains the equivalent open producer.
4. **Two independent lower bounds on `G` from small record observables.**
   Theorem 1.4 (`K` small ⟹ `G` large) and Theorem 6.3 (jumps `≤ 4` ⟹ `G ≥ u^{4/3}` at
   records) charge the same object, the deletion of protected primes, from two
   observables; Theorem 4.5 charges it to `A_n` instead. All three are lower bounds on
   quantities that normalised vanishing (`log G_n, log R_n = o(n)`) leaves free.
5. **Cubic rate.** Lemma 8.2 composes with Theorem 8.1 into Corollary 8.3, and with
   the quadratic exclusions into the `λ = 2` statement of §8 modulo the restatement
   of Theorem 7.1 over `ℚ[X]`.

## 11. Remaining implication

A counterexample to (H) ⟹ (S) must now satisfy, simultaneously and in primitive
coordinates with arbitrary cancellation:

1. `R_{n+1} − R_n ≥ 2` infinitely often (Theorem 1.5), and `K + Γ ≥ 1`
   (Theorem 1.4);
2. `𝓔 = ∞`, with at least `1/16` of energy in every protected epoch, and
   `Σ_{records}(d_n − 2)_+/√u_n = ∞` (Theorem 2.4);
3. `limsup A_n = ∞`: unbounded record-amplified errors, through unbounded negative
   errors or unbounded drawdown ratios `R_n/u_n` (Theorem 4.5); at the critical rate
   `δ_n = O(1/n)`, `u_n/n` and `(−e_n)_+` are both unbounded (Corollary 4.6);
4. infinitely many record-setting jumps `≥ 5`, or `G_n ≥ u_n^{4/3 − o(1)}` at
   infinitely many records (Corollary 6.4), and then `M_n ≥ u_n^{2/3 − o(1)}` there;
5. `ω(v_N) ≥ N − o(N)`, `P⁺(v_N)/N → ∞`, at most `o(√N)` principal source primes
   ever contact the LCM numerator (Theorems 3.2, 3.3);
6. no agreement with any rational multiple of a monic integer quadratic on more than
   a `3/4` proportion of any long interval; no density-one agreement with any fixed
   rational cubic profile (positive lower density of exceptions per profile; `1/28`
   only for the two primitive words `2n(n+1)(n+2)±1`); and no rate
   `1 + 3/n + o(n^{−3})` (Theorems 7.1, 8.1, Corollary 8.3);
7. together with everything in `EightReturnRigidityCriteria.md` §11.

Every item is a lower bound on a record, cancellation, or profile observable, and
every one is compatible with `log C_n = o(n)` and `e_n/u_n → 0`. The single missing
implication is unchanged: an upper bound, from (H) and the exact denominator
feedback, on any one of these observables. Eventual unit record increments (Lean
core plus the stated supply) remain an exact equivalence with (S). Bounded `A_n`
and finite epoch energy are **proposed** equivalences: the local visibility lemma
and the integer epoch inequality are checked, the global CRT/deletion iteration
and the epoch-series comparison are not. The finite weighted LCM record budget of
`weighted_lcm_record_summability` remains the named equivalent open producer.

## 12. Receipts

Checker `scripts/check_erdos243_weighted_record_octuple.py --quick` (stdlib, exact
arithmetic, one JSON status line), quick run 2026-09-05, all parts `failures: 0`:
part B `21,882` primitive states, `2,479` valuation drops, `2,007` full erasures;
part C `1,108` one-step barrier crossings, `3,000` capacity checks, `27` engineered
epochs; part D the construction for `m = 2..8` and `2,889` sandwich states; part E
`22,583` transport steps (`12,484` paid), `4,123` Lemma 4.2 checks, `192` family
members; part F `50` continuation-family members; part G `1,600` exhaustive cut pairs
and `242` erasure-family members; part H `2,289` identity checks and the norm identity
for `k ≤ 12`; part I the two mod-`7` words, the `d_1` image `{0,2,5,6}`, the sole
integer scale `12`, and the countermodel's ratio error below `2/n³`.

Lean, all `lake env lean` in the private authoring root with axioms `propext`,
`Classical.choice`, `Quot.sound` and no `sorry`: `RecordIncrementBarrier.lean`
(603 lines, 9 theorems, rc `0`, 65 s), `SaturatedSquareTransport.lean` (413 lines,
10 theorems, rc `0`), `TwoModulusRecordCut.lean` (206 lines, 2 theorems, rc `0`),
`ProtectedEpochEnergy.lean` (423 lines, 5 declarations, rc `0`, 46 s). The
authoritative focused build
`scripts/lean_fast_build.py ErdosProblems.Erdos243.{RecordIncrementBarrier,SaturatedSquareTransport,TwoModulusRecordCut,ProtectedEpochEnergy}`
completed with rc `0` ("Build completed successfully", 8251 jobs, 2026-09-05
15:15Z) and the four modules are imported from `ErdosProblems.lean`. The
canonical-v1 cross-check before any public export is still owed (Task Ledger
`cap_quick_wire_build_receipt_and_canonical_v1_chec_a1380f362662`). The
Comparator entry `ExternalVerification243RecordIncrementBarrier` packages
`recordIncrementOne_sylvesterNext_eventually` (Challenge Mathlib-only, Solution
rc `0`).
Desk receipts are in the batch work directory
`public-source-redacted://state/type_b_return_batches/erdos243_20260905_weighted_record_octuple_returns_02/work/`
(`desk_L1_lean_receipt.json`, `desk_L2_lean_receipt.json`,
`desk_L3_lean_receipt.json`); the research packet rows carry the declaration names.
