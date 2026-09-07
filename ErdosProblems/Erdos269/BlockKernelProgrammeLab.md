# The Block-Kernel Programme for Erdős #269

**Proof-layer lab note.** Wave-2 authoring pass (`proof_drafter`), 2026-08-31.
Incorporates the wave-2 adversary-audit and `lambda_structure` correction drops; every
imported claim was re-derived or re-measured here before being written down.

Every claim carries one of four labels:

| Label | Meaning |
|---|---|
| **PROVED-HERE** | Full proof in this document; I derived and checked every step this pass. |
| **PROVED-ON-DISK** | Landed in the repo; locator given and **verified by reading the file this pass**. |
| **VERIFIED-COMPUTATIONALLY** | Exact-arithmetic check only, scale stated. Not a proof. |
| **OPEN** | Not proved anywhere. |

Claims imported from sibling agents that I could not re-derive are marked
**`reported_prior`** and are never used as a premise.

---

## §0. Status and claim ceiling

**Erdős #269 is OPEN.** With `h_0 < h_1 < …` enumerating `H = {2^i3^j5^k}`,
`L_n = lcm(h_0,…,h_n) = H(h_n)`, and

```
S = Σ_{n≥0} 1/L_n = Σ_{h ∈ H} 1/H(h) = 1.80931935238932…
```

whether `S ∈ ℚ` is unresolved. **This document proves no part of that.** It contains:

1. the identity layer with full proofs (§2);
2. the width bound, pinned (§3);
3. the block-exclusion lemma `[P2*]` and its lattice scaffolding, restructured over
   **`P`-classes** rather than cylinders (§4–§5);
4. the `s_j`-chain coordinates for the lattice (§4.7);
5. **two** terminal open statements (§6) — the block programme does *not* reduce #269 to one.

**Claim ceiling.** Nothing here is a parent theorem or a partial result on #269. The
deliverable is a conditional reduction whose hypotheses are two genuinely open statements, one
of which (`B = 1`) the input framing had silently dropped.

### 0.1 Errata found in the input material

> Errata **E12–E15**, found by the wave-8 Type B assimilation against *this document's own*
> §12/§13, are tabled in **§14.0**. Two of them (E12, E13) retire conclusions this document
> previously recorded as settled; read §14 before relying on §12 or §13.

| # | Claim | Verdict | §|
|---|---|---|---|
| **E1** | `A9`: `Σ c_r Q_{a_r} ≠ 0` for `c ≠ 0` | **FALSE.** `b_a Q_a = Q_{a+1}`, so `c = (b_a t, −t)` kills it for every `a,t`; smallest `2Q_0 − Q_1 = 0`. Not used — `(ii)` supersedes it. **Do not state A9.** | §4.9 |
| **E2** | `A6` for "every length-`L` radix word" | Must be **realized** windows: the abstract word `2^L` has `P/8^L = 4^{−L}`. Corrected, with a two-line proof; now a corollary of the `P`-class lemma. | §4.6 |
| **E3** | `m ≥ 3L−4` gives a `{−1,0,1}` collision | **Wrong by ≈ 2⁷.** `3L−4 = log₂(P/2)` for the *lower* A6 bound; pigeonhole needs the *upper*. Correct: **`m ≥ 3L+3`**. | §4.11 |
| **E4** | width: `d_m ≤ (m+2)²` "reconcile `2a²+12a+22` with `a²+6a+11` (factor 2?)" | Not an arithmetic error: **units**. The repo state is the *half*-height `X^rep = X/2`. Both statements true. Pinned constant is much sharper than either. | §1.2, §3 |
| **E5** | `exact_results[56]`: `S = Σ_p (p−1)Σ_m A(p^m)/H(p^m)`, `A(x)=#{2 ≤ s < x}` | **Off by exactly 1**; that sum is `S − 1`. Needs `N(x) = #{1 ≤ s < x}`. The packet's own aside `Σ_p(p−1)Σ_m 1/H(p^m) = 1` is the dropped term. | §2.4 |
| **E6** | block theorem over "every `B` coprime to 30" | `B = 1` makes `(ii)` unsatisfiable ⇒ hypothesis never true ⇒ theorem vacuous. **Two** terminal open statements are needed. | §4.15, §6 |
| **E7** | `(iii*)`'s `W` | Must bound `X`, **not** `Y = 15X`. State as `Σ|c_r|W(a_r+L) < P/B`. Wave-1 used a 15×-conservative width (`reported_prior`) — conservative, not wrong. | §4.13 |
| **E8** | `(I1)` uses `min(Y_a,Z_a)` | **Correct**, but coupled to the coefficients: `(2,4,+8)` goes with `min`, `(10,12,−8)` with `max`. Mixing fails at `a = 1`. | §2.1 |
| **E9** | "`X_1`" in the CF probe | A **third** meaning: `exact_results[47]` defines `X_1 = Σ_{s≥2}1/H(s) = S − 1`, no normalizer. | §1.2 |
| **E10** | "`L ≥ 13`" | A `B = 1`, cylinder-design statement. Under the `P`-class design the constraint dissolves entirely (§5). | §5 |
| **E11** | `s_j`-chain "for members with common window product `P` (`P`-class)" | **FALSE on a `P`-class.** `w_j = P/v_j` with `v_j = Q_{a+j}/Q_a`, which is *not* constant on a `P`-class. Measured: 300/300 on a cylinder, **0/300** on a `P`-class. The `s_j`-chain is a **cylinder** coordinate system. | §4.7 |

`E11` is the one that changes what the next agent should do: the two structural upgrades
(`P`-classes for pool size; `s_j`-chain for lattice coordinates) **cannot be applied
simultaneously**. §4.7 gives the resolution.

---

## §1. Conventions and unit tests

### 1.1 Objects

For real `x ≥ 1`, `H(x) = 2^⌊log₂x⌋ 3^⌊log₃x⌋ 5^⌊log₅x⌋`. For smooth `h`, `H(h)` is the
running lcm, so `L_n = H(h_n)`.

```
B_a = ⌊a θ₃⌋,  θ₃ = log₃2 = 0.6309297535714574…
C_a = ⌊a θ₅⌋,  θ₅ = log₅2 = 0.4306765580733931…
Q_a = H(2^a) = 2^a 3^{B_a} 5^{C_a}
b_a = Q_{a+1}/Q_a = 2·3^{B_{a+1}−B_a}·5^{C_{a+1}−C_a} ∈ {2,6,10,30}
Sh_a = {h ∈ H : 2^a ≤ h < 2^{a+1}},  c_a = #Sh_a
m_a = Σ_{Sh_a} 1/H(h),  d_a = Q_a m_a,  e_a = 15 d_a
X_a = Q_a Σ_{h ≥ 2^a} 1/H(h),   Y_a = 15 X_a
```

`b_a ∈ {2,6,10,30}` because `[2^a,2^{a+1})` holds at most one power of 3 and one of 5.

**Convergence and a free bound.** `H(h) ≥ h` for smooth `h`, so
`S ≤ Σ_{h ∈ H} 1/h = 2·(3/2)·(5/4) = 15/4 = 3.75`. **PROVED-HERE.**

### 1.2 The three "`X`"s — read before importing any number

| Name | Definition | `a = 5` | `a = 200` |
|---|---|---|---|
| **`X_a`** (this document, **full height**) | `H(2^a)·Σ_{h≥2^a}1/H(h)` | `11.29801160923445` | `7192.0723641328` |
| **`X_a^rep`** (repo, Lean, `exact_results[57],[58]`, **half height**) | `(H(2^a)/2)·Σ_{h≥2^a}1/H(h) = X_a/2` | `5.64900580461722` | `3596.0361820664` |
| **`X_1`** (`exact_results[47]`, CF probe) | `Σ_{s ∈ H, s ≥ 2} 1/H(s) = S − 1`, no normalizer | — | `0.80931935238932` |

The half-height row is pinned three ways, all read this pass:
* `research_packet.json → open_producers[0]` states the target verbatim as
  **"the genuine normalized source tail `X_a = H(2^a) T_a / 2`"**;
* `RationalLatticeReduction.lean:196` gives the witness as `p·H(2^a)/2 − q·(cleared prefix)`;
* `DyadicOrderedTailRecurrence.lean:31` reads `(H(2^{a+1})/2)·m_a = dyadicOrderedBlockDigit235 a`.

And numerically: `exact_results[57]`'s two anchors are **exactly half** my full-height values
(**VERIFIED-COMPUTATIONALLY**, exact `Fraction`s, 14 significant figures).

Consequences used below: the repo's `{1,3,5,15}`-weighted ordered digit is
`δ_a := (Q_{a+1}/2)m_a = (b_a/2)d_a = b_a e_a/30`; and any width imported from
`exact_results[58]` must be doubled to enter this document's units.

### 1.3 Recurrences

```
(R1)  X_a = d_a + X_{a+1}/b_a        ⟺   Y_{a+1} = b_a Y_a − b_a e_a
(R2)  Y_{a+L} = P·Y_a − Ê_{a,L},   P = Π_{i<L} b_{a+i} = Q_{a+L}/Q_a,
                                   Ê_{a,L} = Σ_{j<L} e_{a+j} · Π_{i=j}^{L−1} b_{a+i}
```

*Proof.* `(R1)`: `X_a = Q_a m_a + (Q_a/Q_{a+1})X_{a+1}`. `(R2)`: induction on `L`. ∎
**PROVED-HERE**; **VERIFIED-COMPUTATIONALLY** exactly for `a < 100`, `1 ≤ L ≤ 7`, 0 failures.

Note `Π_{i=j}^{L−1}b_{a+i} = Q_{a+L}/Q_{a+j} = P/v_j` with `v_j := Q_{a+j}/Q_a`, so

```
(R2′)  Ê_{a,L} = Σ_{j<L} e_{a+j} · w_j ,     w_j := P/v_j ,   v_j w_j = P .
```

### 1.4 Unit tests (all reproduced exactly this pass)

```
Q_0..Q_4 = 1, 2, 12, 120, 720
e_0..e_7 = 15, 20, 21, 35, 65, 120, 91, 190
b_0..b_7 = 2, 6, 10, 6, 30, 2, 30, 6
c_0..c_12 = 1, 2, 3, 5, 7, 8, 11, 14, 16, 19, 23, 27, 30
X_2 − 6X_1 = −8      X_3 − 10X_2 = −14      Ê′(a,1)|_{a=0..7} = 1,4,7,7,65,8,91,38
```

`e_a` computed two independent ways (definition with exact `Fraction`s; weight decomposition of
§2.0) agrees for `a < 40`.

---

## §2. The identity layer

`N(x) = #{h ∈ H : h < x}` (**strict**, **including `h = 1`**);
`P₃₅(x) = #{(j,k)≥0 : 3^j5^k < x}`; `P₂(x) = #{i≥0 : 2^i < x}`.

### 2.0 Lemma W — the shell weight

> For `h ∈ Sh_a`, with `δ₃ = 1[h ≥ 3^{B_a+1}]`, `δ₅ = 1[h ≥ 5^{C_a+1}]`:
> `⌊log₃h⌋ = B_a+δ₃`, `⌊log₅h⌋ = C_a+δ₅`, hence
> ```
> Q_a/H(h) = 1/w,  w = 3^{δ₃}5^{δ₅} ∈ {1,3,5,15},   15/w = 15 − 10δ₃ − 12δ₅ + 8δ₃δ₅ .
> ```

*Proof.* `h ≥ 2^a ⇒ ⌊log₃h⌋ ≥ B_a`; `3^{B_a+2} > 3·2^a > 2^{a+1} > h ⇒ ⌊log₃h⌋ ≤ B_a+1`;
threshold `3^{B_a+1}` by definition. Same for 5 via `5^{C_a+2} > 5·2^a > 2^{a+1}`.
`⌊log₂h⌋ = a`. The linear form is the four cases `(0,0)↦15, (1,0)↦5, (0,1)↦3, (1,1)↦1`. ∎
**PROVED-HERE.**

Corollaries, all **PROVED-HERE**:

```
(★)   e_a ∈ ℤ,   c_a ≤ e_a ≤ 15 c_a,   i.e.   c_a/15 ≤ d_a ≤ c_a .
(★★)  b_a = 2  ⟺  e_a = 15 c_a .
```

`(★★)`: `b_a = 2` iff neither threshold lies in the shell, iff every `w = 1`. Conversely if
`3 | b_a` then `3^{B_a+1} ∈ (2^a,2^{a+1})` is itself a smooth point of the shell with `δ₃ = 1`,
so some weight exceeds 1. **VERIFIED-COMPUTATIONALLY** (`a ≤ 300`: 62/62 when `b_a = 2`,
**0**/239 otherwise — an exact iff, not a one-way implication).

### 2.1 (I1) — threshold-count form of the digit

`T₃ = min(3^{B_a+1}, 2^{a+1})`, `T₅ = min(5^{C_a+1}, 2^{a+1})`.

> **(I1)** `e_a = N(2^{a+1}) + 2N(T₃) + 4N(T₅) + 8N(min(T₃,T₅)) − 15N(2^a)`.

*Proof.* Lemma W gives
`e_a = 15c_a − 10 A₃ − 12 A₅ + 8 A₃₅` with `A₃ = #{h ∈ Sh_a : δ₃=1}` etc.
Since `3^{B_a+1} > 2^a` always, `A₃ = #{h ∈ H : 3^{B_a+1} ≤ h < 2^{a+1}} = N(2^{a+1}) − N(T₃)`
(both when the threshold is inside the shell and when it is not — the `min` handles it).
Same for `A₅`. `A₃₅` needs `h ≥ max(3^{B_a+1},5^{C_a+1})`, and
`min(max(3^{B_a+1},5^{C_a+1}), 2^{a+1}) = max(T₃,T₅)` by lattice distributivity, so
`A₃₅ = N(2^{a+1}) − N(max(T₃,T₅))`. With `c_a = N(2^{a+1}) − N(2^a)`,

```
e_a = N(2^{a+1}) + 10N(T₃) + 12N(T₅) − 8N(max(T₃,T₅)) − 15N(2^a).      (I1-max)
```
Substituting `N(max) = N(T₃)+N(T₅)−N(min)` (the multiset `{min,max}` *is* `{T₃,T₅}`) turns
`(10,12,−8)` into `(2,4,+8)` with `min`. ∎ **PROVED-HERE.**
**VERIFIED-COMPUTATIONALLY**: both forms `a < 200`, 0 failures; the chimera `(10,12,−8)`-with-`min`
fails at `a = 1` (162/200 failures) — coefficients and anchor are **coupled** (E8).

**Sibling form on disk.** `DyadicBlockThresholdPartition.lean:150` defines
`dyadicOrderedBlockDigit235 a : ℕ` as
`card(Sh_a) + 10·bt₃ + 4·bt₅` if `3^{B_{a+1}} ≤ 5^{C_{a+1}}`, else `card(Sh_a) + 2·bt₃ + 12·bt₅`.
That is `(I1)` for the half-height digit `δ_a = Σ_{Sh_a}(1+2u)(1+4v)` with the same `min`
collapse. **PROVED-ON-DISK** (read this pass).

### 2.2 (I2) — the triple difference

> `Δ₂Δ₃Δ₅ N(x) = 1[x > 1/30]` for all real `x > 0`, where `Δ_pF(x) = F(px) − F(x)`.

*Proof.* `h ↦ 5h` is a bijection `{h<x} → {h<5x, 5|h}`, so `Δ₅N(x) = N_{2,3}(5x)`. Again for 3:
`Δ₃Δ₅N(x) = N_{2,3}(15x) − N_{2,3}(5x) = P₂(15x)`. Again for 2:
`P₂(30x) − P₂(15x) = #{i≥0 : 15x ≤ 2^i < 30x} = 1[30x>1]`, since a ratio-2 half-open interval
holds exactly one power of 2 and it has `i ≥ 0` iff `30x > 1`. ∎ **PROVED-HERE.**
**VERIFIED-COMPUTATIONALLY**: 408 rationals incl. all boundaries, 0 failures.

**Companion, corrected.** `Δ₃Δ₅N(x) = P₂(15x) = max(0, ⌈log₂(15x)⌉)`. The form
`⌊log₂(15x)⌋+1` is valid **only when `15x` is not a power of 2**: at `x = 16/15`,
`P₂(16) = 4` but `⌊log₂16⌋+1 = 5`. **PROVED-HERE** (0 mismatches away from powers of 2).

### 2.3 (I3) — the pair-counter parallelogram

> For `u,v ≥ 0` integers and real `T > 1/15`,
> `P₃₅(3^u5^vT) − P₃₅(3^uT) − P₃₅(5^vT) + P₃₅(T) = uv`.

*Proof.* Let `ψ(z) = #{k≥0 : 5^k < z} = max(0,⌈log₅z⌉)`. The 3-shift bijection gives
`P₃₅(3y) − P₃₅(y) = ψ(3y)`, so `P₃₅(3^uT) − P₃₅(T) = Σ_{i=1}^{u}ψ(3^iT)` and
`LHS = Σ_{i=1}^{u}[ψ(3^i5^vT) − ψ(3^iT)]`. Now `ψ(5^vz) − ψ(z) = v` **iff** `⌈log₅z⌉ ≥ 0`,
i.e. iff `z > 1/5`; with `z = 3^iT`, `i ≥ 1`, that is `T > 1/15`. ∎ **PROVED-HERE.**
The hypothesis is **sharp and strict**: at `T = 1/15`, `u=v=1`, the parallelogram is `0`.
**VERIFIED-COMPUTATIONALLY** (299 admissible triples, 0 failures; boundary confirmed).

### 2.4 (I4) — the prime-power jump expansion

> `S = Σ_{p ∈ {2,3,5}} (p−1) Σ_{m≥1} N(p^m)/H(p^m)`, with `N` **including `h = 1`**.

*Proof.* `H` is non-decreasing on `[1,∞)`, tends to `∞`, and jumps exactly at `q = p^m`, where
`H(q) = p·H(q^-)` (no two such `q` coincide, by unique factorization). Telescoping from `∞`,
`1/H(h) = Σ_{q>h}[1/H(q^-) − 1/H(q)] = Σ_{q>h}(p_q−1)/H(q)`. Summing over smooth `h` and
exchanging (all terms positive) gives `S = Σ_q (p_q−1)N(q)/H(q)`. ∎ **PROVED-HERE**;
**VERIFIED-COMPUTATIONALLY** to 12 significant figures.

> **ERRATUM E5.** `exact_results[56]` writes this with `A(x) = N(x) − 1`. That sum is
> `0.809319352389 = S − 1`. Repair: use `N`, or write
> `S = 1 + Σ_p (p−1)Σ_m A(p^m)/H(p^m)`. The packet's own aside
> *"the landed telescope `Σ_p(p−1)Σ_m 1/H(p^m) = 1`"* is precisely the dropped summand.

### 2.5 (I5) — the Green identity on floor cells

For `v = (a,b,c)`, `A = 2^a, B' = 3^b, C' = 5^c`, `P_v = AB'C'`,
`F(m) = Σ_{h∈H, h≥m}1/H(h)`, `G(v) = P_v F(m_v)`, `E_p` the `+1` shift, `c(v)` the number of
smooth points with floor vector `v`:

> `(2−E₂)(3−E₃)(5−E₅)G = 30 c(v)`, for **either** anchor `m_v = max(A,B',C')` or `min(A,B',C')`.

*Proof.* Expanding, `(2−E₂)(3−E₃)(5−E₅)G(v) = 30 P_v Σ_{ε∈{0,1}³}(−1)^{|ε|}F(m^{(ε)})`.
Write `F(m) = Σ_h 1[h ≥ m]/H(h)`. For `max`, `1[h ≥ max] = Π_p 1[h ≥ ·]`, so the alternating
sum factors as `Π_p(1[h≥p_{low}] − 1[h≥p_{high}]) = 1[h ∈ cell]`. For `min`, use
`1[h≥min] = 1 − Π(1−1[h≥·])`; the constant is killed by `Σ_ε(−1)^{|ε|} = 0` and the product
gives `(−1)³Π_p(α_1−α_0) = 1[h ∈ cell]`. Either way the result is
`30P_v Σ_{h ∈ cell}1/H(h) = 30 c(v)`, since `H ≡ P_v` on the cell. ∎ **PROVED-HERE**;
**VERIFIED-COMPUTATIONALLY** on 270 cells, both anchors, 0 failures.

### 2.6 (DIV), and `Ê ≡ 0 (mod 30)`

Dictionary (unique factorization rules out equality):

```
3 | b_a  ⟺  B_{a+1} = B_a+1  ⟺  3^{B_a+1} < 2^{a+1}
5 | b_a  ⟺  C_{a+1} = C_a+1  ⟺  5^{C_a+1} < 2^{a+1}
```

> **(DIV)** `3 ∤ b_a ⇒ 3 | e_a`, and `5 ∤ b_a ⇒ 5 | e_a`.

*Proof.* `3 ∤ b_a` means `3^{B_a+1} > 2^{a+1}`, so `A₃ = A₃₅ = 0` and by Lemma W
`e_a = 15c_a − 12A₅ ≡ 0 (mod 3)`. Symmetrically `5 ∤ b_a` gives `A₅ = A₃₅ = 0` and
`e_a = 15c_a − 10A₃ ≡ 0 (mod 5)`. ∎ **PROVED-HERE**, two lines.
**VERIFIED-COMPUTATIONALLY**: `a ≤ 800`, hypotheses fire 296 (for 3) and 457 (for 5) times,
0 failures.

**Non-vacuity.** When `3 | b_a`, `3 | e_a` holds in only 37.0% of shells (`a ≤ 300`); for 5,
20.9%. So `(DIV)` is a genuine constraint on a genuine sub-family, not an artifact.
**VERIFIED-COMPUTATIONALLY.**

*Route note.* The input material proposed deriving `(DIV)` from `(I1)` by "relating the
threshold counts". That is a detour: `(DIV)` is a statement about which weights *occur*, one
step upstream of `(I1)`.

**Sharp form.** The two rows combine to `30 | b_a e_a`, i.e. `δ_a := b_a e_a/30 ∈ ℤ` — and
`δ_a` is the repo's `dyadicOrderedBlockDigit235`, an **ℕ-valued definition**
(`DyadicBlockThresholdPartition.lean:150`) proved equal to `(H(2^{a+1})/2)m_a`
(`DyadicOrderedTailRecurrence.lean:31`). So the sharp form is **PROVED-ON-DISK**
(`exact_results[11]`, `lean_checked`).

> **Corollary.** `Ê_{a,L} ≡ 0 (mod 30)`; set `Ê′ = Ê/30`.

*Proof 1.* Fix `j < L`. The term is `e_{a+j}·Π_{i=j}^{L−1}b_{a+i}`; the product is non-empty
and every `b` is even, so `2` divides it. If `3 | b_{a+i}` for some `i ∈ [j,L−1]`, `3` divides
the product; otherwise `3 ∤ b_{a+j}` and `(DIV)` gives `3 | e_{a+j}`. Same for 5. ∎
*Proof 2 (structural).* `Ê′_{a,L} = Σ_{j<L}δ_{a+j}Π_{i=j+1}^{L−1}b_{a+i}`, an integer
combination of the integer digits `δ`. **This is literally the Lean `windowForcing`**
(`RestrictedFloorSum.lean:422`, recursion `windowForcing(len+1) = b(lo+len)·windowForcing(len)+e(lo+len)`)
at `e := dyadicOrderedBlockDigit235`; the same recursion is `rigidityN`
(`IntegralRigidity.lean:33`). So `Ê′ = windowForcing`: cite the disk owner, do not redefine. ∎
**PROVED-HERE** + **PROVED-ON-DISK**; **VERIFIED-COMPUTATIONALLY** `a < 80`, `L ≤ 8`, 0 failures.

### 2.7 Residue variety along returns (context row, not used)

A sibling agent reports: along returns to a fixed cylinder, `{e_{a+L} mod B}` equals
`{r : gcd(B,μ) | r}` with `μ = 3^{[3∤b]}5^{[5∤b]}` of the target letter — i.e. `(DIV)` is the
*only* constraint and is exactly saturated. Reported scale 2274/2780 exact, all mismatches
sample-starved, zero overshoots. `reported_prior`.

My independent spot check (`L = 3` + next letter, `a ≤ 236`, `B ∈ {7,11,49,77}`, 6 largest
cylinders, 24 rows): **0 overshoots**, 4/24 exact, shortfall fully explained by 18–20 returns
having to cover up to 11 residues. **VERIFIED-COMPUTATIONALLY at small scale.**
The containment direction *is* `(DIV)`; the surjectivity direction is unproved and is **not
used anywhere below** — see §8.4(5) for why it could not be used as stated.

---

## §3. Width: pinning the constant

### 3.1 Telescope

`(R1)` iterates to `X_a = Σ_{r≥0} d_{a+r}/P_r` with `P_r = Q_{a+r}/Q_a ≥ 2^r`, absolutely
convergent (`d` polynomial, `P_r ≍ 8^r`). Hence

```
(T)  X_a ≤ Σ_{r≥0} d_{a+r}2^{−r},     Σ 2^{−r} = 2,  Σ r2^{−r} = 2,  Σ r²2^{−r} = 6.
```

### 3.2 Sharp digit bound

> **S1.** `c_a = P₃₅(2^{a+1})`.

*Proof.* For each `(j,k)` with `g = 3^j5^k`, the ratio-2 interval `[2^a/g, 2^{a+1}/g)` holds
exactly one power of 2, and its exponent is `≥ 0` iff `g < 2^{a+1}`. Unique factorization makes
this a bijection onto `Sh_a`. ∎ **PROVED-HERE**; verified `a < 120`, 0 failures.

> **S2.** `P₃₅(x) ≤ (log₃x + 1)(½log₅x + 1)` for `x > 1`.

*Proof.* `P₃₅(x) = Σ_{j=0}^{J}ψ(x/3^j)`, `J = max{j : 3^j<x}`, `ψ(y) ≤ log₅y + 1`. With
`v = log₅x`, `ρ = log₅3`, `n = J+1`, this is `≤ f(n) := n(v+1) − ρn(n−1)/2`, concave with
vertex `n* = log₃x + log₃5 + ½ > log₃x + 1 ≥ n`. So `f` is increasing on the admissible range
and `P₃₅(x) ≤ f(log₃x+1) = (log₃x+1)(v − ρlog₃x/2 + 1) = (log₃x+1)(v/2+1)`, using `ρlog₃x = v`. ∎
**PROVED-HERE.**

> **S3.** `d_a ≤ c_a ≤ α(a+1)² + β(a+1) + 1` with `α = θ₃θ₅/2 = 0.1358633273…`,
> `β = θ₃+θ₅/2 = 0.8462680326…`; rationally, `d_a ≤ (7/50)(a+1)² + (17/20)(a+1) + 1`.

*Proof.* `d_a ≤ c_a` is `(★)`; apply S2 at `x = 2^{a+1}`, where `log₃x = (a+1)θ₃`,
`log₅x = (a+1)θ₅`, `θ₃θ₅/2 = α`, `θ₃+θ₅/2 = β`; then `α < 7/50`, `β < 17/20`. ∎
**PROVED-HERE**; verified `a ≤ 320`, 0 violations.

### 3.3 A12 — the pinned width

> **A12.** For every `a ≥ 0`,
> ```
> X_a ≤ W*(a) := (7/25)a² + (141/50)a + (177/25)  =  0.28a² + 2.82a + 7.08 ,
> ```
> and consequently `X_a ≤ W(a) := a² + 6a + 11` and `X_a ≤ a² + 4a + 6`, and
> `X_a^rep ≤ W*(a)/2`.

*Proof.* Insert S3 into `(T)` with `α' = 7/50`, `β' = 17/20`:

```
X_a ≤ 2α'(a+1)² + (4α'+2β')(a+1) + (6α'+2β'+2) = 0.28(a+1)² + 2.26(a+1) + 4.54
    = 0.28a² + 2.82a + 7.08 .
```
`W*(a) ≤ a²+6a+11` coefficientwise. For `a²+4a+6`: `W*(a) ≤ a²+4a+6 ⟺ 0.72a²+1.18a ≥ 1.08`,
true for `a ≥ 1`; and `X_0 = S ≤ 15/4 = 3.75 < 6` by §1.1. ∎ **PROVED-HERE.**
**VERIFIED-COMPUTATIONALLY**: exact `X_a`, `a ≤ 280`, 0 violations; min slack `5.27` for `W*`,
`4.19` for `a²+4a+6`, `9.19` for `W`. Measured `sup_{20≤a≤280}X_a/(a+1)² = 0.20743` against the
leading coefficient `0.28`, so the proof retains asymptotic slack.

**Working width.** `(iii*)` below is stated with `W(a) = a²+6a+11` **on the `X`-scale**, which
A12 licenses (it is `≈ 3.6×` conservative). Substituting `W*` anywhere `W` appears is legal and
strictly improves every downstream bound — measured effect at `L = 12`: `B_max` rises from
`238546` to `816766` (§5.2), a `3.4×` gain; a sibling reports `156` primes killed vs `39` on the
wave-1 row 0. `reported_prior` for the second figure.

### 3.4 E4 resolved

| Statement | Convention | Status |
|---|---|---|
| `X^rep_a ≤ a²+6a+11` (`exact_results[58]`) | half height | true; status is `exact_checker`, so **VERIFIED-COMPUTATIONALLY**, not proved |
| `X_a ≤ 2a²+12a+22` | full height (`= 2×`) | true; what the crude telescope with `d_m ≤ (m+2)²` gives |
| `X_a ≤ 0.28a²+2.82a+7.08` | full height | **A12**, `≈ 3.6×` sharper, PROVED-HERE |

Both explanations offered for the "factor 2" are correct simultaneously:
**(a) units** — `X^rep = X/2` puts a `½` in front of the whole telescope; and
**(b) indexing** — `Σ_{i≥0}(m+i+1)²2^{−(i+1)} = m²+4m+6` while
`Σ_{i≥0}(m+i+2)²2^{−(i+1)} = m²+6m+11`, the second being the first at `m+1`. With the digit
input `d_m ≤ (m+1)²` (**VERIFIED-COMPUTATIONALLY**, `m ≤ 240`, 0 violations; note `e_m ≤ 15m²`
*fails* at `m = 0`, where `d_0 = 1`), the half-height telescope reads `X^rep_a ≤ a²+4a+6`
counting from shell `a`, and `a²+6a+11` counting from shell `a+1`.

**No statement I found was false.** What was wrong was attribution: `a²+6a+11` is not what
`d_m ≤ (m+2)²` plus the `b ≥ 2` telescope yields in full-height units, and mixing a half-height
`W` with a full-height `X` costs a factor 2 in `(iii*)`.

---

## §4. The lemma chain

*Label note.* `A1, A2, A6, A10` keep the input material's labels. `A3–A5, A7, A8, A11–A15` are
assigned **in this document**; do not assume they match any other numbering. `A9` is retired.

### A1 — half-height integrality
> For smooth `x < 2^a`, `2H(x) | Q_a`; hence `N_a := Q_a Σ_{x∈H, x<2^a}1/H(x) ∈ 2ℤ`.

*Proof.* `x < 2^a ⇒ ⌊log₂x⌋ ≤ a−1`, so `2^{⌊log₂x⌋+1} | 2^a`; monotone floors give
`⌊log₃x⌋ ≤ B_a`, `⌊log₅x⌋ ≤ C_a`. Each `Q_a/H(x)` is therefore an even integer. ∎
**PROVED-HERE**; verified termwise `a < 24`, parity `a ≤ 240`.
This is *why* the repo normalizes by `H(2^a)/2`: the half-height is the exact integrality
normalizer.

### A2 — the exact state identity
> `X_a = Q_a S − N_a`. If `S = A/(MB)` in lowest terms with `M = 2^α3^β5^γ`, `gcd(B,30)=1`,
> then for every `a ≥ a₀(M) := max(α, ⌈βlog₂3⌉, ⌈γlog₂5⌉)` we have `M | Q_a` and `B·X_a ∈ ℤ`.

*Proof.* `X_a = Q_a(S − Σ_{x<2^a}1/H(x))`. `M | Q_a` iff `α ≤ a`, `β ≤ B_a`, `γ ≤ C_a`;
`B_a ≥ β ⟺ 3^β ≤ 2^a ⟺ a ≥ ⌈βlog₂3⌉` (equality impossible); all three are monotone in `a`, so
`M | Q_{a}` for every `a ≥ a₀(M)`. Then `BX_a = (Q_a/M)A − BN_a ∈ ℤ`. ∎ **PROVED-HERE**;
verified against enumerated `N_a` for `a < 26`, 0 failures.

### A3 / A4 — recurrences
`(R1)`, `(R2)`, `(R2′)` of §1.3. **PROVED-HERE.**

### A5 — divisibility
`(DIV)`, `30 | b_a e_a`, `Ê ≡ 0 (30)` — §2.6. **PROVED-HERE** + **PROVED-ON-DISK.**

### A7 — the `P`-class lemma  *(the structural upgrade)*

> **Floor lemma.** For real `x` and `y ≥ 0`, `⌊x+y⌋ − ⌊x⌋ ∈ {⌊y⌋, ⌊y⌋+1}`.

*Proof.* `⌊x+y⌋ = ⌊x⌋ + ⌊{x}+y⌋` and `{x} ∈ [0,1)`, so `⌊y⌋ ≤ ⌊{x}+y⌋ ≤ ⌊y⌋+1`. ∎
**PROVED-HERE**; verified on 20 000 random reals.

> **A7.** For fixed `L`, `P(a) := Q_{a+L}/Q_a = 2^L 3^{u} 5^{v}` with
> `u = ⌊(a+L)θ₃⌋−⌊aθ₃⌋ ∈ {⌊Lθ₃⌋, ⌊Lθ₃⌋+1}` and `v ∈ {⌊Lθ₅⌋, ⌊Lθ₅⌋+1}`.
> **Hence at most 4 values of `P` are realized, for every `L` and every range of `a`.**

*Proof.* Floor lemma at `x = aθ₃`, `y = Lθ₃`, and at `x = aθ₅`, `y = Lθ₅`. ∎ **PROVED-HERE.**
**VERIFIED-COMPUTATIONALLY**: for `L ∈ {1,2,3,5,8,12,20,30,40}` over `a < 2000`, exactly 4
values are realized each time, and the `(u,v)` pairs are exactly the four corners — e.g.
`L = 40`: `⌊Lθ₃⌋ = 25`, `⌊Lθ₅⌋ = 17`, realized `(u,v) ∈ {(25,17),(25,18),(26,17),(26,18)}` with
counts `1179, 346, 369, 106`.

**Why this replaces the cylinder.** `[P2*]` (A13) uses "same radix word" for exactly one
purpose: to make `P` common across the block. A7 says the *`P`-class* — the fibre of `a ↦ P(a)`
— already does that, and there are only 4 of them. Consequences:

* **Pigeonhole is unconditional and trivial.** Among any `n` consecutive starts, some `P`-class
  holds `≥ n/4`. No word-complexity input, no `(L+1)²`, no irrationality of `θ₃,θ₅` needed.
* **Nothing quantifies over abstract words**, so E2's failure mode cannot recur.
* **Pools are 23–142× larger.** Measured over `a < 2000`:
  | `L` | largest `P`-class | largest cylinder | ratio | #cylinders |
  |---|---|---|---|---|
  | 8 | 1053 | 45 | 23.4× | 80 |
  | 12 | 949 | 33 | 28.8× | 156 |
  | 20 | 757 | 17 | 44.5× | 336 |
  | 30 | 1704 | 12 | 142.0× | 577 |
  | 40 | 1179 | 11 | 107.2× | 876 |
* **Members are much earlier**, which is what actually matters for `(iii*)` (§5.2).

Cylinders remain a *sub*-family of `P`-classes, so any cylinder certificate is automatically a
`P`-class certificate. That asymmetry is what makes §4.7 usable.

### A6 — radix mass of a realized window  *(corrected, E2)*

> For every **realized** window (`P = Q_{a+L}/Q_a`), `8^L/15 < P < 15·8^L`, strictly.

*Proof.* By A7, `P = 2^L3^u5^v` with `u − Lθ₃ ∈ (−1,1)`; since `3^{θ₃} = 2`,
`3^u = 2^L·3^{u−Lθ₃} ∈ (2^L/3, 3·2^L)`. Identically `5^v ∈ (2^L/5, 5·2^L)`. Multiply. ∎
**PROVED-HERE.**

> **ERRATUM E2.** "for every length-`L` radix word" is false for *abstract* words: `(2,…,2)`
> gives `P/8^L = 4^{−L}`. Realizability is load-bearing.

**VERIFIED-COMPUTATIONALLY**: `a < 3000`, `L ≤ 44`, `P/8^L ∈ [0.082, 12.168]`. The cap `15` is
nearly attained (`12.17` at `L = 35`), so it cannot be quietly shaved.

### A8 — Sturmian complexity  *(superseded; retained for context)*

The cylinder count is `≤ (L+1)²`: `b_a = 2·3^{s₃(a)}5^{s₅(a)}` with `s₃, s₅` mechanical
sequences of irrational slopes `θ₃, θ₅` (irrational since `θ₃ ∈ ℚ` would give `2^q = 3^p`),
each of factor complexity `L+1`. **PROVED-HERE**; verified realized counts
`4, 9, 16, 36, 80, 193` for `L = 1,2,3,5,8,13` against `(L+1)² = 4,9,16,36,81,196`.

**Two cautions.** (a) The *upper* bound is unconditional; any claim that the count is
*exactly* `(L+1)²`, or that the pair `(s₃,s₅)` equidistributes for product Haar measure, needs
ℚ-independence of `1, θ₃, θ₅` — a four-exponentials-conjecture instance (§7.1), hence
**conditional**. (b) **The `P`-class chain (A7) uses none of this.** Removing A8 from the
critical path removes the only 4EC-adjacent dependency from the block programme.

### A9 — **RETIRED. DO NOT STATE.** *(E1)*

The input claim "`Σ_r c_r Q_{a_r} ≠ 0` for `c ≠ 0`" is **false**: `b_aQ_a = Q_{a+1}` gives the
family `c = (b_a t, −t)` on `(a, a+1)` for every `a, t ≠ 0`; smallest `2Q_0 − Q_1 = 0`.
The true restricted version (`|c_r| ≤ 1` ⇒ nonzero, by `Q_{a+1} ≥ 2Q_a` domination) is not
needed: `(ii)` of A13 already forces `U ≢ 0 (mod B)`, hence `U ≠ 0`. **Do not use A9, and do
not use the domination argument with an unbounded coefficient budget.**

### A10 — the lattice

Fix a block `a_1 < … < a_m` inside one `P`-class (common `P`), `Ê′_r = Ê_{a_r,L}/30`, and

```
Φ : ℤ^m → ℤ/(P/2),  Φ(c) = Σ_r c_r Ê′_r ;  Λ = ker Φ
Ψ : ℤ^m → ℤ/B,      Ψ(c) = Σ_r c_r Q_{a_r}
```

> **A10.** (a) `[ℤ^m:Λ]` divides `P/2` and is 30-smooth.
> (b) If `gcd(B,30)=1` then `Ψ(Λ) = ℤ/B`, so `[Λ : Λ∩kerΨ] = B` exactly.

*Proof.* (a) `ℤ^m/Λ ≅ imΦ ≤ ℤ/(P/2)`, and `P = Πb_i` is 30-smooth. (b) `Q_{a_1}` is a unit mod
`B` (30-smooth, `gcd(B,30)=1`), so `Ψ` is onto. With `κ = [ℤ^m:Λ]`, `gcd(κ,B) = 1` by (a) and
`κv ∈ Λ` for all `v`, so `Ψ(Λ) ⊇ κ·ℤ/B = ℤ/B`. Then `Λ/(Λ∩kerΨ) ≅ ℤ/B`. ∎ **PROVED-HERE.**
**VERIFIED-COMPUTATIONALLY** on a realized block (`L = 3`, `m = 12`, `P = 360`):
`gcd(Ê′_r, P/2) = 1` so `[ℤ^m:Λ] = 180`, 30-smooth; every `Q_{a_r}` a unit mod `B` for
`B ∈ {7,11,101,7919}`.

### A11 — pigeonhole threshold  *(corrected, E3)*

> If `2^m > P/2` then some `c ∈ {−1,0,1}^m \{0}` lies in `Λ`. By A6, `m ≥ 3L+3` suffices.

*Proof.* The `2^m` subset sums `Σ_{i∈T}Ê′_i mod (P/2)` cannot be distinct; a colliding
difference is the vector. `P < 15·8^L ⇒ P/2 < 7.5·8^L < 2^{3L+3}`. ∎ **PROVED-HERE.**

> **ERRATUM E3.** "`m ≥ 3L−4`" is `log₂(P/2)` computed with the **lower** A6 bound
> (`3L − log₂30 = 3L − 4.907`); the pigeonhole needs the **upper** one. The gap is `≈ 2⁷`.
> Even a purely data-driven threshold is `3L+3`: the worst realized word up to `L = 44` has
> `P/8^L = 12.17`, requiring `m ≥ 3L + 2.61`.

### A12 — width
§3.3. **PROVED-HERE.**

### A13 — `[P2*]`, the block-exclusion lemma  *(bookkeeping settled, E7)*

> **A13.** Let `S = A/(MB)` in lowest terms, `M = 2^α3^β5^γ`, `gcd(B,30)=1`, `B ≥ 1`.
> Let `a_1 < … < a_m` share a common window product `P` (a `P`-class block — a cylinder block
> is a special case), with `a_1 ≥ a₀(M)`, and let `c ∈ ℤ^m` satisfy
>
> * **(i\*)** `Σ_r c_r Ê′_r ≡ 0 (mod P/2)`;
> * **(ii)** `Σ_r c_r Q_{a_r} ≢ 0 (mod B)`;
> * **(iii\*)** `Σ_r |c_r| · W(a_r+L) < P/B`, with `W` bounding **`X`** (A12), indexed at the
>   **window end** `a_r + L`.
>
> Then `S ≠ A/(MB)`.

*Proof, with every 15 written out.* Put `V = Σ_r c_r Y_{a_r+L}`, `U = Σ_r c_r Q_{a_r}`.

**Step 1 (transport).** A4 gives `Y_{a_r+L} = P Y_{a_r} − Ê_r`, so
`V = P Σ_r c_r Y_{a_r} − Σ_r c_r Ê_r`. By A5, `Ê_r = 30Ê′_r`, so `(i*)` yields
`Σ_r c_r Ê_r = 30·(P/2)·k = 15Pk` for some `k ∈ ℤ`. (This is *equivalent* to
`Σ_r c_r Ê_r ∈ 15Pℤ`; the modulus `P/2` rather than `P` is exactly what matches the `15ℤ`
lattice in Step 2, and is optimal.) Dividing by `P`:
`V/P = Σ_r c_r Y_{a_r} − 15k`.

**Step 2 (state identity).** `Y_a = 15X_a = 15(Q_aS − N_a)` by A2, so
`Σ_r c_r Y_{a_r} = 15US − 15Σ_r c_r N_{a_r}`. Hence, with `T := Σ_r c_r N_{a_r} + k ∈ ℤ`,

```
(♦)   15 U S − V/P = 15 T  ∈ 15ℤ .
```

**Step 3 (size — `W` bounds `X`, not `Y`).**
`|V| ≤ Σ_r |c_r||Y_{a_r+L}| = 15 Σ_r |c_r| X_{a_r+L} ≤ 15 Σ_r |c_r| W(a_r+L)`, so `(iii*)`
gives `|V/P| < 15/B`. **The two 15s cancel:** dividing `(♦)` by 15,

```
|U S − T| < 1/B .
```

**Step 4 (arithmetic).** `a_r ≥ a₀(M)` gives `M | Q_{a_r}` (A2), so `M | U`; write `U = MU′`.
Then `US = U′A/B` and `US − T = (U′A − TB)/B` with `U′A − TB ∈ ℤ`. If `U′A ≠ TB` then
`|US − T| ≥ 1/B`, contradicting Step 3. So `U′A = TB`, hence `B | U′A`, hence `B | U′` since
`gcd(A,B) = 1` (from `gcd(A,MB)=1`), hence `B | MU′ = U`. This contradicts `(ii)`. ∎
**PROVED-HERE.**

**What the bookkeeping settles.**
* `(iii*)` **must** use a `W` bounding `X`. A `W` bounding `Y` makes the budget 15× too
  generous and the lemma false as proved. Writing it as the integer inequality
  `B·Σ|c_r|W(a_r+L) < P` removes all ambiguity.
* `W(a) = a²+6a+11` **is** valid on the `X`-scale — A12 proves a bound `3.6×` smaller. A
  sibling reports the wave-1 instances clear `(iii*)` with slack `1.37×` and `1.42×`, and that
  a missing 15 would have failed by `≈ 11×`; so the instances themselves pin the normalization.
  `reported_prior` (I did not re-run those instances), but consistent with Step 3 as proved.
* `A9` is not invoked (E1). `U ≠ 0` is free from `(ii)`.
* Only `M | Q_{a_1}` and `gcd(A,B) = 1` are used, so `B` must be the coprime-to-30 part of the
  **reduced** denominator.

**Corollary (a check that needs no `(i*)`).** For any `c` on a common-`P` block,

```
U·S − (V + Σ_r c_r Ê_r)/(15P) = Σ_r c_r N_{a_r} ∈ 2ℤ ,
```
by Step 1 with the `Ê` term restored, Step 2, and `N_a ∈ 2ℤ` (A1). This single identity
validates transport, the `Ê` bookkeeping, the 15-scaling, and A1 simultaneously.
**VERIFIED-COMPUTATIONALLY** here on a `P`-class block (`L = 4`, `m = 9`, 200 random
`c ∈ {−2,…,2}^9`, exact `Fraction`s, 0 failures); reported by a sibling at 2000+ digits on both
wave-1 instances.

**End-to-end unit test of the full chain** (exact `Fraction`s, `L = 3`, cylinder `(6,10,6)`,
`P = 360`, `m = 12`, members `{1,12,15,17,26,31,36,45,47,50,61,64}`, pigeonhole vector
`c = (1,1,0,−1,−1,1,0,0,0,0,0,0)`):

```
Σ c_r Ê_r  = 21600 = 15·360·4        ⇒ k = 4                     (integer ✓)
U = 3046657644556502566233600002
T = 5512376636400931365889330596                                  (integer ✓)
15·U·S − V/P = 82685649546013970488339958940 = 15·T               (EXACT ✓)
|V/P| = 0.153984…     |U S − T| = 0.010266…
```
`(iii*)` fails at this toy scale (`Σ|c_r|W(a_r+L) = 1061.7` vs `P = 360`) — and correspondingly
no contradiction appears: at `B = 101`, `|US − T| = 0.010266 > 1/101 = 0.009901`. The algebraic
core `(♦)` is exact; `(iii*)` is the *only* inequality in the lemma and the only reason `L` must
be large. **VERIFIED-COMPUTATIONALLY.**

### A14 — the `J`-lemma  *(finiteness hypothesis added)*

Fix `β > 0`. Let `Adm_β = {c ∈ Λ : Σ_r|c_r|W(a_r+L) < β}` and `Λ_β = ⟨Adm_β⟩`, the **subgroup
generated by** `Adm_β` — `Adm_β` is not itself closed under addition, and this matters.

> **A14.** Suppose `gcd(B,30)=1`, `B ≥ 2`, `β ≤ P/B`, `J := [Λ : Λ_β] < ∞`, and `B ∤ J`.
> Then some `c ∈ Adm_β` satisfies `(i*)`, `(ii)`, `(iii*)`.

*Proof.* If every `c ∈ Adm_β` had `Ψ(c) = 0`, then `Adm_β ⊆ Λ∩kerΨ`, and since the latter is a
subgroup, `Λ_β ⊆ Λ∩kerΨ ⊆ Λ`; with `J` finite this forces `B = [Λ:Λ∩kerΨ]` to divide
`[Λ:Λ_β] = J` (A10b), contradiction. So some `c ∈ Adm_β` has `Ψ(c) ≠ 0`, i.e. `(ii)`; `(i*)`
because `c ∈ Λ`; `(iii*)` because `Σ|c_r|W < β ≤ P/B`. ∎ **PROVED-HERE.**

Three things the input statement elided:
* **`J < ∞` is a real hypothesis.** `Λ_β` can fail to have full rank — e.g. if every admissible
  vector happened to lie in `{U(c) = 0}`. The hypothesis-free version is the subgroup form
  `Λ_β ⊄ Λ∩kerΨ`.
* **`B ≥ 2`.** At `B = 1`, `kerΨ = Λ` and `(ii)` is unsatisfiable. See E6.
* **Certification is one-sided.** An exact LLL (or MITM) basis of `Λ` all of whose vectors lie
  within budget certifies **both** `J = 1` and finiteness. Any search that fails returns a
  subgroup `Λ' ⊆ Λ_β`, so the computed index is a **multiple** of `J`. Report such an outcome
  as **"not certified `J = 1`"**, never as "`J > 1`".

### A15 — the block theorem  *(quantifier repaired, E6)*

> **A15.** Suppose that for **every `B ≥ 7` with `gcd(B,30)=1`** and every `A₀` there is a
> `P`-class block with `a_1 ≥ A₀` and a `c ≠ 0` satisfying `(i*)`, `(ii)`, `(iii*)`.
> Then `S` is not a rational whose reduced denominator has a non-trivial part coprime to 30.

*Proof.* If `S = A/(MB)` reduced with `M` 30-smooth and `B ≥ 7`, take `A₀ = a₀(M)`; the
hypothesis supplies a block and a `c`; A13 gives a contradiction. ∎ **PROVED-HERE.**

> **ERRATUM E6.** The input quantified over "every `B` coprime to 30", which includes `B = 1`,
> where `(ii)` reads `U ≢ 0 (mod 1)` and is unsatisfiable. The hypothesis is then never true and
> the implication, though formally valid, is vacuous. **A15 does not prove irrationality even if
> its hypothesis is granted.** The `B = 1` branch is separate and open — §6.2.

### 4.7 The `s_j`-chain — cylinder coordinates for `Λ`  *(E11: not `P`-class)*

Suppose the block lies in one **cylinder** (common radix *word*), so that `v_j = Q_{a+j}/Q_a`
and `w_j = P/v_j` are the same for every member. Put `s_j := Σ_r c_r e_{a_r+j}` for `j < L`.
Then by `(R2′)`,

```
Σ_r c_r Ê_r = Σ_{j<L} s_j w_j ,   so   c ∈ Λ  ⟺  Σ_{j<L} s_j w_j ≡ 0  (mod 15P).
```
**PROVED-HERE.** **VERIFIED-COMPUTATIONALLY**: 300/300 on a cylinder block (`L = 6`, `m = 10`,
`c ∈ {−2,…,2}^{10}`).

> **ERRATUM E11 — this is a cylinder statement, not a `P`-class statement.** On a `P`-class,
> `P` is common but `v_j` is **not** (only `v_L = P` is), so `w_j` varies with the member and
> the identity fails. Measured on the largest `L = 6` `P`-class (`P = 648000`, `m = 10`):
> **0/300**. The two structural upgrades therefore pull in opposite directions.

**Structure the coordinates reveal.** All **PROVED-HERE** from the display above:
* `s_j` enters only **modulo `15v_j`** (changing `s_j` by `15v_j` changes `s_jw_j` by `15P`).
* Termwise `s_j ≡ 0 (mod 15v_j)` for all `j` is **sufficient** for `c ∈ Λ`.
* **The modulus ladder outruns any budget.** `|s_j| ≤ Σ_r|c_r|·max_r e_{a_r+j}` is polynomial in
  `a` and `m`, while `15v_j ≥ 15·2^j` (in fact `≍ 15·8^j`). So beyond some `j₀`, `|s_j| < 15v_j`
  and the congruence forces `s_j = 0` **exactly**. Measured (`L = 20`, `a₀ = 100`, `m = 63`,
  crude `|s_j|` bound): forced from `j = 10` onward — i.e. `j₀ ≈ L/2`.

**Consequence (the shape a proof of §6.1 will probably take).** For budget-bounded `c` the
membership condition splits into

1. **low `j < j₀`:** finitely many congruences with small moduli `15v_j`;
2. **high `j ≥ j₀`:** `c` must lie in the **exact integer kernel** of the `(L−j₀)×m` matrix
   `(e_{a_r+j})_{j≥j₀, r}`.

Part 2 is Siegel-lemma-shaped and needs only `m ≳ cL` members. A sibling reports `m = 3L+4`
sufficing in 44/44 measured blocks, all `J = 1`; `reported_prior`. Note the generic Siegel bound
(`R ≈ L` equations, `m ≈ 3L`, entries `≲ (mH)^{R/(m−R)} ≈ (mH)^{1/2}`) is far too weak to give
`±1` vectors, so the empirical `J = 1` is *not* explained by Siegel — that gap is where the
terminal statement lives.

**Methodology warning (recorded, `reported_prior`).** Floating-point-GSO LLL fails silently at
`L ≥ 10`: an exact meet-in-the-middle search found all-`±1` generators of `ℓ¹` norm `≤ 10` where
float LLL was off by `3700×`. **`J` certification must be exact-arithmetic.**

---

## §5. Parameter regime

Given `L`, `B`, and a floor `A₀`:

1. **Pool.** Among `a ∈ [A₀, A₀+n)`, A7 gives a `P`-class with `≥ n/4` members —
   **unconditional, no word complexity, no equidistribution**. Taking `m` members costs
   `n = 4m`, so `a_m < A₀ + 4m`.
2. **`(i*)`** by A11 as soon as `m ≥ 3L+3`.
3. **`(iii*)`** for the resulting `{−1,0,1}` vector: `Σ|c_r| ≤ m` and `W(a_r+L) ≤ W(A₀+4m+L)`,
   so it suffices (via `P > 8^L/15`, A6) that
   ```
   15 · B · m · W(A₀ + 4m + L) < 8^L ,       m = 3L+3 .
   ```
4. **`(ii)`** is delivered by nothing above. That is the terminal statement.

**E10 dissolved.** The cylinder design needed `N ≍ 8^{L/3}(L+1)^{2/3}(15κB)^{−1/3}` with
`m = N/(L+1)²`, forcing `L ≥ L₀(B)` with `L₀(1) = 13` and `L₀(B) ≈ 13 + (log₂B)/3`; and its
`(iii*)` was **knife-edge** — with `N³ = 8^L(L+1)²/(15κB)` the `ℓ¹` budget divided by `m` is
*exactly* 1, so "(iii\*) automatic" was arranged, not free (measured: budget `45.7` vs `m = 45`).
The `P`-class design has no such constraint; step 3 is a plain inequality in `L`.

### 5.1 The `P`-class threshold table

Least `L` satisfying step 3, computed exactly:

| `A₀ \ B` | 1 | 7 | 101 | 10⁶ | 10³⁰ |
|---|---|---|---|---|---|
| 10 | 8 | 9 | 11 | 15 | 43 |
| 100 | 9 | 10 | 11 | 16 | 44 |
| 10⁴ | 12 | 13 | 15 | 19 | 46 |
| 10⁶ | 17 | 18 | 19 | 24 | 51 |

with `W(a) = a²+6a+11`; substituting the pinned `W*` of A12 lowers each entry by 0–1
(e.g. `A₀ = 10, B = 1`: `8 → 7`). Asymptotically `L ≈ (2log₂A₀ + log₂B)/3 + O(log L)`.
**VERIFIED-COMPUTATIONALLY.**

**Everything in §5 steps 1–3 is delivered unconditionally**: for every `L` at or above the
table entry and every `A₀`, the construction produces a `P`-class block with members `≥ A₀` and
a `c ∈ {−1,0,1}^m\{0}` satisfying `(i*)` and `(iii*)`. It says nothing about `(ii)`.
**PROVED-HERE** (A6 + A7 + A11 + A12).

### 5.2 What the `P`-class upgrade buys, measured

At `L = 12`, `m = 3L+3 = 39` members drawn from `a ≥ 1`, `B_max := P/(m·W(a_m+L))`:

| pool | `P` | members | pool size | `B_max` (`W`) | `B_max` (`W*`) |
|---|---|---|---|---|---|
| **`P`-class** | `83 980 800 000` | `a ∈ [1, 80]` | 2846 | **238 546** | **816 766** |
| cylinder | `419 904 000 000` | `a ∈ [23, 2345]` | 91 | 1 933 | 6 892 |

A **123×** gain, despite the cylinder having the larger `P`. The driver is not `P` — it is that
the `P`-class supplies 39 members inside `a ≤ 80` while the cylinder needs `a ≤ 2345`, and
`W(a_m+L)` is `≈ 800×` larger there. **VERIFIED-COMPUTATIONALLY.** (A sibling reports
`4 199 291` vs `395 555` on a differently-chosen block; same direction, `reported_prior`.)

---

## §6. The two terminal open statements

The block programme reduces #269 to **two** open statements, not one. Writing it as one is the
quantifier break E6.

### 6.1 `A16` — the `B > 1` branch  **(OPEN)**

> **A16.** For every `B ≥ 7` with `gcd(B,30)=1` and every `A₀`, there exist `L` and a `P`-class
> block `a_1 < … < a_m` with `a_1 ≥ A₀` such that, with `β = P/B`,
> `Λ_β = ⟨{c ∈ Λ : Σ|c_r|W(a_r+L) < β}⟩` has finite index `J` in `Λ` with `B ∤ J`.
> (Strongest concrete form: `J = 1`.)

`A16 ⇒` A15's hypothesis (via A14) `⇒ S ∉ {A/(MB) : B ≥ 7}` (via A13). **PROVED-HERE.**

**What one `J = 1` block certifies, exactly.** For that `B`, for **every** numerator `A`, and
for **every** 30-smooth `M` with `a₀(M) ≤ a_1` — i.e. exactly `M | Q_{a_1}`, where
`a₀(2^α3^β5^γ) = max(α, ⌈1.585β⌉, ⌈2.322γ⌉)`. Three caveats, all load-bearing:

* **The `M | Q_{a_1}` caveat.** One block reaches only the 30-smooth denominators below its
  floor. Covering all `M` is precisely why "cofinally many blocks" appears: one block **per**
  `A₀`, not one block full stop.
* **`β` depends on `B`.** `β = P/B` shrinks as `B` grows, so `Λ_β` shrinks and `J` can only
  grow. There is **no** `B`-uniform statement; the quantifier order is `∀B ∀A₀ ∃block`, never
  `∃block ∀B`.
* **`J > 1` is not a datum.** See A14's third bullet: any search returns a multiple of `J`.

**Why it is hard, honestly.** `(i*)` is a congruence mod the 30-smooth `P/2`, identical for all
members; `(ii)` is a condition mod `B`, coprime to 30, hence decoupled by CRT — A10 says the two
are independent homomorphisms with `Ψ(Λ)` full. So there is **no arithmetic obstruction**. What
is missing is a **size** statement: that the `Λ`-vectors witnessing the `B`-fibres can be taken
short in the `W`-weighted `ℓ¹` norm. That is a successive-minima question about
`Λ = ker(c ↦ Σc_rÊ′_r mod P/2)` with `m ≈ 3L` and `[ℤ^m:Λ] ≈ 8^L ≈ 2^m` — unit-ish determinant
per dimension, where nothing generic applies and the `Ê′_r` are the actual structured
window-forcing values. §4.7 is the best available coordinate system for attacking it.

### 6.2 The `B = 1` branch — cofinal escape certificates  **(OPEN)**

If `S = A/M` with `M` 30-smooth, then for every `a ≥ a₀(M)`, `X_a = (Q_a/M)A − N_a ∈ ℤ`, and
`X_a > 0`. So it suffices to exhibit **one** `A ≥ a₀(M)` with `X_A ∉ ℤ`.

**Single-`A` certificates exist and are unconditional.** `X_A = n` determines the entire forward
orbit through `(R1)`; every candidate `n ∈ (0, W(A)] ∩ ℤ` can be refuted by forward transport,
because a wrong start's deviation is amplified by `Π b ≥ 2^j` while the admissible window only
grows quadratically. **VERIFIED-COMPUTATIONALLY here**: for `A = 5, 10, 20, 40, 60`, all
`66 / 171 / 531 / 1851 / 3971` integer candidates are refuted, at maximum forward depth `3–5`.

> **The `B = 1` terminal statement (OPEN).** For every `A₀` there exists `A ≥ A₀` admitting such
> a certificate.

This is exactly the repo's priority-1 producer, `open_producers[0]`,
`exclude_exact_integral_dyadic_tails` — whose statement names the target verbatim as
"the genuine normalized source tail `X_a = H(2^a)T_a/2`" and records that the exact `a = 2295`
source word kills every uniform three-transition post-clear proof
(`exact_results[42]`), and that exact left-null certificates kill every phase-conditioned source
potential of degree `≤ 2` (`exact_results[43]`, `[44]`). The dichotomy and transport are
Lean-checked (`BoundedRadixTailEscape.lean`: `boundedRadix_zero_or_cofinal_far`,
`rational_of_scaledTail_integer`, `exact_results[33]`, `[34]`); the structurally matching
consumer is `no_positive_reducedCarry_of_cofinalLocalWindowEscape`
(`RestrictedFloorSum.lean:646`), whose producer `CofinalLocalWindowEscape` (`:629`) is a named
`Prop`, deliberately **not** a theorem. **PROVED-ON-DISK** for the consumer; **OPEN** for the
producer.

**Empirical status, stated with its ceiling.** A sibling reports a coverage of `A ≤ 50000` by
640 000 certificates, with mean escape depth `≈ ⅓ + ⅔log₂A`, geometric excess, and zero
failures; `reported_prior`. **I could not confirm the `A ≤ 50000` figure**: the packet's
640 000-certificate rectangle (`exact_results[49]`) is a *different* object — 32 odd
denominators `q ≤ 120` coprime to 30 against starts `a ≤ 20 000` — so the two "640k"s may be
the same census described twice. Treat the coverage bound as unverified pending a locator.
Either way the census is finite and the cofinal statement is open; `exact_results[49]` itself
records that a later 181-digit-denominator witness stays trapped for 200 post-clear steps,
refuting every uniform escape cap through 199.

### 6.3 The honest headline

```
A16  ⇒  S has no rational value with a non-30-smooth denominator.
A16  +  the B=1 cofinal certificate family   ⇒   S is irrational.
```
Neither hypothesis is proved. The second has an empirically perfect law and no proof; the first
has no obstruction and no proof.

---

## §7. Retired routes, and the conditional layer

### 7.1 `[P1′]` — the synchronization lemma, and four exponentials

The older single-window arguments wanted Weyl equidistribution of
`a ↦ ({aθ₃},{aθ₅}) ∈ 𝕋²`, which needs `1, θ₃, θ₅` ℚ-linearly independent. **That independence
is not unconditional.** A relation `p + qθ₃ + rθ₅ = 0` clears to

```
p·ln3·ln5 + q·ln2·ln5 + r·ln2·ln3 = 0 ,   i.e.   ln(3^p 2^q)·ln5 − ln(2^{−r})·ln3 = 0 ,
```

which is precisely the vanishing of the `2×2` determinant
`det [[ln(3^p2^q), ln3], [ln(2^{−r}), ln5]]` of logarithms of algebraic numbers — an instance of
the **four exponentials conjecture**. What is available does not reach it: the proved six
exponentials theorem gives only rank `≥ 2` of a `3×2` log array, which does not forbid a single
vanishing `2×2` minor; and Baker's theorem concerns linear forms in logarithms, while this is
quadratic. **OPEN.**

* **Two-term cases are elementary.** `q = 0` gives `5^p = 2^{−r}` so `p = r = 0`; `r = 0` and
  `p = 0` reduce likewise to unique factorization. **PROVED-HERE.**
* **`[P1′]`'s repair** replaces the Weyl step by minimality on the orbit closure (a closed
  subgroup coset in either case) — cited to Walters, *An Introduction to Ergodic Theory*,
  Thm 6.20; audited as airtight. `reported_prior` for the citation, which I did not check.
* **The block chain of §4–§6 uses none of it.** A7 replaced A8, so the only 4EC-adjacent
  dependency (exact Sturmian complexity / product Haar) is off the critical path. This is worth
  saying out loud whenever the route is described.

### 7.2 Retired-route table

One line each, with the locator I read this pass. All are *mechanism eliminations*: they close
a strategy, not the problem.

| Route | Why retired | Locator |
|---|---|---|
| Single-window escape (uniform depth cap) | Superseded: an exact 181-digit-denominator affine-cylinder witness stays trapped 200 post-clear steps, refuting every uniform cap through 199. | `exact_results[49]`, `[38]` |
| Denominator-one three-transition rule | Exact `a = 2295` delay-four source word: four canonical states stay under cap, only the fifth escapes. | `exact_results[42]` |
| Metric / statistical (equidistribution of `{X_a}`) | Orbit is Dirichlet-exact-generic: 13 109 certified partial quotients, Gauss–Kuzmin on target, exponent 2.005, largest p.q. 129 114 — no automatic/algebraic CF structure; equidistribution is measured, not derivable. | `exact_results[47]`, `[59]` |
| Stammering / Adamczewski–Bugeaud | Period must serve both Sturmian slopes at once ⇒ needs simultaneous exponent 1; Dirichlet in dim 2 caps at 1/2. Measured exponents decay like `1+O(q^{−1/2})`. | `exact_results[46]` |
| Same-start projective coherence | Same-start pairs are **always** coherent (`P = 1.0000` at every tested `B`); different-start coherence is short-range only. | `exact_results[50]`, `[21]`, `[22]` |
| Finite-observer / rank collapse | Function-faithful observers into finite dimension force finite realised range; the literal kernel has nonsingular minors of every order. | `exact_results[28]` |
| Source-linear coboundary (36 params) | Inconsistent at equation 27 (rank 26 vs augmented 27), primitive integer left-null certificate. | `exact_results[43]` |
| Source-quadratic coboundary (180 params) | Rank 115 vs augmented 116 on 116 equations; 788-bit left-null vector. | `exact_results[44]` |
| Farey-band monotone occupancy | Occupied↔empty polarity flips at depths 16/24/50 vs 32/40/64/80 with all cylinders exactly nested. | `exact_results[40]` |
| Naive weighted transport | Carries do not splice across windows; jump-set density too high. The `a^{−1/2}` density figure is `reported_prior` — I could not pin it to a single verified packet statement. | `exact_results[25]`, `[26]` |

---

## §8. Traps, reproduction, soft spots

### 8.1 Trap list

1. **`X` vs `X^rep` vs `X_1`** (§1.2). `X^rep = X/2`. Double anything imported from
   `exact_results[57]`/`[58]` or the Lean. `η = {Y_a}` is a fourth object, in the
   equidistribution measurements only.
2. **`Ê` vs `Ê′`.** `Ê′ = Ê/30 =` the Lean `windowForcing`. `(i*)` is `Ê′ mod P/2`; for `Ê` it
   reads `Σc_rÊ_r ≡ 0 (mod 15P)`. Dropping the `30` or the `/2` changes the lattice index by a
   30-smooth factor and silently changes `J`.
3. **`e` vs `δ`.** `e_a = 15d_a` (full height); `δ_a = b_ae_a/30` (half height, the Lean digit,
   integer *by definition*).
4. **`N` vs `A`.** `N` includes `h = 1`; `(I4)` needs `N` (E5).
5. **`(I1)`'s anchor and coefficients are coupled**: `(2,4,+8)`↔`min`, `(10,12,−8)`↔`max`.
6. **`(I3)` needs `T > 1/15`, strictly**, and it is sharp.
7. **`⌊log₂(15x)⌋+1` vs `⌈log₂(15x)⌉`** differ exactly at powers of 2.
8. **A6 needs "realized"** (E2), and the cap 15 is nearly attained (12.17).
9. **`(iii*)`'s `W` bounds `X`, not `Y`**, and is indexed at the window end `a_r+L` (E7).
10. **The `s_j`-chain needs a cylinder, not a `P`-class** (E11).
11. **`J` certification must be exact-arithmetic** — float LLL fails silently at `L ≥ 10`.
12. **Never write "`J > 1`"** — write "not certified `J = 1`".

### 8.2 Reproduction

All computations exact (Python `int`/`Fraction`; floats only in reported decimals and in the
real-exponent threshold tables). Scripts in `.../scratchpad/wave2_proof_drafter/`:

| script | contents |
|---|---|
| `core.py` | `H, Q, b, shells, e, d, N, P₃₅, P₂`; two independent `e_a` routes |
| `check1.py` | unit tests; `(I1)` three variants; `c_a = P₃₅(2^{a+1})`; `(DIV)` to `a ≤ 800`; `Ê ≡ 0 (30)` |
| `check2_width.py` | digit bounds; width candidates vs exact `X_a` to `a ≤ 280`; telescope constants |
| `check3_ids.py` | `(I2)`, the `Δ₃Δ₅` companion, `(I3)` incl. sharpness, `(I4)` both counters, `(I5)` 270 cells, A6, A1, A9 counterexample, Sturmian complexity |
| `check4_chain.py` | convention reconciliation vs `exact_results[57]`; `(R2)`; `N_a` parity; `max P/8^L`; cylinder `L₀(B)`; `ℓ¹` budget; lattice index |
| `check5_endtoend.py` | per-shell digit bounds; the exact `[P2*]` end-to-end instance; A10 on a realized block; residue-variety spot check |
| `check6_pclass.py` | A7 (4 realized `P`); pool ratios; floor lemma; **`s_j` cylinder-vs-`P`-class**; `(★★)`; DIV non-vacuity; the `2ℤ` invariant; `B = 1` certificates |
| `check7_regime.py` | `P`-class `B_max` demo; `P`-class threshold table; `s_j` modulus ladder |

### 8.3 Scale of every computational claim

| claim | scale | result |
|---|---|---|
| `(I1)` both forms | `a < 200` | 0 failures (chimera fails 162/200) |
| `c_a = P₃₅(2^{a+1})` | `a < 120` | 0 failures |
| `(DIV)` | `a ≤ 800`, 296+457 firings | 0 failures |
| DIV non-vacuity | `a ≤ 300` | `3\|b_a ⇒ 3\|e_a` only 37.0%; for 5, 20.9% |
| `(★★)` `b_a=2 ⟺ e_a=15c_a` | `a ≤ 300` | 62/62 and 0/239 |
| `Ê ≡ 0 (30)` | `a < 80`, `L ≤ 8` | 0 failures |
| `(I2)` | 408 rationals | 0 failures |
| `(I3)` | 299 triples + boundary | 0 failures; sharp at `T = 1/15` |
| `(I4)` `N`-form | 12 s.f. | exact; `A`-form is `S−1` |
| `(I5)` | 270 cells, both anchors | 0 failures |
| A6 | `a < 3000`, `L ≤ 44` | `P/8^L ∈ [0.082, 12.168] ⊂ (1/15,15)` |
| A7 (4 realized `P`) | `L ∈ {1,2,3,5,8,12,20,30,40}`, `a < 2000` | exactly 4 each; corners as predicted |
| floor lemma | 20 000 random reals | 0 failures |
| A1 | `a < 24` termwise, `a ≤ 240` parity | 0 failures |
| A2 | `a < 26` vs enumerated `N_a` | 0 failures |
| A8 complexity | `L ≤ 13`, `a < 4000` | `193 ≤ 196` |
| A12 width | exact `X_a`, `a ≤ 280` | 0 violations; slacks 5.27 / 4.19 / 9.19 |
| A10 on a realized block | `L=3, m=12, P=360` | `[ℤ^m:Λ]=180`, 30-smooth; `Ψ` surjective |
| A13 `(♦)` end-to-end | exact `Fraction`s | `15US − V/P = 15T` exactly |
| `2ℤ` invariant | `P`-class `L=4, m=9`, 200 vectors | 0 failures |
| `s_j` chain | `L=6, m=10`, 300 vectors each | cylinder 300/300; **`P`-class 0/300** |
| `B=1` certificates | `A ∈ {5,10,20,40,60}` | all candidates refuted, depth `≤ 5` |
| residue variety | 24 rows | 0 overshoots, 4 exact (sample-starved) |

### 8.4 Soft spots a referee will poke

1. **`A16` is not a lemma; it is the problem relocated.** It asks for short vectors in a lattice
   of dimension `≈ 3L` and covolume `≈ 2^{3L}` to hit a prescribed fibre of an independent
   character. Nothing in §2–§5 constrains the geometry of `Λ`.
2. **The `B = 1` branch is a second open statement**, not a footnote (E6). Any presentation that
   says "the programme reduces #269 to one open statement" is wrong.
3. **`P`-class and `s_j`-chain are not simultaneously available** (E11). A proof attempt must
   choose: large pools (`P`-class) or good coordinates (cylinder). Cylinder certificates do
   transfer upward, so the cylinder is the safer target; the `P`-class is the safer *hypothesis*
   for stating A16.
4. **The empirical `J = 1` is unexplained.** The generic Siegel bound is far too weak to produce
   `±1` kernel vectors at `m ≈ 3L`; so `44/44` blocks with `J = 1` is either a structural fact
   about the `e_{a+j}` matrix or small-`L` luck, and nothing here distinguishes those.
5. **The residue-variety saturation (§2.7) is not used and could not be used as stated**: it
   constrains residue *sets*, not *short generators*.
6. **`exact_results[58]` is `exact_checker`, not proved.** §3.3 proves a strictly stronger
   bound, so nothing downstream depends on the packet's status.
7. **`a₀(M)` monotonicity** is used in A13 (`M | Q_{a_1} ⇒ M | Q_{a_r}`); immediate, but it must
   be stated in any formalization.
8. **The `B = 1` coverage figure (`A ≤ 50000`) is unverified** and may be a re-description of
   `exact_results[49]`'s different rectangle (§6.2).
9. **`(iii*)` in the `P`-class design is comfortable, but the table of §5.1 uses `m = 3L+3`.**
   Any `J`-argument that needs more members costs `L`, and the cost is `≈ (2/3)log₂` of the
   member count.

---

## §9. Wave-2 certificate record (addendum, same day)

Landed after this document was drafted; `wave2_j_scale` receipts, all exact-arithmetic,
independently re-derived engine (VERIFIED-COMPUTATIONALLY unless noted).

**Headline exclusion certificate** (`headline_certificate.json`, end-to-end verification with
exact big-int/`Fraction` arithmetic, 0 failures): `L = 128`, `m = 64`, `P`-class grouping,
`a₁ = 10005`, `P ≈ 2^386.41`, `[ℤ^64 : Λ] = P/2` exactly (Bareiss), max weighted budget
`≈ 2^37.43`. Conclusion: **`S` is not a rational whose *reduced* denominator is `M·B` with `M`
30-smooth dividing `Q_{10005}` (`= 2^10005·3^6312·5^4308`), `gcd(B,30) = 1`, and
`1 < B ≤ B_max ≈ 1.135×10^105`.** Explicit `(i*)(ii)(iii*)` witnesses were exhibited for
`B = 7, 11, 13, 101, 1009, 65537, 10⁶+3, 10⁹+7, 10¹²+39, 10¹⁵+37`. `B = 1` is not claimed
(§6.2 branch). This is a finite exclusion, not the parent theorem.
Wave-3 adversary re-verified the certificate end-to-end from an independent exact engine
(0 failures; extra witnesses `B = 10³⁰+57, 10⁶⁰+33, 10¹⁰⁰+267`), with two repairs folded in
here: the A14 instantiation takes `β_B = P/B` per `B` (every basis vector's budget `< P/B`
throughout the range; same conclusion), and the "26× slack" is unused headroom — contradicting
against the computed distances instead of the width bound gives `B_max ≈ 3.0×10^106` free.

**Cofinality scan:** `J = 1` in **124/124** blocks (50 cylinder + 74 `P`-class, `a₁` up to
55,001, **all at `L = 32`** — cross-`L` evidence is the separate 82-row cylinder sweep),
including a fixed-budget `β = 2^40` regime run precisely because adaptive `β` makes
`J = 1` uninformative. `[ℤ^m : Λ] = P/2` in every one of those blocks. **Index-deficient blocks
do exist** (wave-3 adversary: an `L = 64`, `m = 8` cylinder block with all eight `Ê′` even, index
`(P/2)/2`; within-cylinder parity is *correlated*, ≈20× the independent rate) — but they are
**favourable, not obstructions**: joint gcd `G > 1` makes `Λ` denser (covolume `(P/2)/G`),
vectors shorter, exclusions larger, and the J-lemma never needed index `= P/2` (any 30-smooth
index keeps `Ψ(Λ) = ℤ/B`).

**Structural split of A16 discovered by the scan.** `[ℤ^m : Λ] = P/2` ⟺
`gcd(Ê′_{a_1},…,Ê′_{a_m}, P/2) = 1` ⟺ (since `P/2` is 30-smooth) **some member has
`Ê′ coprime to 30`** — measured frequency 27.2–27.9% per member vs 26.67% independent-uniform,
`L`-independent. So the *index* half of A16 is a finite-automaton statement over `e mod 30`
and the `b`-word (via `Ê ← b(Ê + e)` and the proved (DIV)). The *binding* half is the budget:
short-basis geometry, Gaussian-heuristic `β ≈ (P/2)^{1/m}(m/2e)W`, with `P`-classes making `m`
unbounded so the asymptotic exclusion target is `B_max ≳ P/(W(a₁+L)·log P)`. Caveat kept from
§6.1: index `= P/2` alone does **not** yield a short full basis (an all-but-one
`Ê′ ≡ 0 (mod P/2)` configuration would give `J = ∞`; never observed, and excluded exactly when
the residues are spread) — the remaining open geometry is a residue-spread/dyadic-ladder
statement about `{Ê′_r mod P/2}` across members, plausibly the same fine-scale statement the
`B = 1` branch needs for window avoidance.

**Scaling laws (measured):** `log₂B_max = 2.693·L − 21.0` under cylinder grouping (slope
measured ≥ 2.86 under `P`-classes at two scales; 3.0 is the A6 ceiling); `a₁`-decay only
logarithmic (`log₂β` vs `log₂a₁` slope 1.70); holding `B_max ≥ T` as `a₁ → ∞` costs
`L ≳ (log₂T + 1.7·log₂a₁ + c)/3`.

---

## §10. Wave-3 terminal formulation: the spread constant κ (addendum, same day)

Wave-3 receipts (`wave3_{index_automaton,beta_geometry,b1_branch,adversary3}`); labels as §0.

**Lemma R (PROVED-HERE, wave-3).** `30 | b_{n−2}b_{n−1}b_n` for every `n ≥ 2` — from `4 > 3`
(3-free runs of the radix word have length ≤ 1) and `8 > 5` (5-free runs ≤ 2). Consequence
(17,630 windows, 0 mismatches, sharp at memory depth 3): `Ê′_{a,L} mod 30` is a function
`G(a+L−1)` of the window-end index alone — the measured `L`-independence is a theorem. Also
PROVED unconditionally (no 4EC): any box with `|I|+|J| > 1` meets the orbit closure in a set of
positive lower density (subgroup/character argument), so e.g. `b_n = 30` has positive density;
and `b_a = 30 ⇒ b_{a+1} ≠ 30`.

**Structure formula (PROVED-HERE, wave-3).** `Ê′_{a,L} = Σ_{j<L} 2^{L−1−j}3^{β_j}5^{γ_j}·δ_{a+j}`
with `β_j, γ_j` the counts of later 3-/5-carries. So `Ê′ mod 2^t` depends on exactly the last
`t` shells (genuine unbounded memory in `t`), while `mod 3` and `mod 5` have memory ≤ 1, ≤ 2.

**The spread constant (PROVED-HERE, wave-3; exact duality).** For a `P`-class block with
`E_r = Ê′_{a_r,L}`, `G = gcd(E_*, P/2)`, `N = (P/2)/G`:

```
κ := min_{1 ≤ q < N} max_r ‖ q·E_r/G / N ‖_{ℝ/ℤ}  ∈ (0, 1/2]
```

with the certified sandwich `max(W_max, W_min/κ) ≤ λ_m(Λ, ℓ¹_W) ≤ m^{3/2}·W_max/κ` (measured
tight to 0.5–4.1 bits), and the exact bridges: `J < ∞ at β ⟺ λ_m ≤ β`; `λ_m ≤ 2β/m ⟹ J = 1`.
**κ unifies both halves of A16**: `κ > 0 ⟺ [ℤ^m:Λ] = P/2` (the index half at threshold) and
`κ ≳ ½N^{−1/m}` is the budget half; index deficiency (`G > 1`) only shrinks `N` and *helps* —
§9's favourability finding drops out of the formula. Blocks are not uniformly generic: one
`L = 32, m = 16` block has κ 13× below the random model; `m` must scale with `log N`.

**Sharpened `B = 1` certificate (ESC) (PROVED-HERE, wave-3).** `[−Ê′_{a,L}]_{P/2} > W(a+L)/2 ⟹
X_a ∉ ℤ` — one residue test refutes every integer candidate at once (0 mismatches vs the §6.2
per-candidate transport; every `a ∈ [1,400)` escapes with `L ≤ 8`). Conversely (PROVED-HERE,
wave-3, `b1_branch`): **no bounded-modulus reader can decide the `B = 1` branch** — for `m | P`
with `m ≤ W/2` the congruence-plus-window constraint is always satisfiable — and an explicit
mod-30 splice countermodel (actual `b`-word, DIV-satisfying, bounded digit perturbation
`≤ 29`, integral orbit) reproduces the §9 index statistic identically. The mod-30 layer is
provably blind to `B = 1`; (DIV) has no refutational content there.

**THE TERMINAL CORE (OPEN), replacing §6's two statements as the unified form.** With
`Θ(a,L;q) := ‖q·Ê′_{a,L}/(P/2)‖_{ℝ/ℤ}`:

> **SPREAD(m, κ₀, Q):** for every `q ∈ Q`: `max_{r ≤ m} Θ(a_r,L;q) ≥ κ₀`.
> - `B = 1` branch = SPREAD(1, `W/(2N)`, {1}) cofinally — measured margin ≈ 10⁶ per instance;
> - `A16` = SPREAD(m, `½N^{−1/m}`, [1,N)) cofinally — the binding corner.

The two corners are **strictly incomparable** (per-member window avoidance is the `q = 1`
slice and provably fails to exclude `E ≡ (1,0,…,0) mod N`, which has `J = ∞`). Name:
**window-forcing residue non-degeneracy.** What the proved layer reaches: the automaton +
(DIV) certify SPREAD for moduli up to `≈ 3log₂m + 5` of the `3L` bits of `N`; the remainder —
(R1) the parity of `P₃₅(2^A)` is not eventually constant (the `M = 2` rung; lattice-point
parity in a dilated irrational triangle), and (R2) the full spread over all divisors and units
— is untouched by bounded-suffix reasoning, which is a proof that any completion must couple
digits across the whole window. Nothing in this section claims the parent theorem; #269 and
both SPREAD corners remain OPEN.

---

## §11. Wave-4 record: (R1) renormalized; the cell layer settled (addendum, same day)

**Cell layer (wave-4 `cell_expansion`) — NOT a wedge, with proofs.** The 3-D cell field of (I5)
is exactly the gap vector of the 1-D counter at the merged prime powers (`c_n = N(μ_{n+1}) −
N(μ_n)`); the cells→shells map is block-diagonal and its digit-space image is **exactly the
(DIV) lattice** (all four `b`-types); cell counts grow like `0.1359·a²` (the earlier max-23 was
an `a ≤ 12` window artifact); at cell resolution every modulus `≤ W` is provably blind
(finer-resolution re-proof of §10's impossibility). Payoffs kept: **(CELL-SHRINK)** pinning the
rigid shell total `c_a = P₃₅(2^{a+1})` collapses admissible digit perturbations to
`{0}/10ℤ/12ℤ/2ℤ` by `b`-type — forced zero on the 20.7%-density `b_a = 2` shells, forced even
everywhere (`e_a ≡ c_a (mod 2)`, now a one-line proof); and the mod-2 rung of the digit stream
**is (R1)** — an independent second arrival at the same terminal statement (canonicity
evidence).

**(R1) renormalized (wave-4 `triangle_parity`; (R1) remains OPEN).** PROVED `T(A) = c_{A−1}`
exactly (`T(A) = P₃₅(2^A)`; convention trap: the strip count is `c_A − c_{A−1}`). Main result —
an exact `O(log A)` renormalization: with `w′ = log₃(5/3)`, `c = 1 − {A/α}`, `K = ⌊A/β⌋`,

```
T(A) = (K+1)(⌊A/α⌋+1) − D − K(K+1)/2,   D = Σ_{k≤K} ⌊k·w′ + c⌋,
```

and mod 2 an explicit 𝔽₂ formula over the Euclid/Ostrowski trace of `D` (`ε_t =
[n_t(n_t−1)/2]·q_t + [n_t]·d_t`, `q_t` the CF quotients of `w′` — the A-independent stream
`[0,2,6,1,1,1,3,7,3,1,1,11,3,7,…]` — and `d_t` the Ostrowski digits of `c`). **Wave-5
independent verification**: 0 mismatches dense to `A = 3000/4000` and at
`10⁶ … 10⁶⁰` on both bracket ends (trace depth ≈ 2.1 levels per decade; certification margin at
`10⁶⁰`: needed precision ~10⁻¹²³ vs bracket 10⁻²⁴⁵ — 122 digits of slack; the wave-4 artifact's
own exact-form check had a **sign error** and its `renorm.py` crashes at `10²⁴`, so the formula
was true-but-unverified when first recorded — it is verified now; the `c`-bracket discontinuity
must be absorbed algebraically, `⌊kw′+c⌋ = (1+⌊z⌋) + ⌊(k(β−α)−A)/α⌋`, before certifying).
Non-integrality of `kw′+c` is unconditional (unique factorization — no Baker input). Parity
non-constancy: dense to `3×10⁵` (odd density 49.941% for `T`; cancellation `O(√N)`, factor ~850
below what constancy demands) and in four certified 301-wide sparse windows at
`10²⁴, 10⁴⁰, 10⁶⁰` (147–154 flips each) — sparse-window evidence, not dense coverage.
Routes CLOSED with proofs: the (I2)/(I3)/(I5) identity layer is **parity-void** for `T`
(integer-argument instantiations collapse to `1 = 1`; wave-5 strengthened this: the 𝔽₂
nullspace of `[T(A..A+8), edge counts, N(2^A), A, 1]` over 20,000 values has dimension 0); no
fixed finite torus condition decides parity (needed resolution shrinks like `N^{−1/2}`; `T`'s
row-form Birkhoff length is `0.4307A` (the strip count is the `0.2717A` object), and
renormalization trades unbounded `A`-memory for unbounded trace length — a complexity gain, not
a decidability gain). **Baker does not bite**: what would be needed is Ostrowski-digit
statistics of the specific number `{A/α}` w.r.t. `CF(log₃5)` — no effective result delivers
that; (R1) is *not* conditional on any known linear-forms-in-logs input. **Minimal remaining
lemma (purely combinatorial; CORRECTED by wave-5 audit): exhibit infinitely many `A` with a
companion `A′` such that the full mod-2 functional — the `ε_t` slots TOGETHER WITH the
outside-trace slots `(K+1)(⌊z⌋+1) + K(K+1)/2` — differs in an odd number of slots; then both
parities occur cofinally.** (The single-`ε_t` form first recorded here is insufficient: of
27,766 pairs with ε-Hamming distance 1 at `A ≤ 4000`, 14,091 do *not* flip the parity — the
outside slot absorbs the difference.) Nothing in this section claims the parent theorem; #269,
both SPREAD corners, and (R1) remain OPEN.

---

## §12. Wave-5: the multiplicative companion mechanism — (R1) reduced to (MRL′)

Wave-5 `mrl_attack` receipts (`wave5_mrl_attack/`); the ε-slot MRL of §11 is superseded (its
identical-trace/head-flip family is measured EMPTY — 0/93 pairs — and the cascade analysis
proves single Ostrowski-digit perturbations propagate to every deeper Euclid level, so
ε-Hamming-1 pairs are coincidental).

**Lemma S (shell splitting; PROVED — wave-6 CORRECTED form).** For integers `p, n ≥ 1` with
`3^p ≈ 2^n`, `δ = pα − n ≠ 0` (unique factorization): splitting shell `A+n` by whether the
3-exponent is `< p`, the map `(u,v) ↦ (u+p, v)` is a bijection onto the high part (a whole
quadrant — no second correction band), giving **`s(A+n) = C_p(A) + s(A) + Σ⁺(A) − Σ⁻(A)`**,
the slivers being the two width-`|δ|` intervals abutting `2^A` and `2^{A+1}` (their sides swap
with the sign of `δ`). The earlier phrasing here omitted the `+ s(A)` term (false as written,
149/149 failures at `(12,19)`; wave-5's own `exp4_verify.py` had it right as
`s(A+n) − s(A) = C + C_slv`). What the parity argument needs is `Σ⁺ ≡ Σ⁻ (mod 2)` — sliver
emptiness is sufficient, not necessary.

**Lemma T (torus form; PROVED).** `C_p(A) = F_p({(A+n)/β})` with
`F_p(x) = #{0 ≤ i < p : {x − i·log₅3} ∈ (1 − log₅2, 1)}` — a **one-dimensional** torus
function: the enabling condition needs only Weyl for `log₅2`, no 4EC, and thereby evades §11's
finite-torus impossibility (which forbids *deciding* parity from a box, not *flipping* it).
Both lemmas: 0 failures over `(p,n)` up to `(665, 1054)` and general variants.

**The chain — wave-6 AUDITED, with a real break and its repair.** L1 = Lemma S (PROVED,
corrected form) · L2 = Lemma T (PROVED; wave-5 verified it only to `(53,84)`, wave-6 closed
`(665,1054)`, `A < 1200`, 0 failures) · L4 = sliver-emptiness for all `A ≤ N_p` via
Matveev/Baker — sound, **but the window is astronomically thin**: with the real Matveev
constant (`K ≈ 1.755×10¹¹` for this three-log form) and any finite irrationality measure of
`log₂3` (Rhin-class `μ ≈ 5.117` known), `N_p = O(p^{(μ−1)/K}) = p^{o(1)}` — every wave-5
empirical witness lies *outside* the certified window. Precision on the Baker boundary: §11's
"Baker does not bite" concerns the *parity*; sliver-emptiness is Baker's home turf; both stand.
**[SUPERSEDED — E12/§14.1.** The second half is wrong. Sliver-emptiness against an *integer*
level is elementary (unique factorization; `A ≥ 1`), with window `A ≲ log₂p_{r+1}` against
Matveev's `p^{6×10⁻¹²}`. Baker is not on the critical path. The §12 BREAK below nevertheless
survives — read §14.1 before using anything in this section.**]
· **BREAK (wave-6):** the original L5 needed a witness `A ≤ N_p` with `F_p` odd at
`{(A+n)/β}`; converting (MRL′)'s *measure* into such a *witness* needs `≳ p` samples
(the odd-set is exactly `p` intervals of width `~1/(2p)`; Erdős–Turán forces `M ≳ p`), while
`N_p = p^{o(1)}` — **a power-of-`p` mismatch. (MRL′) alone does NOT imply (R1).** "Only Weyl
is needed" was wrong: the killed requirement was quantitative discrepancy against a
`p`-refining set. · **REPAIR (quantifier reversal; the operative route):** fix `A ≥ A*`
FIRST; `N_p → ∞` makes `N_p ≥ A` reachable for all large convergents; ¬(R1) then forces
`F_p({(A+n_p)/β})` **even for every such `p`**. The residue becomes pointwise — no
equidistribution anywhere:

> **THE OPERATIVE RESIDUE — (MRL″) (OPEN):** for some `A`, infinitely many convergents `p`
> (`3^p ≈ 2^n`) have `F_p({(A+n_p)/β})` odd. (Since `1/β = log₅2`, the evaluation points are
> the orbit `{(A+n_p)·log₅2}` — the same specific-orbit object as (D′) below; the two residues
> converge.) Measured: the parity of `C_p(A)` is non-constant across the family for every
> fixed `A ≤ 12`.

> **(MRL′) (OPEN; now auxiliary):** there exist `μ₀ > 0` and infinitely many `p`
> (`3^p ≈ 2^n`) with `|{x ∈ 𝕋 : F_p(x) odd}| ≥ μ₀`. Supports (MRL″) heuristically; does not
> imply (R1) by itself (the break above).

A **measure statement about the starting point of a rotation** — strictly softer than (R1),
Kesten/Beck Birkhoff-sum territory (`log₅2 ∉ ℤ·log₅3 + ℤ` by unique factorization, so the
interval is not a bounded-remainder set and the discrepancy is unbounded). Measured (wave-6
CORRECTED — the wave-5 fast sweep seeded at the event point `x = 0` and reported the
complement): `μ_p = 0.5491 → 0.5005` along convergents `p = 665 … 190537`; over all
`p ≤ 3000`: mean 0.5001, **min 0.1399 at `p = 460`** (the earlier "0.0700 at 230" was the
complement of the *maximum*, `μ₂₃₀ = 0.9300`), 4 values below 0.25, none below 0.10. Whether a
published Kesten/Beck-type theorem delivers (MRL′) is a literature question, flagged for the
external-research lane. Wave-6 structure (receipts `wave6_mrl_prime/`): `μ` is a
translation-invariant pseudo-norm on ℤ (exact cocycle `F_{a+b}(x) = F_a(x) + F_b(x−aγ)`);
`F_p` flips parity at exactly `2p` points (unique factorization); exact phase-free block
decomposition over any composition of `p`; the rigidity law `μ_q = dist(q·log₅2, 2ℤ)` holds
iff `range(F_q) = 1` (iff verified to `q ≤ 1200`; range-1 set `{1,3,22,63,293,523,753,983}` —
NOT all CF(γ) denominators); the identity `1 − 2μ_p = ⟨ψ, ψ(·+ℓ)⟩` for the alternating
orbit-counting function ψ (proved; the Fourier mass sits at `|n| ~ p`, so no low-frequency
shortcut). Unconditional non-collapse: **`max(μ_p, μ_{p−3}) ≥ 0.35399` for every `p`**
(proved), plus family-transfer certificates `≥ 0.24–0.354` for `r = 2…12` (decaying per
iteration — not cofinal). The remaining gap, classified: a decorrelation estimate for
well-separated blocks (the product law `1−2μ_p ≈ Π(1−2μ_{q_j})^{c_j}` is accurate only under
scale separation, error ≤ 0.0021 for the family, NOT one-sided in general), plus **(D′)**:
infinitely many family `p_r` have a nonzero Ostrowski digit (w.r.t. CF(log₅3)) at a level
`q_j ≤ 41` — equivalently `{n_r·log₅2}` (`n_r` the CF(log₂3) numerators) does not eventually
confine to one fixed small arc. (D′) holds for all 22 family members computed to
`p = 5.4×10¹²`; it is **Baker-silent** (Baker bounds distance from 0, (D′) needs distance from
a fixed point — opposite direction) and 4EC-adjacent. **Important structural negative
(proved-modulo-product-law): `inf_p μ_p = 0` is near-certain (`‖q₇₀(γ)·log₅2‖ = 0.0013` at
`q₇₀ ≈ 7×10³¹`), so no `p`-uniform argument can prove (MRL′) — any proof must use the
3^p ≈ 2^n family structure.** Trade-off
law: `p·|δ|` governs the certified window versus box-lemma reach (the minimal companion
`(p,q) = (−1,1)` satisfies §10's box-density lemma unconditionally but caps at `A ≲ 14`).
Artifact hygiene: use `wave5_mrl_attack/trace.py` (standalone, re-verified) — never import
`wave4_triangle_parity/renorm.py`. Nothing in this section claims the parent theorem; #269,
both SPREAD corners, (R1), and (MRL′) remain OPEN.

---

## §13. Wave-7 terminal record: the campaign's converged residue

Wave-7 `mrl_pointwise` receipts (`wave7_mrl_pointwise/`); everything below flagged for
independent audit before downstream use.

**New identity layer (PROVED; 0 failures at 320/900/125 checks).** `(W)`
`T_p(M) = −Σ_{i<p}⌊iγ − Mℓ⌋`; `(N)` `C_p(A) = W_p(A+n) − W_p(A+n+1)` — a second independent
evaluator for the Lemma-T object; `(TEL/TEL2)` exact telescoping column identities with closed
form `Σ_{A<L}C_p(A) = p⌊Lℓ⌋ + Φ_p({Lℓ})`. `W_p` is a floor-sum, so **`C_p(A)` is exactly
computable in `O(log p)`** on certified dyadic brackets — scale jump to `p ≤ 6.17×10³⁹`
(86 family members; 5,590 exact parity cells).

**Theorem W7-N1 (PROVED; audit required).** The telescoping/A-coupling contradiction route is
**impossible**: a contradiction would need a finite level-set `S` whose arc-cover multiplicity
`μ_S(t)` is odd for *every* `t`; telescoping over maximal runs of `S` jumps `±1` at `2M`
pairwise-distinct points (distinctness by unique factorization), so the parity is never
constant. (𝔽₂-elimination unsolvable for all `L ≤ 300`; brute force `L ≤ 14`, 0 hits.) The
exact `r`-recursion along CF convergents (verified, 288 pairs) likewise **cannot propagate**
¬(MRL″) — its blocks sit at huge levels with off-integer offsets.

**The decisive measurement.** [**INFERENCE SUPERSEDED — E13/§14.2: the measurement reproduces
exactly at `r ≤ 85`, but `A*` is `Geometric(½)`, so `max A*` grows like `log₂(#convergents)`;
over 1097 certified convergents `max A* = 13`. There is no constant level.**]
`A*(r) := min{A : C_{p_r}(A) odd}` has **maximum 5 over all 86
members** (mean 1.047; `A* ≤ 2` for 78/86): the odd witness sits at a **constant level**, and
sliver-emptiness holds at every `A ∈ [1,24)` for all members. The §12 break is thereby
quantified: the witness is empirically constant-level; only the certified conversion fails.

> **TERMINAL RESIDUE OF THE WAVE CAMPAIGN (OPEN).** [**SUPERSEDED by (ODD-∞), §14.3 — drop the
> `{0,…,5}` box (E14: unsound as a bound, unnecessary as a hypothesis; every fixed level has odd
> density `½`), and exclude `A = 0` (E15).**] A fixed `A ∈ {0,…,5}` with
> `C_{p_r}(A) = F_{p_r}({(A+n_r)·log₅2})` odd for infinitely many convergents `p_r` of
> `log₂3`. Wave-7 **proved** that no combinatorial rearrangement of the level constraints can
> substitute for this: any proof must supply an external Birkhoff/Ostrowski evaluation of the
> specific orbit `{n_r·log₅2}` in a non-bounded-remainder arc. This is the definitive
> convergence point of (MRL″), (D′), and — through §10 — the `B = 1` corner of SPREAD.

**Campaign verdict.** Seven waves (28 agents) exhausted the internal corpus on this residue:
every combinatorial, automaton, lattice, cell, transport, and metric route is now either
proved, certified, or retired with a proof of why. The two named open cores — SPREAD's binding
`B > 1` corner (§10) and the specific-orbit statement above — are the escalation surface for
the external-research lane. Nothing in this document claims the parent theorem; **Erdős #269
remains OPEN.**

---

## §14. Wave-8: eight parallel Type B returns, assimilated

Eight independent Type B returns fired against the §10–§13 escalation surface. They could not
see each other, so the first job was deduplication against this document and against each
other; the second was verification. Labels as §0. Verifiers:
`wave8_typeb_assimilation/` (exact integer comparisons on certified 1200-digit rational
brackets of `log 2, log 3, log 5`; every certified quantity computed under **both** bracket
endpoints and accepted only on agreement; no float decides any claim).

**None of the eight proved #269, and none proved either SPREAD corner.** Five carried genuinely
new mathematics; two carried claims false as stated; one re-derived a route this corpus had
already fenced. The net effect is larger than any single return: **two of this document's own
wave-6/wave-7 conclusions are wrong**, and correcting them removes Baker from the critical path
and dissolves the constant-level framing of §13.

### 14.0 Errata found in *this document* (E12–E15)

| # | Claim | Verdict | § |
|---|---|---|---|
| **E12** | §12: *"sliver-emptiness is Baker's home turf"* | **Misclassification, and quantitatively fatal.** Sliver-emptiness against an *integer* level is elementary — unique factorization alone — with window `A ≲ log₂p_{r+1}` against Matveev's `p^{(μ−1)/K} = p^{2.3×10⁻¹¹}` (§12's own constants `K ≈ 1.755×10¹¹`, `μ ≈ 5.117`). At `r = 124` that is `A ≤ 200` versus `A ≤ 1`. The whole (MRL′) apparatus of §12 was built under an unnecessary constraint. | §14.1 |
| **E13** | §13: `A*(r)` has *"maximum 5 over all 86 members"* ⇒ *"the odd witness sits at a **constant level**"* | **Horizon artifact.** The measurement is right and I reproduce it exactly; the inference is wrong. `A*` is `Geometric(½)`, so its max over `N` convergents is `≈ log₂N`; `86` members give `≈ 6`. Extended to 1097 certified convergents: **`max A* = 13`**, `A* > 5` at 17 indices. | §14.2 |
| **E14** | §13 terminal residue restricting to *"a fixed `A ∈ {0,…,5}`"* | The box is **unsound as a bound** (E13) and **unnecessary as a hypothesis**: at *every* fixed `A ∈ {0,…,8}` the odd density across 1097 convergents is `0.483–0.521`. Drop the box; state the residue at one fixed `A`. | §14.3 |
| **E15** | §12 Lemma S at `A = 0` | **Off by one.** `3⁰5⁰ = 2⁰` exactly, so the integer separation `|3^u5^v − 2^A| ≥ 1` fails and the sliver carries the single point `1`. Measured `Σ⁺ − Σ⁻ = −1` at `A = 0` for every convergent tested. The elementary window needs `A ≥ 1`, and no return stated this. Same shape as (I3)'s sharp `T > 1/15` (§2.3). | §14.1 |

### 14.1 The elementary sliver window — Baker off the critical path

> **A17 (PROVED-HERE).** Let `A ≥ 1` and let `x = 3^u5^v` be any smooth point. Then
> ```
> |log₂x − A| ≥ log₂(1 + 2^{−A}) > 1 / ((2^A + 1)·ln2) .
> ```

*Proof.* `A ≥ 1` and unique factorization give `3^u5^v ≠ 2^A`, so `|x − 2^A| ≥ 1` — both are
integers. If `x > 2^A`, `log₂(x/2^A) ≥ log₂(1+2^{−A})`; if `x < 2^A`,
`log₂(2^A/x) ≥ −log₂(1−2^{−A}) > log₂(1+2^{−A})`. ∎ **At `A = 0` the hypothesis fails and the
conclusion is false** (E15): `x = 1` attains equality.

> **A18 (PROVED-HERE).** Let `n/p` be any rational with `δ = pα − n`, `α = log₂3`. If
> `|δ| ≤ log₂(1 + 2^{−(A+1)})` and `A ≥ 1`, then **both** slivers of Lemma S (§12) at level `A`
> are empty, so
> ```
> s(A+n) = C_p(A) + s(A)    exactly,   hence   s(A+n) ≡ C_p(A) + s(A)  (mod 2).
> ```

*Proof.* The slivers are the two log₂-width-`|δ|` intervals abutting the integer levels `A` and
`A+1`; A17 at each, the binding one being `A+1`. ∎ **No linear form in logarithms is used, and
no irrationality measure.** Dirichlet already gives infinitely many `p` per fixed `A`.

**VERIFIED-COMPUTATIONALLY** (`lemma_s2.py`): **161 exact instances, 0 failures**, over
`r ∈ {4,…,399}` and `A ∈ [1,12] ∪ {A_max−1, A_max}`, `p` up to 696 bits. The realized window
tracks the prediction exactly:

| `r` | `log₂p_r` | elementary `A_max` | Matveev `N_p` (§12) |
|---|---|---|---|
| 39 | 66 | 66 | `≈ 1` |
| 124 | 200 | 200 | `≈ 1` |
| 249 | 421 | 424 | `≈ 1` |
| 399 | 696 | 696 | `≈ 1` |

**What this does not do.** §12's BREAK **survives**: converting (MRL′)'s *measure* into a
*witness* still needs `≳ p` samples against a window of `log₂p_{r+1}`. The elementary bound does
not resurrect (MRL′) ⇒ (R1). What it does is make §12's REPAIR (fix `A` first) unconditional,
explicit, and wide — which is exactly what removes the pressure that produced §13's box.

### 14.2 `A*(r)` is Geometric(½) — the corrected empirical law

`A*(r) := min{A ≥ 0 : C_{p_r}(A) odd}`, over the first **1097** certified convergents of
`log₂3` (`astar_scan.py`; 0 uncertified rows).

| `A*` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 13 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| observed | 554 | 265 | 140 | 67 | 37 | 17 | 7 | 5 | 1 | 1 | 2 | 1 |
| `N·2^{−(A*+1)}` | 548.5 | 274.2 | 137.1 | 68.6 | 34.3 | 17.1 | 8.6 | 4.3 | 2.1 | 1.1 | 0.5 | 0.07 |

Over the eight cells `A* ≤ 7`, where every expected count exceeds `4`, **`χ² = 1.09` on 7 d.f.**
Beyond that the expected counts fall below `1` and `χ²` does not apply; the lone `A* = 13` is the
ordinary maximum of 1097 geometric draws (`P ≈ 0.13` of seeing one). **`max A* = 13` at
`r = 978`**; `A* > 5` at
`r ∈ {124,170,183,287,344,400,477,645,649,675,689,690,754,803,810,914,978}`.

Restricted to wave-7's own horizon `r ≤ 85` this engine returns **max 5, mean 1.035,
`A* ≤ 2` for 78/86** — §13 reports max 5, mean 1.047, 78/86. The two engines agree on the
overlap; §13's range was simply too short to see the law. Four of the eight returns each
reported one isolated counterexample (indices 125, 171, 184, 979 in 1-based convention =
`r = 124, 170, 183, 978` here, `A* = 7, 7, 10, 13`); all four are confirmed, and all four are
instances of the same distribution rather than anomalies.

**Consequence.** No `∀r`-bounded-level lemma is available, at any constant. Any future proposal
of the form "some `A ≤ K` always works" is refuted in advance by `max A* ≈ log₂(#convergents)`.

### 14.3 The corrected (R1) residue

For each **fixed** level, the odd density of `C_{p_r}(A)` across all 1097 convergents:

| `A` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| odd density | .5050 | .4831 | .4904 | .5205 | .4895 | .5105 | .5059 | .4959 | .4904 |

So the level is not scarce; **every** fixed level is a fair coin. Combining with A18:

> **(ODD-∞) (OPEN) — replaces §13's terminal residue.** For cofinally many `A ≥ 1`, there are
> infinitely many `p` with `|p·log₂3 − n| ≤ log₂(1+2^{−(A+1)})` and `C_p(A)` **odd**.
>
> **(ODD-∞) ⇒ (R1).** *Proof.* If `T(·) mod 2` were eventually constant then `s(t) ≡ 0 (mod 2)`
> for `t ≥ t₀`; pick `A ≥ t₀` from the cofinal family and any admissible `p`; A18 gives
> `0 ≡ C_p(A) + 0`, contradicting oddness. ∎ **PROVED-HERE.**

This is strictly weaker than §13's residue (no constant-level box, no `A ∈ {0,…,5}`), it is
Baker-free, and its measured support is `½` at every level rather than a search over six.
`A = 0` is **excluded** by E15 and must not be used as the witness level.

### 14.4 LCM homogenisation — E11 dissolved (Returns 4 and 5, independently)

Two returns converged on the same device, which this document lacks. For fixed `L` put

```
P̄_L := 2^L 3^{⌊Lθ₃⌋+1} 5^{⌊Lθ₅⌋+1} ,      ρ_{a,L} := P̄_L / P_{a,L} .
```

> **A19 (PROVED-HERE).** `ρ_{a,L} ∈ {1,3,5,15}` for **every** start `a`, with no `P`-class or
> cylinder restriction.

*Proof.* Immediate from A7: `P_{a,L} = 2^L3^u5^v` with `u ∈ {⌊Lθ₃⌋,⌊Lθ₃⌋+1}`, likewise `v`. ∎
**VERIFIED-COMPUTATIONALLY**: 17 600 `(a,L)` pairs (`L ≤ 44`, `a < 400`), all four values
realized, 0 violations.

**Why this matters.** §8.4(3) forces a choice: `P`-classes for pool size *or* cylinders for the
`s_j` coordinates (E11). A19 removes the choice at the level of the *modulus*: **all** starts
share the single modulus `P̄_L` at an endpoint cost of at most `15`, so `(i*)` may be imposed
mod `P̄_L/2` over an unrestricted pool while `(iii*)` pays a factor `≤ 15`. Against
`P̄_L ≍ 8^L` that factor is free. The phases are preserved *exactly*, not just in norm: with
`F_a := ρ_{a,L}Ê′_{a,L}` and `M* := P̄_L/2`,

```
‖ q F_a / M* ‖  =  ‖ q Ê′_{a,L} / (P_{a,L}/2) ‖    for every q,
```
since `F_a/M* = Ê′_{a,L}/(P_{a,L}/2)` identically. So κ (§10) is unchanged by homogenisation.
**PROVED-HERE.** This does not settle A16; it removes a bookkeeping obstruction that had been
recorded as structural.

### 14.5 SPREAD reduces to a one-launch arc bound (Return 1)

> **A20 (PROVED-HERE).** Let `𝒜` be a pool of `M` starts sharing modulus `N`, and
> `b_q := #{a ∈ 𝒜 : ‖qE_a/N‖ < ½N^{−1/m}}`. If
> ```
> Σ_{q=1}^{N−1} (b_q)_m / (M)_m  <  1        ((x)_m = falling factorial)
> ```
> then some `m`-subset satisfies SPREAD(m, ½N^{−1/m}, [1,N)). In particular
> **`b_q/M ≤ N^{−1/m}` for every `q` suffices.**

*Proof.* Draw an ordered `m`-tuple of distinct starts uniformly. It fails at `q` iff all `m`
land in the bad set, with probability `(b_q)_m/(M)_m`; union bound. For the special case,
`(b)_m/(M)_m = Π_{i<m}(b−i)/(M−i) ≤ (b/M)^m ≤ 1/N`, and `(N−1)/N < 1`. ∎

**The reading that makes it actionable.** At the working regime `m ≈ 3L`, `N ≍ 8^L`, we have
`N^{−1/m} → ½`. So the sufficient condition is literally: *for every multiplier `q`, at most
half the pool lands in the half-circle arc around `0`.* SPREAD's binding corner is therefore not
a joint `m`-dimensional spread statement but a **single-launch no-half-circle-concentration
statement** — and `P`-classes (or A19) make `M` as large as wanted while `m` stays `≈ 3L`.
This is the cleanest reformulation of §10's binding corner produced so far.

### 14.6 A CRT terminal-digit star forcing κ ≥ 1/3 (Return 6)

> **A21 (PROVED-HERE).** Let `N = 2^a3^b5^c > 1` and `m = a+b+2c`. Suppose the reduced block
> residues contain, for each `0 ≤ j < a`, a row `≡ (N/2^a)2^j u` with `u` odd; for each
> `0 ≤ j < b`, a row `≡ (N/3^b)3^j u` with `3∤u`; and for each `0 ≤ j < c`, **two** rows
> `≡ (N/5^c)5^j u` and `≡ (N/5^c)5^j v` with `u,v` units and `v/u ≡ 2` or `3 (mod 5)`. Then
> `κ ≥ 1/3 ≥ ½N^{−1/m}`.

*Proof.* Given `q ≢ 0 (mod N)`, some `p ∈ {2,3,5}` has `d := a_p − min(v_p(q),a_p) ≥ 1`; use its
row at level `j = d−1`. The complementary CRT factor cancels and `qE/N` reduces to a non-zero
terminal digit mod `p`: distance `1/2` for `p=2`, `≥1/3` for `p=3`. For `p=5` the residue is
`q'u/5`; if `q'u ≡ ±1` the partner row `q'v/5` has `q'v ≡ ±2` because `v/u ≡ 2,3`, giving `2/5`.
The Gaussian target is exact:
`N/(3/2)^m = (4/3)^a 2^b (20/9)^c ≥ 1`, so `N^{1/m} ≥ 3/2` and `½N^{−1/m} ≤ 1/3`. ∎

**VERIFIED-COMPUTATIONALLY** (`algebra.py`): 8 shapes `(a,b,c)`, exhaustive over all `q`;
**`κ = 1/3` exactly in 6 of 8** — the constant is sharp, not merely a bound. A companion
(also PROVED-HERE, verified `N = 3…399`): a unit dyadic ladder
`{u·2^k : 0 ≤ k ≤ ⌈log₂(N/3)⌉}` forces `κ ≥ 1/3` by first-crossing of `N/3`.

**What A21 changes.** The `B > 1` corner stops being "prove the residues behave randomly" and
becomes "construct `m = a+b+2c` prescribed valuation levels from the suffix-weight formula
`Ê′_{a,L} = Σ_j 2^{L−1−j}3^{β_j}5^{γ_j}δ_{a+j}` (§10)". That is a symbolic construction problem
with a finite certificate, not a geometry-of-numbers problem. It is **not** discharged: the
residues are given, not chosen. Open, and named **KERNEL-STAR**.

### 14.7 Returns that do not survive, and one correction to a return

* **The `10^1000` exclusion certificate (Return 7) adds no mechanism.** It is the continued-
  fraction route: 2300 shells give a tail `≈ 8^{−2300}`, hence `≈ 2077` digits of `S`, hence
  denominators to `≈ 10^{1038}`. That is exactly the `Θ(√B_L)` law the corpus already records
  as a **negative** result (`research_packet.json`, the finite-escape-certificate row), and the
  §9 block certificate at `10^105` is a structurally different and more informative object. A
  larger finite exclusion is not progress toward either corner. *Recorded as retired, not new.*
* **"The six-level parity terminal is FALSE" over-reads §13.** §13 asserts an
  `∃A ∀^∞ r` statement, which my data **supports** (§14.3); what is false is the `∀r` bound that
  motivated the box (E13). Both halves matter and the returns stated only one.
* **Return 6's Jacobi identity is right and its correction is worth keeping.** For odd `q` and a
  convergent `p/q` of `w ∈ (0,1)`, `(−1)^{Σ_{k=1}^{(q−1)/2}⌊2kw⌋} = (p/q)` (Gauss's lemma); the
  `⌊kw⌋` variant is false, e.g. `p/q = 2/5` gives `+1` against `(2/5) = −1`. Confirmed here. It
  does **not** decide the parity: in the irrational renormalisation the shift, the
  convergent-substitution crossings and §11's outside-trace slots all remain.
* **Two returns re-derived A8/A11 verbatim** (cylinder complexity `≤(L+1)²`; the `{−1,0,1}`
  subset-sum collision at `m ≥ 3L+3`). Already on disk; the *cost comparison* they draw from it
  is new and correct — a full cylinder costs only `O(L³)` in start horizon against `P/B ≍ 8^L`,
  so E11's incompatibility is a bookkeeping cost, not a barrier. A19 supersedes it.

### 14.8 Fencing: the `q = 1` slice is not an equidistribution statement (Return 7, sharpened)

> **A22 (PROVED-HERE).** On any block, with `P = Q_{a+L}/Q_a`,
> ```
> 2Ê′_{a,L} = P·X_a − X_{a+L} ,      hence      Ê′_{a,L}/(P/2) ≡ Q_a S − X_{a+L}/P   (mod 1).
> ```
> Therefore the `q = 1` slice of §10's `Θ` satisfies, **with equality**,
> ```
> Θ(a,L;1) = ‖ Q_a S − X_{a+L}/P ‖ ,     and     |X_{a+L}/P| ≤ W(a+L)/P .
> ```

*Proof.* `(R2)` in `Y = 15X` units gives `30Ê′ = 15(P X_a − X_{a+L})`; divide by `15`. Then
`X_a = Q_a S − N_a` (A2) with `N_a ∈ ℤ`. ∎ **VERIFIED-COMPUTATIONALLY** (`fencing.py`, exact
`Fraction`s): the deviation is not merely bounded by `X_{a+L}/P` but **equals** it, to 30 digits,
on every instance tested (`(a,L)` from `(3,4)` to `(6,10)`; deviation `2.5×10⁻⁴ → 8.9×10⁻¹⁰`).

**What this fences.** The same identity holds after multiplication by every integer `q`.
The resulting error is at most `|q|` times the endpoint-tail bound divided by the window base.
For a controlled finite pool of starts, all multipliers below the reciprocal error scale shadow
the original scalar uniformly. For larger multipliers this estimate may give no useful
information. Any source-derived anti-concentration theorem must therefore retain the multiplier
dependence of the error. Establishing such a theorem would be substantive; assuming that the
residues have become independent of the original value is unjustified. A20 is unaffected as a
*sufficient* union bound; it is not a reason to treat `q ≥ 2` as unshadowed.

### 14.9 Where the frontier now stands

```
B > 1  :  SPREAD(m, ½N^{−1/m}, [1,N)) cofinally.
          Sufficient via A20 to a one-launch half-circle anti-concentration bound
          (the converse is false: N=5, labelled pool (0,0,1,2) has subset {1,2} of
          spread 2/5 while the union-bound sum equals 2),
          and sufficient (A21) from a constructible CRT terminal-digit star.   OPEN
B = 1  :  (ODD-∞) at cofinally many A ≥ 1 — Baker-free, window A ≲ log₂p_{r+1},
          measured odd density ½ at every fixed level.                         OPEN
```

Both corners remain open and **#269 remains OPEN**; §0's claim ceiling is unchanged. What
wave-8 changes is the shape of the remaining work: the `B = 1` corner no longer needs a
transcendence input or a constant-level miracle, and the `B > 1` corner is now a construction
problem with a finite certificate rather than a randomness assertion.

---

## §15. Wave-9: a divisor-pairing parity anchor for (R1)

Second assimilation pass. §14 corrected the campaign's framing; this section adds new
mathematics on the `B = 1` side. Verifiers: `wave8_typeb_assimilation/{pairing,pairing2,pairing3,
pairing4,ladder,ladder2,offsets}.py`, same certified-bracket discipline as §14.

**#269 remains OPEN and so does (R1).** What is new is the corpus's **first unconditional
parity theorem** in this lane: every previous parity statement here is a measurement (§11's
density scans), a conditional transport (§12 Lemma S, §14 A18), or an orbit conjecture (§13).
Grepping this document and `research_packet.json` for `divisor` / `involution` / `pairing` /
`perfect square` returns one unrelated hit, so the mechanism below is new here.

### 15.1 Theorem P

> **A23 — Theorem P (PROVED-HERE).** Let `i, j ≥ 0` be integers, `c = iα + jβ`, `w > 0`, and
> suppose
> ```
> (B1_w)   jβ ≤ iα + α − w ,        (B2_w)   iα ≤ jβ + β − w .
> ```
> Then `#{(u,v) ∈ ℤ²_{≥0} : |uα + vβ − c| < w}` is **ODD**.

*Proof.* Write `x = 3^i5^j`, so `N := x² = 3^{2i}5^{2j}` is a **perfect square**. Let `S` be the
set and `σ(u,v) = (2i−u, 2j−v)` — multiplicatively `d ↦ N/d`.
*σ stays in the quadrant.* If `u ≥ 2i+1` then `(2i+1)α ≤ uα + vβ < c + w = iα + jβ + w`, giving
`iα + α < jβ + w`, contradicting `(B1_w)`; so `u ≤ 2i`, and `v ≤ 2j` by `(B2_w)`.
*σ preserves S.* `h(σ(u,v)) = 2c − h(u,v)`, so `|h(σ) − c| = |h − c| < w`.
*σ is an involution with one fixed point.* `σ(u,v) = (u,v) ⟺ (u,v) = (i,j)`, and `(i,j) ∈ S`
since `|c − c| = 0 < w`. Every other point is in a 2-cycle. ∎

The balance hypothesis is exactly "every smooth number within a factor `2^w` of `x` divides
`x²`". It is **load-bearing, not cosmetic**: over `i,j ≤ 25`, the 643 *unbalanced* pairs split
313 odd / 330 even. **VERIFIED-COMPUTATIONALLY**: `w = 1/2`, all 212 balanced pairs with
`i,j < 170` (`max |S| = 145`), **0 even**; plus 22 general-`w` instances in the large scan, 0 even.
Every predicate is the integer test `x² < 2y²` and `y² < 2x²`.

### 15.2 Transfer to a dyadic shell, and the exact alignment obstruction

Put `K = ⌊c − ½⌋` and `off := c − K − ½ ∈ [0,1)`. Choosing `w = c − K` puts the **left endpoint
exactly on the integer `K`**, so the window is `(K, K+1+2·off)` and it contains all of shell `K`:

> **A24 (PROVED-HERE).** Under `(B1_w),(B2_w)` with `w = c − K`,
> ```
> s(K) ≡ 1 + E   (mod 2),      E := #{ y smooth : K + 1 ≤ log₂ y < K + 1 + 2·off } .
> ```
> Hence **`E = 0 ⟹ s(K) is ODD`**, with no hypothesis of any kind.

(The `w = ½` form gives the two-sided variant `s(K) ≡ 1 + E₁ + E₂` with edges of width `off` at
`K` and `K+1`; both are verified, 0 violations, and agree as they must.)

> **A25 — the alignment obstruction (PROVED-HERE).** `E = 0` is *forced* only when the anchor is
> exactly aligned, `c = K + ½`, i.e. `3^{2i}5^{2j} = 2^{2K+1}` — **impossible by unique
> factorization**. Quantitatively, `A17` makes the edge provably empty only for
> `off ≲ 2^{−K}`, while `off` over anchors of size `n` is bounded below by a *polynomial* in
> `1/n` (three-distance). The gap is exponential, so no choice of `(i,j)` forces `E = 0`.

So the natural parity anchor exists but is **misaligned with the dyadic grid by an `O(1)`
amount that cannot be removed**. That is a clean structural reason (R1) resists: the divisor
involution lives on the `√N`-centred window, and the dyadic shell is not one.

### 15.3 What the anchors actually deliver, measured

**The anchor family is thin but regular.** Over `i < 6000`: 7 511 balanced anchors, `K ≤ 19 015`,
**exactly one anchor per covered level**, covering `39.5%` of levels. Their offsets are
**equidistributed** — decile histogram `747, 757, 746, 753, 747, 755, 748, 753, 749, 756`.

**The corollary is not a general complexity reduction.** Over 162 levels to `K = 408`,
`mean E₁ = 29.2`, `mean E₂ = 29.0` against `mean s(K) = 56.2` — the edge terms are as large as
the shell they are meant to decide. A24 bites only when `off` is small, i.e. `off ≲ g_K`, the
log-gap above `2^K` (`g_K ≈ 3.7/K`).

**Five unconditional certificates.** Exhaustive search over all balanced anchors to `K ≈ 19 000`
found `E = 0` exactly five times:

| `K` | `(i,j)` | `s(K)` | `off` |
|---|---|---|---|
| 1 | (1,0) | 1 | `8.50×10⁻²` |
| 41 | (13,9) | 13 | `1.87×10⁻³` |
| 124 | (39,27) | 35 | `5.60×10⁻³` |
| 254 | (80,55) | 69 | `3.05×10⁻³` |
| 384 | (121,83) | 105 | `4.95×10⁻⁴` |

At those five levels, `s(K)` is **proved odd by divisor pairing** rather than by counting the
shell. The last four form a **ladder**: the step is `(41,28)`, i.e. `3^41 5^28 ≈ 2^130`
(`ΔK = 130` twice), and the offset drifts by `−2.55×10⁻³` per rung — which is why the ladder
tightens (`5.60 → 3.05 → 0.49 ×10⁻³`) and then must break when the offset changes sign.

**Rate.** `E = 0` needs `off < g_K` with both `≍ 1/K`; with `0.4` anchors per level and the
two-sided edge width this predicts `≈ 0.74·ln X` hits below `X`, i.e. `7.0` over the scanned
range against **5 observed** — unremarkable for a Poisson count. The first heuristic written
here predicted `14` by forgetting that emptiness is required across the *whole* edge; the
corrected constant is the one above.

### 15.4 The new terminal formulation

> **(ANCHOR-∞) (OPEN).** There are infinitely many balanced pairs `(i,j)` whose edge interval
> `[K+1, K+1+2·off)` contains no `{3,5}`-smooth number.
>
> **(ANCHOR-∞) ⇒ (R1).** Immediate from A24: each such pair proves `s(K)` odd, at levels
> `K → ∞`. **PROVED-HERE.**

This is **not** §13's residue and not §14's (ODD-∞). Those ask for an Ostrowski/Birkhoff
evaluation of one specific orbit in a non-bounded-remainder arc, and nothing is ever certified
along the way. (ANCHOR-∞) is a two-sided shrinking-target statement — `off` against `g_K`, two
`≍1/K` quantities — and **each success is a finite, self-contained, unconditional certificate**.
Five are exhibited above. Whether the equidistribution of `off` (measured flat) is asymptotically
independent of the gap sequence `g_K` is precisely the open point.

**Ceiling.** A23–A25 are proved and verified; (ANCHOR-∞) is open; (R1) is open; the `B > 1`
corner is untouched by this section; **Erdős #269 remains OPEN.**

---

## Correction, 2026-09-06: two numbers and one label

**1. The continued-fraction exponent in §7.2.** The retired-route table row
"Metric / statistical (equidistribution of `{X_a}`)" reads "13 109 certified
partial quotients, Gauss–Kuzmin on target, exponent 2.005, largest p.q.
129 114". The figure `2.005` is wrong. The authoritative block
`public-source-redacted://state/probes/erdos269_continued_fraction_receipt.json#result`
records `irrationality_exponent_proxy_max = 2.04373` and
`irrationality_exponent_proxy_tail_max = 1.00096`, with 13,109 certified
partial quotients, largest denominator 22,483 bits, largest partial quotient
129,114, mean partial quotient 23.4133 and Lévy constant 1.18869 against
1.18657.

`2.005` comes from `experiment_contract.result.summary` in the same receipt
file, which is a stale block from an earlier and smaller run: it reports 2,162
certified partial quotients, Gauss–Kuzmin frequencies 0.4265/0.1651/0.0888/0.0587,
Lévy constant 1.19749 and a denominator floor of `2^3737`. That block
contradicts the `result` block beside it. Every figure quoted for this probe
should come from `result`, and the exclusion figure is `2^22482`, about
`10^6768`. The row's other four figures are correct; only the exponent changes,
and the retirement it supports is unaffected.

**2. The stammering row in the same table.** The row reads "Period must serve
both Sturmian slopes at once ⇒ needs simultaneous exponent 1; Dirichlet in dim 2
caps at 1/2." Dirichlet in dimension two is an existence guarantee: for every
slope pair there are infinitely many `q` with
`max(‖qα‖, ‖qβ‖) ≤ q^{-1/2}`. It places no upper bound on how well
`(log_3 2, log_5 2)` can be approximated, so it caps nothing. The retirement is
carried by the measurement alone, whose margin is a full power `q^{1/2}`, and
its correct label is `empirical_deprioritisation` rather than a proved closure.
The full argument is in the 2026-09-06 correction block appended to
`TorusCocycleAndDiophantineTypeLab.md`. Note the coupling with §7.1 of this
file: `research_packet.json` `negative_results[19]` states the same retirement
with the clause "two rationally independent slopes", and §7.1 records that the
independence of `1, θ₃, θ₅` is a four-exponentials instance and **OPEN**.

**3. §7.1 is the load-bearing record for a separate repair.** The sentence
"That independence is not unconditional" and the `[P1′]` repair note, which
replaces the Weyl step by minimality on the orbit closure, are the correct
treatment. The same repair shape has now been applied to
`PurePowerIrrationalityNote.md`, whose §2 used full-torus density directly; see
the 2026-09-06 correction block there. §A8 caution (a) of this file already
draws the right line and needs no change: the **upper** bound `≤ (L+1)²` is
unconditional, and only the claim that the count is exactly `(L+1)²`, or that
`(s₃,s₅)` equidistributes for product Haar measure, needs the independence. The
`P`-class chain of A7 uses none of it, so the block programme's critical path is
untouched by all of the above.
