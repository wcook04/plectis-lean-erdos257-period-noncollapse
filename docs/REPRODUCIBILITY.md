<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reproduce the public release

This page is the clean-clone runbook for the standalone
[`plectis-erdos`](https://github.com/wcook04/plectis-erdos)
repository. It uses only files in this checkout and ordinary public tools. The
private `ai_workflow` repository, a sibling checkout, an inherited shell state,
and a pre-existing build cache are not prerequisites.

## 1. Start with a complete committed checkout

Use a full clone when following source coordinates or any gate that compares
the pinned history. A shallow clone is intentionally an environment with
insufficient history; `verify_claims.py` reports that condition separately
and exits `2` rather than presenting it as a mathematical failure.

```sh
git clone --filter=blob:none https://github.com/wcook04/plectis-erdos.git
cd plectis-erdos
git fetch --tags --force
git status --short
```

The blob filter retains the complete commit and tag graph required by the
pinned-history gates, but downloads old file bodies only if a later command
actually reads them. It does not make the clone shallow. This matters because
the current checkout is hundreds of megabytes while historical generated
projections are much larger; eagerly transferring every obsolete body does not
strengthen any proof or release check.

Run the following static, no-Lean first impression. These commands use the
committed Python and JSON surfaces and do not need Lake, elan, or Mathlib:

```sh
python3 -VV
python3 scripts/test_dependency_lock_contract.py
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/build_module_graph.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/test_downstream_example_contract.py
python3 scripts/query_corpus.py --tour --format card
```

The quick check is a bounded navigation check, not a proof build. It confirms
that the eight-problem entry surface, both public Lean roots, claim/source
routes, paper handles, open-boundary routes, and environment guidance are
present before any toolchain download. Its semantic-corpus freshness step uses
the tracked content-addressed receipt in `docs/semantic_corpus_check.json`, so
an unchanged clone hashes the relevant inputs and outputs instead of rebuilding
the 153,000-declaration projection. Use
`python3 scripts/build_semantic_corpus.py --check --full-check` when a full
in-memory rebuild is the thing being tested.

Before installing or building anything, a reader can return from any indexed
problem to its public evidence with the same no-build query surface:

```sh
python3 scripts/query_corpus.py --route erdos_<n>
# <n> is one of 68, 243, 249, 251, 257, 269, 1041, or 1049
```

The packet identifies the problem-owned note, formal directory, module
inventory, and open-obligation handles. Expand the matching row in
[`docs/problems.json`](problems.json) to read its complete `what_is_checked`
result inventory and `what_is_not_checked` evidence ceiling, then follow the
exact paper/source and frontier joins described in
[`docs/SEMANTIC_COMPILER.md`](SEMANTIC_COMPILER.md).
This route is navigation evidence only: the Lean kernel remains proof
authority and every problem-level open boundary remains open.

## 2. Reproduce the pinned Lean environment

Install [elan](https://leanprover-community.github.io/get_started.html) once
using its documented installer. From the repository root, elan reads
[`lean-toolchain`](../lean-toolchain), which selects
`leanprover/lean4:v4.29.1`; [`lake-manifest.json`](../lake-manifest.json)
pins the Mathlib revision and its transitive dependencies.

```sh
lake --version
python3 scripts/test_dependency_lock_contract.py
python3 -m pip install --disable-pip-version-check --no-cache-dir --require-hashes \
  --requirement requirements-release.txt
lake exe cache get
```

The cache command is optional for correctness but avoids recompiling Mathlib
from source. It may download several gigabytes. A cache is an acceleration,
not authority: the toolchain file and manifest are the reproducibility inputs.

Check one real published theorem module first. This is the short feedback path
for confirming that the toolchain, dependency cache, and project all work:

```sh
python3 scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems.Erdos249.PeriodMultipleEscape
```

For a complete release replay, build the two supported public roots and the
explicitly supported non-default consumers through one host-shared wrapper
invocation:

```sh
python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness \
  Erdos249257 ErdosProblems Examples FormalConjecturesAdapter \
  FormalConjecturesVariants ResidualBench
python3 scripts/build_lean_dependency_index.py --check --full-check
```

`Erdos249257` and `ErdosProblems` are the default library targets. `Examples`
is a downstream consumer and is deliberately not a default target. The other
targets are separate adapter, variant, and residual-check surfaces; their
declarations do not enlarge the reviewed mathematical corpus. Keeping all six
targets behind the wrapper gives the clean clone one bounded scheduler owner,
one dependency plan, and the same host-wide duplicate-build suppression used
by focused replay and CI.

Both commands automatically enter the tracked public singleflight scheduler.
On one host, identical source/toolchain requests from separate clones join the
same future, while different Lean validations serialize behind one heavy-build
lock. The heavy lock is host-wide and intentionally lives above any repository
slug, so public cold clones and other cooperating Plectis checkouts queue before
Lake starts rather than discovering contention through SIGTERM. State defaults
to the platform cache directory under the public repository identity, not to
the checkout. The cache retains bounded log tails
and launches hourly terminal-state cleanup; it is disposable acceleration and
never substitutes for the recorded Lake exit code. Lean keys cover every
visible Lean source plus their toolchain and build
authorities rather than the entire Git tree, so unrelated paper or README edits
do not force a duplicate proof build. A successful owner publishes a bounded
copy-on-write `.lake/build` seed keyed by those exact inputs. An equivalent
clone hydrates that seed before accepting the terminal receipt, so reuse means
the caller has local build outputs rather than only a cached success status.
To submit without attaching the current shell, use:

```sh
python3 scripts/validation_singleflight.py submit --class lean \
  --target ErdosProblems.Erdos249.PeriodMultipleEscape
```

The admitted owner also manages a same-lock dependency seed through
`scripts/lean_package_share.py`. On APFS (or a Linux filesystem supporting
reflinks), each clone keeps an independent `.lake/packages` path while
unchanged files share physical blocks. The first healthy checkout publishes
the host seed; later cold clones attach before building. The lane rejects dirty
dependency repositories and mutable-cache symlinks and never falls back to a
full byte-for-byte copy. Unsupported filesystems simply retain ordinary local
Lake behavior. Successful macOS builds also compact large repeated
`*.setup.json` manifests with transparent filesystem compression after checking
byte identity and source stability. Only the current and one previous semantic
package seed are retained.

Build-output sharing follows the same no-symlink, no-full-copy rule and keeps
only the two newest semantic seeds. Existing checkout outputs are preserved;
matching files are updated by reflink under the same host-wide Lean lock.
Unsupported filesystems fail closed for cross-clone receipt reuse and retain
ordinary local build behavior.

`run` is the corresponding submit-or-join-and-collect command. A later caller
with the same semantic key reuses the in-flight or completed receipt; no human
retry is needed to preserve the detached owner. If the host sends SIGTERM or
SIGKILL, that owner resumes partial build output automatically for up to three
attempts; exhaustion is recorded as deferred exit 75, not a theorem failure.
`PLECTIS_LEAN_HOST_LOCK_ROOT` can relocate the cross-repository lock namespace
for a container or CI worker; all cooperating processes on that host must use
the same value.

The module's `pureDyadicEndpointError_succ` identity gives the endpoint-error
cocycle; `prime_forces_pureDyadicEndpointError_excursion` and
`exists_late_pureDyadicEndpointError_excursion` expose the adjacent-error
excursion forced by arbitrarily late prime positions. The directional
`prime_successor_upper_trap_forces_bottom_lock` and its cofinal companion
record the additional constraint under an upper-trap hypothesis. These are
source-level constraints, not reviewed external-verification interfaces: they
do not supply the actual-series-to-orbit bridge or prove Erdős #249
irrationality, and the open endpoint remains open.

## 3. Run the release-surface checks

These checks are ordered from cheap source/navigation checks to the broader
release gate. They remain repository-local and do not require the private
factory:

```sh
python3 scripts/check_release.py
python3 scripts/test_projection_checkout_independence.py
python3 scripts/test_root_import_closure.py
python3 scripts/test_check_release_ref.py
```

The clean-ref wrapper is the later immutable-snapshot gate. It resolves one
commit, creates a disposable local clone, and runs the configured release
checks there; uncommitted files in the caller's checkout are excluded. A
bounded snapshot probe can verify that preparation without replaying the full
gate:

```sh
python3 scripts/check_release_ref.py --ref HEAD --probe-only
```

Do not read a successful static check as a terminal release clearance. The
final release pair still requires one clean immutable SHA and the separately
managed terminal Palomar and Comparator receipts. Those gates may be
resource-intensive and are not substituted by this runbook.

## 4. Reproduce a changed checkout safely

Keep generated projections in dependency order. After changing an owning
source, use its builder and then its `--check` mode; do not hand-edit a
generated JSON or Markdown projection. Before a scoped commit, confirm that
the worktree contains no unrelated path changes and that every claimed path
is clean after landing.

The supported command vocabulary is intentionally environment-neutral:

```sh
python3 scripts/build_corpus_descriptor.py --check
python3 scripts/build_module_graph.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/build_lean_dependency_index.py --check
```

If a command reports stale generated output, regenerate from the named owning
builder and commit the source plus all projections that builder declares. Do
not copy files from another checkout or rely on a developer's `.lake` state.
The ordinary dependency-index `--check` never compiles; an intentional release
export uses `--check --full-check` after the coordinated Lean build above.

## Resource and boundary notes

- Python-only navigation is the fast cold-clone path; Python `3.11+` is
  required by the repository's TOML and standard-library interfaces.
- The pinned Mathlib cache is large. Allow the cache download and the Lean
  build their documented time and disk budget; `--jobs 2` is the supported
  bounded local build setting.
- `lake build` proves the checked Lean targets, not the open Erdős problems.
  The public claim registry and papers retain the exact conditional results
  and open boundary.
- `docs/problems.json`, `docs/claims.json`, the paper corpus, and the
  generated declaration/dependency projections are public evidence surfaces;
  this runbook describes how to replay them and is not proof authority.
