Full verification runs in the private `Niklas-Fraccaro/sixth-moment-lean` copy.
The personal repository is retained.

Run **Actions → Lean full verification → Run workflow**:

- `smoke`: three short jobs testing real Lean builds, error detection, process-group
  termination, checkpoint transfer, and reuse on fresh runners. Two project modules only.
- `full`: all project modules, then `SixthMoment/Verification/Final.lean`.
  The theorem still assumes `DivisorProof.Watt41`.

Only standard `ubuntu-24.04` runners are used. Up to eight sequential segments run
for at most 330 minutes each, plus a five-minute result job: **2,645 minutes maximum**.
Setup, uploads, and checkpoint creation are included in each segment's time limit.
Build work stops 285 minutes after segment start to reserve time for saving.
There are no automatic triggers, retries, or paid-runner fallbacks.

Keep the organization's Actions budget at **$0 with stop usage enabled**. Included
minutes must cover the run; other workflows consume the same monthly allowance.
An exhausted allowance stops work rather than permitting paid overage.

Each segment uses an isolated pinned toolchain, one Lean compiler at a time, and
8 GiB additional swap. The first segment fetches dependency caches only. Project
artifacts come exclusively from preceding segments of the same run and commit;
all checkpoint files are hashed and verified before extraction.

Checkpoints are capped at 900 MiB and retained for seven days. A preceding checkpoint
is deleted only after its replacement uploads successfully. Logs and source hashes
are retained for 30 days. Download the run's `full-evidence-*` and `full-result-*`
artifacts for a permanent record; the source is identified by the exact commit.

Any build, verification, checkpoint, or transfer failure stops the chain. If all
eight segments finish without completing verification, the result is a failure
and the latest checkpoint remains available. A green smoke test is not a full proof run.
