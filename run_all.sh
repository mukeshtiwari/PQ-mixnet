#!/usr/bin/env bash
# run_all.sh -- rebuild and re-verify the handed-off state on this machine.
#
#   ./run_all.sh smoke   build, native self-tests, size model against the recorded proof sizes   (under a minute)
#   ./run_all.sh         smoke + full Python test suites + native/Python cross-check, in both
#                        proximity regimes                                                       (about 2 minutes)
#   ./run_all.sh bench   all of the above + native benchmarks at 256, 1024 and 4096 ballots      (about 4 minutes, ~1.5 GB RAM)
#
# Environment:  PYTHON (default python3),  CXX (default c++),
#               FP_NO_OPENSSL=1 forces the built-in SHA-256 (slower; timings then differ from Handoff.md).
# Needs: Python >= 3.9 (standard library only), a C++20 compiler with __int128 (g++ or clang++),
#        and, optionally, the OpenSSL headers.
set -euo pipefail
cd "$(dirname "$0")/Unverified"      # the Python and C++ code; logs go to ../results
MODE="${1:-full}"
case "$MODE" in smoke|full|bench) ;; *) echo "usage: $0 [smoke|full|bench]"; exit 2 ;; esac
PY="${PYTHON:-python3}"; CXX="${CXX:-c++}"
export LOG="$(cd .. && pwd)/results/run-$(date +%Y%m%d-%H%M%S)"; mkdir -p "$LOG"
say() { printf '\n== %s\n' "$*"; }
"$PY" -c 'import sys; assert sys.version_info >= (3, 9), "Python 3.9 or newer is required"'

say "build mixnative"
SSL=""
if [ -z "${FP_NO_OPENSSL:-}" ]; then
  if command -v pkg-config >/dev/null 2>&1 && pkg-config --exists libcrypto 2>/dev/null; then SSL="$(pkg-config --cflags --libs libcrypto)"
  elif command -v brew >/dev/null 2>&1 && brew --prefix openssl@3 >/dev/null 2>&1; then P="$(brew --prefix openssl@3)"; SSL="-I$P/include -L$P/lib -lcrypto"
  else SSL="-lcrypto"; fi
fi
compile() {   # $1 = architecture flag, $2 = extra define, $3 = link flags
  # shellcheck disable=SC2086
  "$CXX" -O3 $1 -std=c++20 -Wno-deprecated-declarations $2 mixnative.cpp $3 -o mixnative >>"$LOG/build.log" 2>&1
}
SHA=""
if [ -n "$SSL" ]; then
  if compile "-march=native" "" "$SSL" || compile "" "" "$SSL"; then SHA="OpenSSL"; fi
fi
if [ -z "$SHA" ]; then
  if compile "-march=native" "-DFP_PORTABLE_SHA256" "" || compile "" "-DFP_PORTABLE_SHA256" ""; then
    SHA="built-in (slower: install the OpenSSL headers to compare timings with Handoff.md)"
  fi
fi
[ -n "$SHA" ] || { echo "build failed, see $LOG/build.log"; exit 1; }
echo "compiler: $("$CXX" --version | head -1)"
echo "SHA-256:  $SHA"

say "native self-tests"
./mixnative selftest | tee "$LOG/selftest.log"
./mixnative checkC | tee -a "$LOG/selftest.log" | tail -1
./mixnative checkG | tee -a "$LOG/selftest.log" | tail -1
if ./mixnative decprove 16 32 4 5 0 0 128 6 >"$LOG/decprove.log" 2>&1 && grep -q "negative checks rejected: 4/4" "$LOG/decprove.log"; then
  echo "decprove: native decryption proof accepted, size model exact, 4/4 negative checks rejected"
else echo "native decryption proof FAILED, see $LOG/decprove.log"; exit 1; fi

say "size model against the recorded proof sizes (expected.json)"
"$PY" - <<'EOF' | tee "$LOG/sizes.log"
import json, os, subprocess, sys
exp = json.load(open("expected.json")); ok = True
code = ("from mix_proof import mix_size_model\nimport json, sys\n"
        "for c in json.loads(sys.argv[1]): print(sum(mix_size_model(4096, c[0], c[1], c[2])))")
for regime, cases in exp["native_proof_bytes"].items():
    out = subprocess.run([sys.executable, "-c", code, json.dumps(cases)], env=dict(os.environ, FP_PROX_DIV=regime),
                         capture_output=True, text=True, check=True).stdout.split()
    for c, got in zip(cases, out):
        good = int(got) == c[3]; ok &= good
        print(f"regime {regime}: {c[0]:5d} ballots, C1={c[1]:6d}, C2={c[2]:5d}: model {got} bytes, recorded {c[3]}: {'ok' if good else 'DIFFERENT'}")
sys.exit(0 if ok else 1)
EOF

run_suite() {   # $1 = regime, $2 = script, $3 = line that must appear in its output
  local log="$LOG/${2%.py}.prox$1.log"
  if FP_PROX_DIV=$1 "$PY" "$2" >"$log" 2>&1 && grep -q "$3" "$log"; then echo "$2: $3"
  else echo "$2 FAILED in regime $1, see $log"; exit 1; fi
}
if [ "$MODE" != smoke ]; then
  for pd in 3 2; do
    say "Python test suites and native/Python cross-check, FP_PROX_DIV=$pd"
    run_suite $pd mix_proof.py "all checks passed"
    run_suite $pd dec_proof.py "all checks passed"
    run_suite $pd cross_check.py "cross-check passed"
  done
fi

if [ "$MODE" = bench ]; then
  say "native benchmarks: N = 4096, 128-bit parameters, one thread"
  "$PY" - <<'EOF' | tee "$LOG/bench.log"
import json, os, re, subprocess, sys
exp = json.load(open("expected.json")); ok = True
print(f"{'regime':>6} {'ballots':>8} {'prove ms/ballot':>16} {'verify ms/ballot':>17} {'proof bytes':>12} {'peak MB':>8}  check")
for regime, cases in exp["native_proof_bytes"].items():
    for tau, C1, C2, size in cases:
        out = subprocess.run(["./mixnative", "prove", "4096", str(tau), str(C1), str(C2), "128", "11"],
                             env=dict(os.environ, FP_PROX_DIV=regime), capture_output=True, text=True).stdout
        open(os.path.join(os.environ["LOG"], f"bench.prox{regime}.tau{tau}.log"), "w").write(out)
        g = lambda pat: re.search(pat, out)
        pr = g(r"PROVE [\d.]+s\s+\(([\d.]+) ms"); ve = g(r"VERIFY [\d.]+s\s+\(([\d.]+) ms per ballot\)\s+-> accepted")
        pb = g(r"proof (\d+) bytes"); pm = g(r"peak memory (\d+) MB"); neg = g(r"negative checks rejected: 4/4")
        good = bool(pr and ve and pb and neg) and int(pb.group(1)) == size; ok &= good
        f = lambda mo: mo.group(1) if mo else "?"
        print(f"{regime:>6} {tau:>8} {f(pr):>16} {f(ve):>17} {f(pb):>12} {f(pm):>8}  {'ok' if good else 'FAILED'}", flush=True)
sys.exit(0 if ok else 1)
EOF
  say "native decryption benchmarks: N = 4096, 128-bit parameters, noise range 2^56, one thread"
  "$PY" - <<'EOF' | tee "$LOG/decbench.log"
import os, re, subprocess, sys
ok = True
print(f"{'ballots':>8} {'digits':>12} {'prove ms/ballot':>16} {'verify ms/ballot':>17} {'proof bytes':>12} {'peak MB':>8}  check")
for tau in (256, 1024):
    for base, kd in ((4, 28), (16, 14)):
        out = subprocess.run(["./mixnative", "decprove", "4096", str(tau), str(base), str(kd), "0", "0", "128", "11"], capture_output=True, text=True).stdout
        open(os.path.join(os.environ["LOG"], f"decbench.tau{tau}.base{base}.log"), "w").write(out)
        g = lambda pat: re.search(pat, out)
        pr = g(r"PROVE [\d.]+s\s+\(([\d.]+) ms"); ve = g(r"VERIFY [\d.]+s\s+\(([\d.]+) ms per ballot\)\s+-> accepted")
        pb = g(r"proof (\d+) bytes"); pm = g(r"peak memory (\d+) MB"); ex = g(r"size model \d+: exact"); neg = g(r"negative checks rejected: 4/4")
        good = bool(pr and ve and pb and ex and neg); ok &= good
        f = lambda mo: mo.group(1) if mo else "?"
        print(f"{tau:>8} {str(kd) + ' base-' + str(base):>12} {f(pr):>16} {f(ve):>17} {f(pb):>12} {f(pm):>8}  {'ok' if good else 'FAILED'}", flush=True)
sys.exit(0 if ok else 1)
EOF
fi

say "ALL GOOD ($MODE).  Logs: $LOG"
