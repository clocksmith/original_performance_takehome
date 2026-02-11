import subprocess
import sys

def run_search(width, n_ops, timeout):
    print(f"\n--- Searching for {n_ops}-op hash at {width} bits ---")
    cmd = [
        "./.venv/bin/python", "scripts/superopt_myhash.py",
        "--n-ops", str(n_ops),
        "--width", str(width),
        "--init-samples", "128",
        "--max-iters", "100",
        "--synth-timeout-ms", str(timeout),
        "--verify-timeout-ms", str(timeout),
        "--two-reg",
        "--shift-src-val",
        "--shift-dst-tmp",
        "--muladd-dst-val"
    ]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout//1000 + 60)
        print(result.stdout)
        if "FOUND" in result.stdout:
            return True
    except subprocess.TimeoutExpired:
        print("Subprocess timed out.")
    return False

# Try 11 ops
if run_search(8, 11, 60000):
    print("Found 11-op candidate at 8 bits!")
else:
    print("No 11-op candidate at 8 bits.")
    run_search(8, 12, 60000)