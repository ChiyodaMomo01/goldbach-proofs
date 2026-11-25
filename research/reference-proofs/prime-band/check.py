"""Replay the prime-band reduction. With the repository's Lean cache installed, run this file with python3."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from urllib.request import urlopen


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "lean"
UPSTREAM = "https://raw.githubusercontent.com/CGandGameEngineLearner/goldbach-proofs"
EQUIVALENCE_ID = "L-goldbach-bulk-prefix-equivalence"
GAP_ID = "L-goldbach-bulk-signed-floor"
STATEMENT_SHA = "5cac9d374fe0214eb2fa65bcc0541c9b2dcf3f5f6ad52c7e9f5af0b41e39d37d"
# Hashes recorded in the accepted manifests for the disjointness and cutoff-scale lemmas.
INPUTS = {
    "UpstreamDisjoint": ("93d33090fdfc93fb272dde08cb463f3bff3c64ce", "L_goldbach_arc_disjoint",
                         "e4fa0e9d68118ed961750de4f554996978e49646a49213ae05330d01aef920bc"),
    "UpstreamScale": ("4a29eb4239368944efb5c486fe59e10d85629cbd", "L_goldbach_arc_cutoff_scale",
                      "831e4b6c6e457aefb39e4d95b3d78f264e17bd7dd82ef30c965e381e8239be54"),
}
MODULES = ("BandGeometry", "BandArithmetic", "BandMask", "BandPairs", "BandReduction", "TailPrefixes", "FirstBand", "PeriodicMass")


def verified_input(commit, name, digest):
    path = f"lean/PEqualNP/Outside/{name}.lean"
    result = subprocess.run(["git", "-C", ROOT, "show", f"{commit}:{path}"], capture_output=True)
    if result.returncode == 0:
        data = result.stdout
    else:
        with urlopen(f"{UPSTREAM}/{commit}/{path}", timeout=30) as response:
            data = response.read()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f"Source hash differs from the accepted manifest for {name}")
    return data


def frozen_target(statement):
    if hashlib.sha256(statement.encode()).hexdigest() != STATEMENT_SHA:
        raise ValueError("The registered target has changed. Review the quantifiers and the definitions.")
    definitions, quantifier, _ = statement.rpartition("∀ e:ℝ")
    if not quantifier:
        raise ValueError("Unexpected target quantifier")
    return (
        "import Mathlib\nnamespace FrozenBulk\n"
        f"noncomputable def deskHigh : ℕ → ℕ → ℝ := {definitions}high\n"
        f"noncomputable def deskI : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℂ := {definitions}I\n"
        f"def BulkFloor : Prop := {statement}\nend FrozenBulk\n"
    )


def replay(build):
    def lake(*args):
        return subprocess.check_output(["lake", "env", *args], cwd=LEAN, text=True).strip()

    bin_dir = Path(lake("lean", "--print-prefix")) / "bin"
    env = dict(os.environ, LEAN_PATH=str(build) + os.pathsep + lake("printenv", "LEAN_PATH"))
    for name, source in INPUTS.items():
        (build / f"{name}.lean").write_bytes(verified_input(*source))
    gaps = json.loads((ROOT / "research/gaps.json").read_text())["gaps"]
    statements = {gap["id"]: gap["statement"] for gap in gaps}
    (build / "FrozenBulk.lean").write_text(frozen_target(statements[GAP_ID]))
    theorem = "PEqualNP.Outside." + EQUIVALENCE_ID.replace("-", "_")
    (build / "CatalogueEquivalence.lean").write_text(
        "import TailPrefixes\nset_option autoImplicit false\n"
        f"theorem {theorem} : {statements[EQUIVALENCE_ID]} :=\n"
        f"  GoldbachMinor.catalogue_prefix_loss_iff\n#print axioms {theorem}\n"
    )
    for name in MODULES:
        (build / f"{name}.lean").write_bytes((HERE / f"{name}.lean").read_bytes())
    names = [*INPUTS, "FrozenBulk", *MODULES, "CatalogueEquivalence"]
    for name in names:
        flags = ["-DwarningAsError=true"] if name not in INPUTS else []
        if name in ("FrozenBulk", "CatalogueEquivalence"):
            flags.append("-Dlinter.unusedVariables=false")
        print(f"Compiling {name}", flush=True)
        args = [bin_dir / "lean", *flags, "-R", build, "-o", build / f"{name}.olean", build / f"{name}.lean"]
        subprocess.run(args, cwd=LEAN, env=env, check=True)
    for name in names:
        subprocess.run([bin_dir / "leanchecker", "--verbose", name], cwd=LEAN, env=env, check=True)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="goldbach-prime-band-") as scratch:
        replay(Path(scratch))
