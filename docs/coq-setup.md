# Coq/Rocq Setup for Verina

This document describes how to set up the Coq environment for running Verina benchmarks with Coq/Rocq.

## Docker Setup (Recommended)

The easiest way to run Coq benchmarks is using Docker. This provides a consistent environment with Coq 8.18 and QuickChick pre-installed.

### Building the Docker Image

```bash
docker build -f docker/Dockerfile.coq -t verina-coq .
```

### Verifying the Installation

```bash
# Check Coq version
docker run --rm verina-coq coqc --version

# Test compilation
docker run --rm -v "$(pwd):/workspace" verina-coq coqc /workspace/datasets/verina/verina_basic_1/task.v
```

### Manual Compilation

To compile a single Coq file:

```bash
docker run --rm -v "$(pwd):/workspace" verina-coq coqc /workspace/path/to/file.v
```

## Running Coq Benchmarks

### Configuration

Create a TOML config file with `itp_type = "coq"`. Example (`configs/coq_baseline.toml`):

```toml
output_dir = "output/coq-baseline"
max_workers = 16
rounds = 1
itp_type = "coq"

code_gen = true
spec_gen = true
proof_gen = true

[gen_lm_config]
provider = "anthropic"
model_name = "claude-sonnet-4-5-20250929"

[coq_config]
use_quickchick = true
quickchick_num_tests = 1000
docker_image = "verina-coq"
```

### Running the Benchmark

```bash
# Full benchmark
uv run python scripts/benchmark.py --config configs/coq_baseline.toml

# Limited run (for testing)
uv run python scripts/benchmark.py --config configs/coq_baseline.toml --limit 10
```

### Analyzing Results

```python
from pathlib import Path
from src.verina.benchmark.summary import EvaluationRoundsReport, DatapointSummaryReport

output_dir = Path("./output/coq-baseline")
report = EvaluationRoundsReport.load_latest(output_dir)
summary = DatapointSummaryReport.from_rounds_report(report)

print("pass@1:", summary.pass_at_k(1))
```

## Coq Test Files

Each task directory contains Coq-specific files:

- `task.v` - Main Coq task file with benchmark markers
- `task.json` - Contains `coq_signature` with Coq types
- `coq_test.json` - Unit tests in Coq syntax
- `coq_reject_inputs.json` - Rejection tests in Coq syntax

### Type Mapping (Lean to Coq)

| Lean Type | Coq Type |
|-----------|----------|
| `Int` | `Z` |
| `Nat` | `nat` |
| `Bool` | `bool` |
| `String` | `string` |
| `Char` | `ascii` |
| `List T` | `(list T)` |
| `Array T` | `(list T)` |
| `Option T` | `(option T)` |
| `A × B` | `A * B` |

## Utility Scripts

### Translate Lean Ground Truth to Coq

Translates Lean code/spec (not proof) to Coq using an LLM:

```bash
uv run python scripts/translate_lean_to_coq.py --help

# Translate all tasks
uv run python scripts/translate_lean_to_coq.py

# Translate specific tasks
uv run python scripts/translate_lean_to_coq.py --filter verina_basic_1,verina_basic_2

# With custom model
uv run python scripts/translate_lean_to_coq.py --model claude-opus-4-5-20251101 --retries 5
```

### Check Signature Alignment

Verifies that `task.json` `coq_signature` matches the signature in `task.v`:

```bash
uv run python scripts/check_coq_signature_alignment.py --help

# Check all tasks
uv run python scripts/check_coq_signature_alignment.py

# Generate report
uv run python scripts/check_coq_signature_alignment.py report --output alignment_report.md
```

### Convert Test Files to Coq Syntax

Converts Lean test JSON to Coq syntax:

```bash
uv run python scripts/convert_tests_to_coq.py --help

# Convert all tasks
uv run python scripts/convert_tests_to_coq.py

# With validation
uv run python scripts/convert_tests_to_coq.py --validate
```

## Troubleshooting

### Docker Build Fails

If the Docker build fails due to opam issues:

```bash
# Clean Docker cache and rebuild
docker build --no-cache -f docker/Dockerfile.coq -t verina-coq .
```

### Compilation Timeout

If compilation times out, increase the timeout in the config or check for infinite loops in the generated code.

### QuickChick Errors

QuickChick requires decidable properties. If you see "Cannot find instance" errors, ensure:
- Preconditions have a `_dec` version returning `bool`
- Postconditions have a `_dec` version returning `bool`
- All types used have decidable equality

## Local Coq Installation (Alternative)

If you prefer a local installation instead of Docker:

```bash
# Install opam (macOS)
brew install opam
opam init

# Install Coq and QuickChick
opam install coq.8.18.0 coq-quickchick

# Verify
coqc --version
```

Then set `docker_image = ""` in your config to use local Coq.
