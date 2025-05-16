# Verina: Benchmarking Verifiable Code Generation

## Prerequisites

- [uv](https://docs.astral.sh/uv/getting-started/installation/)
- [lean](https://docs.lean-lang.org/lean4/doc/quickstart.html)
- docker

## Setup

```bash
uv sync
```

## API Key Configuration

See `.env.example` for the required environment variables.

## Running Benchmarks with Prefect

### Starting Prefect Server

Before running the benchmarks, start the Prefect server:

```bash
docker compose up -d # This will start the database for prefect in the background
prefect server start
```

The server will be available at http://127.0.0.1:4200 with the API at http://127.0.0.1:4200/api.

### Using Configuration Files

```toml
output_dir = "output/gpt-4o-mini-5rnd"  # Directory where all generated output will be saved
max_workers = 128  # Number of parallel worker tasks to use for generation and evaluation
rounds = 5  # Total number of rounds to run each benchmark task
fewshot_example_names = ["verina_basic_15", "verina_basic_44"]  # Identifiers for example tasks used in few-shot prompting

# Tasks selected to run:
code_gen = false         # Code generation task
spec_gen = false         # Specification generation task
proof_gen = true         # Proof generation task
code_spec_gen = false    # Combined code and specification generation task
code_proof_gen = true    # Combined code and proof generation task
spec_proof_gen = true    # Combined specification and proof generation task
code_spec_proof_gen = true  # Combined code, specification and proof generation task

[gen_lm_config]  # Settings for the language model generation, see utils/lm.py for more details
provider = "openai"     # The language model API provider to use
model_name = "gpt-4o-mini"  # Specific model name for generation

[baseline_config]
name = "baseline" # Name of the baseline method ["baseline", "proof-refinement]
resume_from_checkpoint = true # whether to resume from the previous result file
refinements = 64 # Number of refinements to run for the proof refinement baseline
```

### Running Benchmark

To run benchmark with Prefect:

```bash
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/benchmark.py -c configs/[config_name].toml
```

It is faster to run the benchmarks by separating the generation and evaluation steps.

```bash
# For generation only
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/benchmark.py -c configs/<config_name>.toml --no-eval

# For evaluation only
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/benchmark.py -c configs/<config_name>.toml --no-gen -ew <evaluation_worker_num_override>
```

### Running Quality Assurance

```bash
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/quality_assurance.py -c configs/qa.toml
```

## Development

### Setup

```bash
# pre-commit
pre-commit install
```

### Code Formatting

```bash
# Sort imports
ruff check --select I --fix

# Format code
ruff format
```
