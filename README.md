# Verina: Benchmarking Verifiable Code Generation

## Overview

Verina (Verifiable Code Generation Arena) is a high-quality benchmark enabling a comprehensive and modular evaluation of code, specification, and proof generation as well as their compositions.
Read more about the project in our [website](https://verina.io) and [paper](https://arxiv.org/pdf/2505.23135).

## Dataset

See the [datasets/verina](./datasets/verina/) directory for the curated dataset used in the benchmark.
Each datapoint in the dataset is organized as a folder containing the following files:
- `task.json`: A JSON file describing the task, including the id, task signature, paths to necessary data files, and other metadata.
- `description.txt`: The description of programming task.
- `task.lean`: The Lean 4 file containing ground truth code, specification, and proof.
- `test.json` and `reject_inputs.json`: JSON files containing test cases and rejected inputs for the task.

The HuggingFace [dataset](https://huggingface.co/datasets/sunblaze-ucb/verina) is an aggregated dataset exctraced from [`datasets/verina`](./datasets/verina/).
To contribute to Verina, please submit a pull request to this repository.
 
## Prerequisites

- [uv](https://docs.astral.sh/uv/getting-started/installation/)
- [lean](https://docs.lean-lang.org/lean4/doc/quickstart.html)
- docker (optional)

## Setup

```bash
uv sync
source .venv/bin/activate  # Activate the virtual environment created by uv
lake exe cache get
lake update
```

## API Key Configuration

See `.env.example` for the required environment variables.
Run `cp .env.example .env` to create a `.env` file, then fill in your API keys for the language model providers you want to use.
`LANGFUSE` related variables are optional and used for logging the benchmark runs.

## Running Benchmarks on Baselines

### Starting Prefect Server

Before running the benchmarks, start the Prefect server:

```bash
docker compose up -d # This will start the database for prefect in the background
uv run prefect server start
```

The server will be available at http://127.0.0.1:4200 with the API at http://127.0.0.1:4200/api.

### Alternative Setup without Docker

Docker is only needed for setting up a postgres database for Prefect.
If you prefer not to use Docker, you can set up a local PostgreSQL database and update the `database.connection_url` in the `prefect.toml` file to point to your local database.

Alternatively, you can comment out the `database.connection_url` line in `prefect.toml` to use the default SQLite database.
In this case, we do not recommend running the benchmarks with a large amount of workers (e.g. 16 workers).

### Using Configuration Files

Existing configuration files are located in the `configs` directory.
You can create your own configuration file by copying one of the existing files and modifying it as needed.

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
name = "baseline" # Name of the baseline method ["baseline", "proof-refinement"]
resume_from_checkpoint = true # whether to resume from the previous result file
refinements = 64 # Number of refinements to run for the proof refinement baseline
```

### Custom Models

You can use custom models by specifying the `provider` and `model_name` in the `gen_lm_config` section of your configuration file.
Currently supported providers include `openai`, `anthropic`, `vertex_ai`, `together_ai`, and any OpenAI-compatible API endpoints (use `local` provider).
See [`utils/lm.py`](./src/verina/utils/lm.py) for more details.

To add a new provider or new models or to customize hyper-prameters, you can modify the relevent functions in [`utils/lm.py`](./src/verina/utils/lm.py), or use the `local` provider (see [`configs/dsprover2-7b.toml`](./configs/dsprover2-7b.toml) as an example).


### Running Benchmark on Baselines

To run benchmark:

```bash
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/benchmark.py -c configs/[config_name].toml
```

It is faster to run the benchmark by separating the generation and evaluation steps.

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

### Reading Results

The detailed results of the benchmark will be saved in the `output_dir` directory specified in your configuration file, including the generated artifacts and evaluation scores.
You can use the following snippet to obtain a summary of the results:

```python
from pathlib import Path
from src.verina.benchmark.report import EvaluationRoundsReport
from src.verina.benchmark.summary import DatapointSummaryReport

output_dir = Path("<your_output_dir>")
report = EvaluationRoundsReport.load_latest(output_dir)
summary = DatapointSummaryReport.from_rounds_report(report)
print(summary.pass_at_k(1))
```

## Creating Your Own Solution

To create your own solution for the Verina benchmark, you can implement a custom method by inheriting from the `Solution` class in [`benchmark/solution.py`](./src/verina/benchmark/solution.py).
It is easier to start with `SimpleSolution` class which only requires implementing the basic tasks and derives the combined tasks automatically.

The `BaselineSolution` class in [`baseline/baseline.py`](./src/verina/baseline/baseline.py) is a good reference implementation which implements the baseline methods for code, specification, and proof generation.

## FAQs

- How to disable `prefect` caching?

  We recommend specifying a new `output_dir` in your configuration file to avoid caching issues.
  To completely disable caching, you can set the `refresh_cache = true` in `prefect.toml` file.

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

## Citation

```bibtex
@article{ye2025verina,
  title={VERINA: Benchmarking Verifiable Code Generation},
  author={Ye, Zhe and Yan, Zhengxu and He, Jingxuan and Kasriel, Timothe and Yang, Kaiyu and Song, Dawn},
  journal={arXiv preprint arXiv:2505.23135},
  year={2025}
}
```
