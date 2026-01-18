#!/usr/bin/env python3
"""Print summary of evaluation results from the latest round report."""

import argparse
from pathlib import Path

from verina.benchmark.report import EvaluationRoundsReport
from verina.benchmark.summary import DatapointSummaryReport


def print_task_summary(output_dir: Path, k: int = 1, overestimate: bool = False) -> None:
    """Print summary of each task from the latest round report.

    Args:
        output_dir: Directory containing round reports
        k: The k value for pass@k calculation (default: 1)
        overestimate: Whether to use overestimate results (default: False)
    """
    # Load the latest rounds report
    rounds_report = EvaluationRoundsReport.load_latest(output_dir)

    if rounds_report is None:
        print(f"No rounds report found in {output_dir}")
        return

    # Create summary report
    summary_report = DatapointSummaryReport.from_rounds_report(rounds_report)

    # Calculate pass@k metrics
    pass_at_k_results = summary_report.pass_at_k(k=k, overestimate=overestimate)

    # Print summary
    print(f"\n{'='*80}")
    print(f"Summary of Evaluation Results (pass@{k})")
    print(f"Output Directory: {output_dir}")
    print(f"Number of Rounds: {len(rounds_report.rounds)}")
    print(f"Overestimate: {overestimate}")
    print(f"{'='*80}\n")

    # Print results for each task
    for task_name in sorted(pass_at_k_results.keys()):
        print(f"\nTask: {task_name}")
        print("-" * 60)

        metrics = pass_at_k_results[task_name]
        for metric_name in sorted(metrics.keys()):
            score = metrics[metric_name]
            print(f"  {metric_name:30s}: {score:.3f} ({score*100:.1f}%)")

    print(f"\n{'='*80}\n")


def main():
    parser = argparse.ArgumentParser(
        description="Print summary of evaluation results from the latest round report"
    )
    parser.add_argument(
        "output_dir",
        type=Path,
        help="Directory containing round reports (rounds_report_*.json files)",
    )
    parser.add_argument(
        "-k",
        type=int,
        default=1,
        help="The k value for pass@k calculation (default: 1)",
    )
    parser.add_argument(
        "--overestimate",
        action="store_true",
        help="Use overestimate results",
    )

    args = parser.parse_args()

    print_task_summary(args.output_dir, k=args.k, overestimate=args.overestimate)


if __name__ == "__main__":
    main()
