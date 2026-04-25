#!/usr/bin/env python3
import re
import statistics
import subprocess
import sys
from pathlib import Path


REQUIRED_METRICS = (
    "accuracy",
    "cpu_time_per_guess",
    "memory_bytes",
    "score",
)

METRIC_PATTERNS = {
    "accuracy": re.compile(r"^Accuracy:\s*([-+]?\d*\.?\d+(?:[eE][-+]?\d+)?)\s*$", re.MULTILINE),
    "cpu_time_per_guess": re.compile(
        r"^CPU time per guess in seconds:\s*([-+]?\d*\.?\d+(?:[eE][-+]?\d+)?)\s*$",
        re.MULTILINE,
    ),
    "memory_bytes": re.compile(r"^Memory in bytes:\s*([-+]?\d+)\s*$", re.MULTILINE),
    "score": re.compile(r"^Score:\s*([-+]?\d*\.?\d+(?:[eE][-+]?\d+)?)\s*$", re.MULTILINE),
}


def run_command(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
    )


def parse_metrics(output: str, hidden_file: str) -> dict[str, float]:
    parsed: dict[str, float] = {}
    for key in REQUIRED_METRICS:
        match = METRIC_PATTERNS[key].search(output)
        if not match:
            raise ValueError(
                f"Could not parse '{key}' from evaluator output for {hidden_file}.\n"
                f"--- Evaluator output start ---\n{output}\n--- Evaluator output end ---"
            )
        parsed[key] = float(match.group(1))
    return parsed


def summarize_metric(name: str, values: list[float]) -> str:
    return (
        f"{name}: avg={statistics.fmean(values):.6f}, "
        f"min={min(values):.6f}, max={max(values):.6f}"
    )


def main() -> int:
    repo_root = Path(__file__).resolve().parent

    eval_java = repo_root / "EvalHangmanPlayer.java"
    player_java = repo_root / "HangmanPlayer.java"
    words_file = repo_root / "words.txt"
    if not eval_java.exists() or not player_java.exists() or not words_file.exists():
        print(
            "Missing required files. Expected EvalHangmanPlayer.java, HangmanPlayer.java, and words.txt in repo root.",
            file=sys.stderr,
        )
        return 1

    hidden_files = [repo_root / f"hiddenWords{i}.txt" for i in range(1, 101)]
    missing = [str(p.name) for p in hidden_files if not p.exists()]
    if missing:
        print(
            f"Missing hidden word files ({len(missing)}): {', '.join(missing)}",
            file=sys.stderr,
        )
        return 1

    print("Compiling HangmanPlayer and EvalHangmanPlayer...")
    compile_result = run_command(["javac", "HangmanPlayer.java", "EvalHangmanPlayer.java"], repo_root)
    if compile_result.returncode != 0:
        print("Compilation failed:", file=sys.stderr)
        print(compile_result.stdout, file=sys.stderr)
        print(compile_result.stderr, file=sys.stderr)
        return compile_result.returncode or 1

    all_results: list[tuple[str, dict[str, float]]] = []

    for idx, hidden_path in enumerate(hidden_files, start=1):
        print(f"[{idx:03d}/100] Evaluating {hidden_path.name}...")
        run_result = run_command(
            ["java", "EvalHangmanPlayer", "words.txt", hidden_path.name],
            repo_root,
        )
        if run_result.returncode != 0:
            print(f"Evaluation failed for {hidden_path.name}:", file=sys.stderr)
            print(run_result.stdout, file=sys.stderr)
            print(run_result.stderr, file=sys.stderr)
            return run_result.returncode or 1

        metrics = parse_metrics(run_result.stdout, hidden_path.name)
        all_results.append((hidden_path.name, metrics))

    accuracy_values = [entry[1]["accuracy"] for entry in all_results]
    speed_values = [entry[1]["cpu_time_per_guess"] for entry in all_results]
    memory_values = [entry[1]["memory_bytes"] for entry in all_results]
    score_values = [entry[1]["score"] for entry in all_results]

    best_name, best_metrics = max(all_results, key=lambda item: item[1]["score"])

    print("\n=== Aggregate Results (hiddenWords1..hiddenWords100) ===")
    print(summarize_metric("Accuracy", accuracy_values))
    print(summarize_metric("CPU time per guess (seconds)", speed_values))
    print(summarize_metric("Memory (bytes)", memory_values))
    print(summarize_metric("Score", score_values))
    print(
        "Best score run: "
        f"{best_name} "
        f"(score={best_metrics['score']:.6f}, "
        f"accuracy={best_metrics['accuracy']:.6f}, "
        f"speed={best_metrics['cpu_time_per_guess']:.6f}, "
        f"memory={best_metrics['memory_bytes']:.0f})"
    )

    return 0


if __name__ == "__main__":
    sys.exit(main())
