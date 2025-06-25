import json
import os


def read_file(file_path):
    if os.path.exists(file_path):
        with open(file_path, "r", encoding="utf-8") as f:
            return f.read()
    return None


def main():
    verina_dir = "datasets/verina"
    output_file = "datasets/verina/verina_dataset.jsonl"

    # Get all subdirectories that match the pattern verina_*_*
    dirs = [
        d
        for d in os.listdir(verina_dir)
        if os.path.isdir(os.path.join(verina_dir, d)) and d.startswith("verina_")
    ]

    with open(output_file, "w", encoding="utf-8") as outfile:
        for dir_name in dirs:
            dir_path = os.path.join(verina_dir, dir_name)

            # Read task.json
            task_path = os.path.join(dir_path, "task.json")
            if not os.path.exists(task_path):
                continue

            with open(task_path, "r", encoding="utf-8") as f:
                task_data = json.load(f)

            # Remove file path fields
            if "description_file" in task_data:
                del task_data["description_file"]
            if "lean_file" in task_data:
                del task_data["lean_file"]
            if "test_file" in task_data:
                del task_data["test_file"]
            if "reject_inputs_file" in task_data:
                del task_data["reject_inputs_file"]
            if "specification" in task_data:
                del task_data["specification"]

            # Read description.txt
            description = read_file(os.path.join(dir_path, "description.txt"))

            # Read test.json
            test_path = os.path.join(dir_path, "test.json")
            tests = None
            if os.path.exists(test_path):
                with open(test_path, "r", encoding="utf-8") as f:
                    tests = json.load(f)

            # Read reject_inputs.json
            reject_path = os.path.join(dir_path, "reject_inputs.json")
            reject_inputs = None
            if os.path.exists(reject_path):
                with open(reject_path, "r", encoding="utf-8") as f:
                    reject_inputs = json.load(f)

            # Read task.lean
            lean_code = read_file(os.path.join(dir_path, "task.lean"))

            # Create a datapoint with all fields at the top level
            datapoint = {
                "id": task_data.get("id", dir_name),
                "description": description,
                "lean_code": lean_code,
                # Add all other task fields at the top level
                **{k: v for k, v in task_data.items() if k != "id"},
                "tests": tests,
                "reject_inputs": reject_inputs,
            }

            # Write to JSONL
            outfile.write(json.dumps(datapoint) + "\n")

    print(f"Created JSONL file at {output_file}")


if __name__ == "__main__":
    main()
