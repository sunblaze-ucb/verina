import json

from datasets import Dataset, Features, Sequence, Value

# 1) Read & normalize your JSONL
records = []
with open("datasets/verina/verina_dataset.jsonl", "r") as f:
    for line in f:
        obj = json.loads(line)

        # Extract difficulty level from ID
        difficulty = "unknown"
        if "id" in obj and isinstance(obj["id"], str):
            id_parts = obj["id"].split("_")
            if len(id_parts) > 1 and id_parts[0] == "verina":
                difficulty = id_parts[1]

        # Set the difficulty level
        obj["difficulty"] = difficulty

        for t in obj["tests"]:
            # ensure expected is a list
            exp = t["expected"]
            if not isinstance(exp, list):
                exp = [exp]
            # now stringify
            t["expected"] = [str(x) for x in exp]

            # same for unexpected (in case it ever comes in as a bare bool/int)
            unexp = t.get("unexpected", [])
            if not isinstance(unexp, list):
                unexp = [unexp]
            t["unexpected"] = [str(x) for x in unexp]

            # optionally, also stringify the input dict wholesale:
            t["input"] = json.dumps(t["input"])

        records.append(obj)

# 2) Define your schema
features = Features(
    {
        "id": Value("string"),  # Added difficulty field
        "description": Value("string"),
        "lean_code": Value("string"),
        "signature": {
            "name": Value("string"),
            "parameters": Sequence(
                {
                    "param_name": Value("string"),
                    "param_type": Value("string"),
                }
            ),
            "return_type": Value("string"),
        },
        "metadata": {
            "upstream": {
                "name": Value("string"),
                "link": Value("string"),
                "task_id": Value("string"),
                "student_id": Sequence(Value("int64")),
            }
        },
        "tests": Sequence(
            {
                "input": Value("string"),  # now always a JSON string
                "expected": Sequence(Value("string")),  # now always list of strings
                "unexpected": Sequence(Value("string")),
            }
        ),
        "reject_inputs": Sequence({"input": Value("string")}),
        "difficulty": Value("string"),
    }
)

# 3) Build the HF Dataset
dataset = Dataset.from_list(records, features=features)

print(dataset)
print(dataset.features)
dataset.save_to_disk("verina_dataset")

# from datasets import load_from_disk

# # 1) Load the dataset back
# ds = load_from_disk("verina_dataset")

# # 2) Print the first 5 examples as Python dicts
# for i, ex in enumerate(ds.select(range(5))):
#     print(f"\n— Example {i} —")
#     for k, v in ex.items():
#         print(f"{k!r}: {v!r}")

dataset.push_to_hub("sunblaze-ucb/verina")
