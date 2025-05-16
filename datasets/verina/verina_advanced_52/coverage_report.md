# Coverage Report

Total executable lines: 10
Covered lines: 10
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def minOperations(nums, k):
2: ✓     collected = set()
3: ✓     operations = 0
4: ✓     required = set(range(1, k+1))
5: ✓     while not required.issubset(collected):
6: ✓         num = nums.pop()
7: ✓         operations += 1
8: ✓         if num <= k:
9: ✓             collected.add(num)
10: ✓     return operations
```

## Complete Test File

```python
def minOperations(nums, k):
    collected = set()
    operations = 0
    required = set(range(1, k+1))
    while not required.issubset(collected):
        num = nums.pop()
        operations += 1
        if num <= k:
            collected.add(num)
    return operations

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = minOperations([3, 1, 5, 4, 2], 2)
        assert result == 4, f"Test 1 failed: got {result}, expected {4}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = minOperations([3, 1, 5, 4, 2], 5)
        assert result == 5, f"Test 2 failed: got {result}, expected {5}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = minOperations([3, 2, 5, 3, 1], 3)
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = minOperations([5, 4, 3, 2, 1], 1)
        assert result == 1, f"Test 4 failed: got {result}, expected {1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = minOperations([5, 4, 1, 2, 3], 3)
        assert result == 3, f"Test 5 failed: got {result}, expected {3}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = minOperations([1, 3, 2, 2, 1], 2)
        assert result == 2, f"Test 6 failed: got {result}, expected {2}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = minOperations([10, 1, 20, 2], 2)
        assert result == 3, f"Test 7 failed: got {result}, expected {3}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = minOperations([1, 2, 3], 0)
        assert result == 0, f"Test 8 failed: got {result}, expected {0}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
