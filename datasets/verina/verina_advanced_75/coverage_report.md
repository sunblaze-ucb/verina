# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def task_code(sequence):
2: ✓     cur = sequence[0]
3: ✓     maxSoFar = sequence[0]
4: ✓     for num in sequence[1:]:
5: ✓         cur = max(num, cur + num)
6: ✓         maxSoFar = max(maxSoFar, cur)
7: ✓     return maxSoFar
```

## Complete Test File

```python
def task_code(sequence):
    cur = sequence[0]
    maxSoFar = sequence[0]
    for num in sequence[1:]:
        cur = max(num, cur + num)
        maxSoFar = max(maxSoFar, cur)
    return maxSoFar

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = task_code([10, -4, 3, 1, 5, 6, -35, 12, 21, -1])
        assert result == 33, f"Test 1 failed: got {result}, expected {33}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = task_code([2, 1, -4, 3, 4, -4, 6, 5, -5, 1])
        assert result == 14, f"Test 2 failed: got {result}, expected {14}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = task_code([-1, -2, -3, -4, -5])
        assert result == -1, f"Test 3 failed: got {result}, expected {-1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = task_code([7])
        assert result == 7, f"Test 4 failed: got {result}, expected {7}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = task_code([1, 2, 3, 4, 5])
        assert result == 15, f"Test 5 failed: got {result}, expected {15}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
