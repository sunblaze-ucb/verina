# Coverage Report

Total executable lines: 15
Covered lines: 15
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def minimumRightShifts(nums):
2: ✓     n = len(nums)
3: ✓     if n <= 1:
4: ✓         return 0
5: ✓     # Check if already sorted.
6: ✓     if all(nums[i] <= nums[i+1] for i in range(n-1)):
7: ✓         return 0
8: ✓     descent_count = 0
9: ✓     pivot = -1
10: ✓     for i in range(n-1):
11: ✓         if nums[i] > nums[i+1]:
12: ✓             descent_count += 1
13: ✓             pivot = i
14: ✓     # Check cyclic condition: last element should be <= first element.
15: ✓     if descent_count == 1 and nums[-1] <= nums[0]:
16: ✓         return n - (pivot + 1)
17: ✓     return -1
```

## Complete Test File

```python
def minimumRightShifts(nums):
    n = len(nums)
    if n <= 1:
        return 0
    # Check if already sorted.
    if all(nums[i] <= nums[i+1] for i in range(n-1)):
        return 0
    descent_count = 0
    pivot = -1
    for i in range(n-1):
        if nums[i] > nums[i+1]:
            descent_count += 1
            pivot = i
    # Check cyclic condition: last element should be <= first element.
    if descent_count == 1 and nums[-1] <= nums[0]:
        return n - (pivot + 1)
    return -1

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = minimumRightShifts([3, 4, 5, 1, 2])
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = minimumRightShifts([1, 3, 5])
        assert result == 0, f"Test 2 failed: got {result}, expected {0}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = minimumRightShifts([2, 1, 4])
        assert result == -1, f"Test 3 failed: got {result}, expected {-1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = minimumRightShifts([1])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = minimumRightShifts([2, 1])
        assert result == 1, f"Test 5 failed: got {result}, expected {1}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = minimumRightShifts([1, 2, 3, 4, 5])
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = minimumRightShifts([5, 1, 2, 3, 4])
        assert result == 4, f"Test 7 failed: got {result}, expected {4}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = minimumRightShifts([1, 5, 2, 3, 4])
        assert result == -1, f"Test 8 failed: got {result}, expected {-1}"
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
