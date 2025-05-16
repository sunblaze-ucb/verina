# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def maxSubarraySum(numbers):
2: ✓     max_sum = 0
3: ✓     current_sum = 0
4: ✓     for number in numbers:
5: ✓         current_sum = max(0, current_sum + number)
6: ✓         max_sum = max(max_sum, current_sum)
7: ✓     return max_sum
```

## Complete Test File

```python
def maxSubarraySum(numbers):
    max_sum = 0
    current_sum = 0
    for number in numbers:
        current_sum = max(0, current_sum + number)
        max_sum = max(max_sum, current_sum)
    return max_sum

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = maxSubarraySum([1, 2, 3, -2, 5])
        assert result == 9, f"Test 1 failed: got {result}, expected {9}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = maxSubarraySum([-2, -3, 4, -1, -2, 1, 5, -3])
        assert result == 7, f"Test 2 failed: got {result}, expected {7}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = maxSubarraySum([-1, -2, -3, -4])
        assert result == 0, f"Test 3 failed: got {result}, expected {0}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = maxSubarraySum([5, -3, 2, 1, -2])
        assert result == 5, f"Test 4 failed: got {result}, expected {5}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = maxSubarraySum([0, 0, 0, 0])
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = maxSubarraySum([])
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = maxSubarraySum([10])
        assert result == 10, f"Test 7 failed: got {result}, expected {10}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = maxSubarraySum([-5, 8, -3, 4, -1])
        assert result == 9, f"Test 8 failed: got {result}, expected {9}"
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
