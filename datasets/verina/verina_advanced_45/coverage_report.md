# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def maxSubarraySum(xs):
2: ✓     if not xs:
3: ✓         return 0
4: ✓     current_sum = max_sum = xs[0]
5: ✓     for x in xs[1:]:
6: ✓         current_sum = max(x, current_sum + x)
7: ✓         max_sum = max(max_sum, current_sum)
8: ✓     return max_sum
```

## Complete Test File

```python
def maxSubarraySum(xs):
    if not xs:
        return 0
    current_sum = max_sum = xs[0]
    for x in xs[1:]:
        current_sum = max(x, current_sum + x)
        max_sum = max(max_sum, current_sum)
    return max_sum

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = maxSubarraySum([1, -2, 3, 4, -1])
        assert result == 7, f"Test 1 failed: got {result}, expected {7}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = maxSubarraySum([-2, -3, -1, -5])
        assert result == -1, f"Test 2 failed: got {result}, expected {-1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = maxSubarraySum([5, -1, 2, -1, 3])
        assert result == 8, f"Test 3 failed: got {result}, expected {8}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = maxSubarraySum([])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = maxSubarraySum([4, -1, -2, 1, 5])
        assert result == 7, f"Test 5 failed: got {result}, expected {7}"
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
