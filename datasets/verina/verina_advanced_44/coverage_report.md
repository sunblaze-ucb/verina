# Coverage Report

Total executable lines: 14
Covered lines: 14
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def maxSubarraySumDivisibleByK(arr, k):
2: ✓     n = len(arr)
3: ✓     if n < k:
4: ✓         return 0
5: ✓     prefix = [0] * (n + 1)
6: ✓     for i in range(n):
7: ✓         prefix[i + 1] = prefix[i] + arr[i]
8: ✓     max_sum = float("-inf")
9: ✓     for i in range(n):
10: ✓         for j in range(i + k - 1, n, k):
11: ✓             current_sum = prefix[j + 1] - prefix[i]
12: ✓             if current_sum > max_sum:
13: ✓                 max_sum = current_sum
14: ✓     return max_sum if max_sum > 0 else 0
```

## Complete Test File

```python
def maxSubarraySumDivisibleByK(arr, k):
    n = len(arr)
    if n < k:
        return 0
    prefix = [0] * (n + 1)
    for i in range(n):
        prefix[i + 1] = prefix[i] + arr[i]
    max_sum = float("-inf")
    for i in range(n):
        for j in range(i + k - 1, n, k):
            current_sum = prefix[j + 1] - prefix[i]
            if current_sum > max_sum:
                max_sum = current_sum
    return max_sum if max_sum > 0 else 0

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = maxSubarraySumDivisibleByK([1, 2, 3, 4, 5], 2)
        assert result == 14, f"Test 1 failed: got {result}, expected {14}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = maxSubarraySumDivisibleByK([1, -2, 3, -4, 5], 3)
        assert result == 4, f"Test 2 failed: got {result}, expected {4}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = maxSubarraySumDivisibleByK([], 5)
        assert result == 0, f"Test 3 failed: got {result}, expected {0}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = maxSubarraySumDivisibleByK([1, 2, 3, 4], 1)
        assert result == 10, f"Test 4 failed: got {result}, expected {10}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = maxSubarraySumDivisibleByK([-2, 7, 1, 3], 2)
        assert result == 9, f"Test 5 failed: got {result}, expected {9}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = maxSubarraySumDivisibleByK([-100, 0, 1], 5)
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = maxSubarraySumDivisibleByK([1999, 1, -1023, 12351, -9999], 2)
        assert result == 13328, f"Test 7 failed: got {result}, expected {13328}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
