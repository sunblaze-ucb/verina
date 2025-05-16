# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def longestIncreasingSubsequence(numbers):
2: ✓     if not numbers:
3: ✓         return 0
4: ✓     dp = [1] * len(numbers)
5: ✓     for i in range(1, len(numbers)):
6: ✓         for j in range(i):
7: ✓             if numbers[i] > numbers[j]:
8: ✓                 dp[i] = max(dp[i], dp[j] + 1)
9: ✓     return max(dp)
```

## Complete Test File

```python
def longestIncreasingSubsequence(numbers):
    if not numbers:
        return 0
    dp = [1] * len(numbers)
    for i in range(1, len(numbers)):
        for j in range(i):
            if numbers[i] > numbers[j]:
                dp[i] = max(dp[i], dp[j] + 1)
    return max(dp)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = longestIncreasingSubsequence([10, 22, 9, 33, 21, 50, 41, 60])
        assert result == 5, f"Test 1 failed: got {result}, expected {5}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = longestIncreasingSubsequence([3, 10, 2, 1, 20])
        assert result == 3, f"Test 2 failed: got {result}, expected {3}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = longestIncreasingSubsequence([50, 3, 10, 7, 40, 80])
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = longestIncreasingSubsequence([10, 9, 8, 7, 6, 5, 4, 3, 2, 1])
        assert result == 1, f"Test 4 failed: got {result}, expected {1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = longestIncreasingSubsequence([1, 2, 3, 4, 5])
        assert result == 5, f"Test 5 failed: got {result}, expected {5}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = longestIncreasingSubsequence([])
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = longestIncreasingSubsequence([5])
        assert result == 1, f"Test 7 failed: got {result}, expected {1}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = longestIncreasingSubsequence([5, 5, 5, 5])
        assert result == 1, f"Test 8 failed: got {result}, expected {1}"
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
