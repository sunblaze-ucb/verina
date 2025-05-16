# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def LongestCommonSubsequence(a, b):
2: ✓     m, n = len(a), len(b)
3: ✓     dp = [[0] * (n + 1) for _ in range(m + 1)]
4: ✓     for i in range(1, m + 1):
5: ✓         for j in range(1, n + 1):
6: ✓             if a[i - 1] == b[j - 1]:
7: ✓                 dp[i][j] = dp[i - 1][j - 1] + 1
8: ✓             else:
9: ✓                 dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
10: ✓     return dp[m][n]
```

## Complete Test File

```python
def LongestCommonSubsequence(a, b):
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i - 1] == b[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
    return dp[m][n]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = LongestCommonSubsequence([1, 2, 3], [1, 2, 3])
        assert result == 3, f"Test 1 failed: got {result}, expected {3}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = LongestCommonSubsequence([1, 3, 5, 7], [1, 2, 3, 4, 5, 6, 7])
        assert result == 4, f"Test 2 failed: got {result}, expected {4}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = LongestCommonSubsequence([1, 2, 3], [4, 5, 6])
        assert result == 0, f"Test 3 failed: got {result}, expected {0}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = LongestCommonSubsequence([], [1, 2, 3])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = LongestCommonSubsequence([1, 2, 3, 4], [2, 4, 6, 8])
        assert result == 2, f"Test 5 failed: got {result}, expected {2}"
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
