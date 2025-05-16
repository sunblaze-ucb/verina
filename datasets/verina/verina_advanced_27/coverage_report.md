# Coverage Report

Total executable lines: 19
Covered lines: 19
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def longestCommonSubsequence(s1, s2):
2: ✓     m, n = len(s1), len(s2)
3: ✓     dp = [[0]*(n+1) for _ in range(m+1)]
4: ✓     for i in range(1, m+1):
5: ✓         for j in range(1, n+1):
6: ✓             if s1[i-1] == s2[j-1]:
7: ✓                 dp[i][j] = dp[i-1][j-1] + 1
8: ✓             else:
9: ✓                 dp[i][j] = max(dp[i-1][j], dp[i][j-1])
10: ✓     i, j = m, n
11: ✓     lcs = []
12: ✓     while i > 0 and j > 0:
13: ✓         if s1[i-1] == s2[j-1]:
14: ✓             lcs.append(s1[i-1])
15: ✓             i -= 1
16: ✓             j -= 1
17: ✓         elif dp[i-1][j] >= dp[i][j-1]:
18: ✓             i -= 1
19: ✓         else:
20: ✓             j -= 1
21: ✓     return ''.join(reversed(lcs))
```

## Complete Test File

```python
def longestCommonSubsequence(s1, s2):
    m, n = len(s1), len(s2)
    dp = [[0]*(n+1) for _ in range(m+1)]
    for i in range(1, m+1):
        for j in range(1, n+1):
            if s1[i-1] == s2[j-1]:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
    i, j = m, n
    lcs = []
    while i > 0 and j > 0:
        if s1[i-1] == s2[j-1]:
            lcs.append(s1[i-1])
            i -= 1
            j -= 1
        elif dp[i-1][j] >= dp[i][j-1]:
            i -= 1
        else:
            j -= 1
    return ''.join(reversed(lcs))

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = longestCommonSubsequence('abcde', 'ace')
        assert result == 'ace', f"Test 1 failed: got {result}, expected {'ace'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = longestCommonSubsequence('aaaa', 'bbaaa')
        assert result == 'aaa', f"Test 2 failed: got {result}, expected {'aaa'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = longestCommonSubsequence('xyz', 'abc')
        assert result == '', f"Test 3 failed: got {result}, expected {''}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = longestCommonSubsequence('axbxc', 'abxc')
        assert result == 'abxc', f"Test 4 failed: got {result}, expected {'abxc'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = longestCommonSubsequence('AGGTAB', 'GXTXAYB')
        assert result == 'GTAB', f"Test 5 failed: got {result}, expected {'GTAB'}"
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
