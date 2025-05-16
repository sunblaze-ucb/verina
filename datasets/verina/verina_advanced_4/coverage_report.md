# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def LongestIncreasingSubsequence(a):
2: ✓     import bisect
3: ✓     sub = []
4: ✓     for num in a:
5: ✓         pos = bisect.bisect_left(sub, num)
6: ✓         if pos == len(sub):
7: ✓             sub.append(num)
8: ✓         else:
9: ✓             sub[pos] = num
10: ✓     return len(sub)
```

## Complete Test File

```python
def LongestIncreasingSubsequence(a):
    import bisect
    sub = []
    for num in a:
        pos = bisect.bisect_left(sub, num)
        if pos == len(sub):
            sub.append(num)
        else:
            sub[pos] = num
    return len(sub)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = LongestIncreasingSubsequence([5, 2, 8, 6, 3, 6, 9, 7])
        assert result == 4, f"Test 1 failed: got {result}, expected {4}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = LongestIncreasingSubsequence([3, 1, 2, 1, 0])
        assert result == 2, f"Test 2 failed: got {result}, expected {2}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = LongestIncreasingSubsequence([2, 3, -2, -1, 7, 19, 3, 6, -4, 6, -7, 0, 9, 12, 10])
        assert result == 6, f"Test 3 failed: got {result}, expected {6}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = LongestIncreasingSubsequence([5, -5, -3, 2, 4, 1, 0, -1, 3, 2, 0])
        assert result == 4, f"Test 4 failed: got {result}, expected {4}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = LongestIncreasingSubsequence([1, 7, 23, 14, -4, 21, 8, 2, -1, 9, 12, 2])
        assert result == 5, f"Test 5 failed: got {result}, expected {5}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = LongestIncreasingSubsequence([])
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
