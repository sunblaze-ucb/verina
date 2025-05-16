# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def longestIncreasingSubsequence(nums):
2: ✓     from bisect import bisect_left
3: ✓     sub = []
4: ✓     for num in nums:
5: ✓         i = bisect_left(sub, num)
6: ✓         if i == len(sub):
7: ✓             sub.append(num)
8: ✓         else:
9: ✓             sub[i] = num
10: ✓     return len(sub)
```

## Complete Test File

```python
def longestIncreasingSubsequence(nums):
    from bisect import bisect_left
    sub = []
    for num in nums:
        i = bisect_left(sub, num)
        if i == len(sub):
            sub.append(num)
        else:
            sub[i] = num
    return len(sub)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = longestIncreasingSubsequence([10, 9, 2, 5, 3, 7, 101, 18])
        assert result == 4, f"Test 1 failed: got {result}, expected {4}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = longestIncreasingSubsequence([0, 1, 0, 3, 2, 3])
        assert result == 4, f"Test 2 failed: got {result}, expected {4}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = longestIncreasingSubsequence([7, 7, 7, 7, 7, 7, 7])
        assert result == 1, f"Test 3 failed: got {result}, expected {1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = longestIncreasingSubsequence([1, 3, 2, 4])
        assert result == 3, f"Test 4 failed: got {result}, expected {3}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = longestIncreasingSubsequence([10])
        assert result == 1, f"Test 5 failed: got {result}, expected {1}"
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
