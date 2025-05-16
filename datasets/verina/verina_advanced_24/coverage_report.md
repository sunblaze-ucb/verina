# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def lengthOfLIS(nums):
2: ✓     from bisect import bisect_left
3: ✓     dp = []
4: ✓     for num in nums:
5: ✓         i = bisect_left(dp, num)
6: ✓         if i == len(dp):
7: ✓             dp.append(num)
8: ✓         else:
9: ✓             dp[i] = num
10: ✓     return len(dp)
```

## Complete Test File

```python
def lengthOfLIS(nums):
    from bisect import bisect_left
    dp = []
    for num in nums:
        i = bisect_left(dp, num)
        if i == len(dp):
            dp.append(num)
        else:
            dp[i] = num
    return len(dp)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = lengthOfLIS([10, 9, 2, 5, 3, 7, 101, 18])
        assert result == 4, f"Test 1 failed: got {result}, expected {4}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = lengthOfLIS([0, 1, 0, 3, 2, 3])
        assert result == 4, f"Test 2 failed: got {result}, expected {4}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = lengthOfLIS([7, 7, 7, 7, 7, 7, 7])
        assert result == 1, f"Test 3 failed: got {result}, expected {1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = lengthOfLIS([4, 10, 4, 3, 8, 9])
        assert result == 3, f"Test 4 failed: got {result}, expected {3}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = lengthOfLIS([1, 3, 6, 7, 9, 4, 10, 5, 6])
        assert result == 6, f"Test 5 failed: got {result}, expected {6}"
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
