# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def longestIncreasingStreak(nums):
2: ✓     if not nums:
3: ✓         return 0
4: ✓     max_streak = 1
5: ✓     current_streak = 1
6: ✓     for i in range(1, len(nums)):
7: ✓         if nums[i] > nums[i - 1]:
8: ✓             current_streak += 1
9: ✓         else:
10: ✓             max_streak = max(max_streak, current_streak)
11: ✓             current_streak = 1
12: ✓     return max(max_streak, current_streak)
```

## Complete Test File

```python
def longestIncreasingStreak(nums):
    if not nums:
        return 0
    max_streak = 1
    current_streak = 1
    for i in range(1, len(nums)):
        if nums[i] > nums[i - 1]:
            current_streak += 1
        else:
            max_streak = max(max_streak, current_streak)
            current_streak = 1
    return max(max_streak, current_streak)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = longestIncreasingStreak([1, 2, 3, 2, 4, 5, 6])
        assert result == 4, f"Test 1 failed: got {result}, expected {4}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = longestIncreasingStreak([10, 20, 30, 40])
        assert result == 4, f"Test 2 failed: got {result}, expected {4}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = longestIncreasingStreak([5, 5, 5, 5])
        assert result == 1, f"Test 3 failed: got {result}, expected {1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = longestIncreasingStreak([10, 9, 8, 7])
        assert result == 1, f"Test 4 failed: got {result}, expected {1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = longestIncreasingStreak([])
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = longestIncreasingStreak([1, 2, 1, 2, 3, 0, 1, 2, 3, 4])
        assert result == 5, f"Test 6 failed: got {result}, expected {5}"
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
