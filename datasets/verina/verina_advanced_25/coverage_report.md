# Coverage Report

Total executable lines: 13
Covered lines: 13
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def lengthOfLIS(nums):
2: ✓     tails = []
3: ✓     for num in nums:
4: ✓         left, right = 0, len(tails)
5: ✓         while left < right:
6: ✓             mid = (left + right) // 2
7: ✓             if tails[mid] < num:
8: ✓                 left = mid + 1
9: ✓             else:
10: ✓                 right = mid
11: ✓         if left == len(tails):
12: ✓             tails.append(num)
13: ✓         else:
14: ✓             tails[left] = num
15: ✓     return len(tails)
```

## Complete Test File

```python
def lengthOfLIS(nums):
    tails = []
    for num in nums:
        left, right = 0, len(tails)
        while left < right:
            mid = (left + right) // 2
            if tails[mid] < num:
                left = mid + 1
            else:
                right = mid
        if left == len(tails):
            tails.append(num)
        else:
            tails[left] = num
    return len(tails)

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
        result = lengthOfLIS([])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = lengthOfLIS([4, 10, 4, 3, 8, 9])
        assert result == 3, f"Test 5 failed: got {result}, expected {3}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = lengthOfLIS([1, 3, 6, 7, 9, 4, 10, 5, 6])
        assert result == 6, f"Test 6 failed: got {result}, expected {6}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = lengthOfLIS([10, 22, 9, 33, 21, 50, 41, 60, 80])
        assert result == 6, f"Test 7 failed: got {result}, expected {6}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = lengthOfLIS([0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15])
        assert result == 6, f"Test 8 failed: got {result}, expected {6}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    # Test case 9
    try:
        result = lengthOfLIS([-2, -1])
        assert result == 2, f"Test 9 failed: got {result}, expected {2}"
        print(f"Test 9 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 9 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
