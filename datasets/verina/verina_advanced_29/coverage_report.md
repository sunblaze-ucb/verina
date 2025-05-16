# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def longestGoodSubarray(nums, k):
2: ✓     count = {}
3: ✓     left = 0
4: ✓     max_len = 0
5: ✓     for right, num in enumerate(nums):
6: ✓         count[num] = count.get(num, 0) + 1
7: ✓         while count[num] > k:
8: ✓             count[nums[left]] -= 1
9: ✓             left += 1
10: ✓         max_len = max(max_len, right - left + 1)
11: ✓     return max_len
```

## Complete Test File

```python
def longestGoodSubarray(nums, k):
    count = {}
    left = 0
    max_len = 0
    for right, num in enumerate(nums):
        count[num] = count.get(num, 0) + 1
        while count[num] > k:
            count[nums[left]] -= 1
            left += 1
        max_len = max(max_len, right - left + 1)
    return max_len

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = longestGoodSubarray([1, 2, 3, 1, 2, 3, 1, 2], 2)
        assert result == 6, f"Test 1 failed: got {result}, expected {6}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = longestGoodSubarray([1, 2, 1, 2, 1, 2, 1, 2], 1)
        assert result == 2, f"Test 2 failed: got {result}, expected {2}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = longestGoodSubarray([5, 5, 5, 5, 5, 5, 5], 4)
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = longestGoodSubarray([1], 1)
        assert result == 1, f"Test 4 failed: got {result}, expected {1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = longestGoodSubarray([2, 2, 1, 1, 3], 2)
        assert result == 5, f"Test 5 failed: got {result}, expected {5}"
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
