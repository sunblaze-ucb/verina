# Coverage Report

Total executable lines: 12
Covered lines: 12
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def longestConsecutive(nums):
2: ✓     s = set(nums)
3: ✓     max_length = 0
4: ✓     for num in s:
5: ✓         if num - 1 not in s:
6: ✓             current = num
7: ✓             count = 1
8: ✓             while current + 1 in s:
9: ✓                 current += 1
10: ✓                 count += 1
11: ✓             max_length = max(max_length, count)
12: ✓     return max_length
```

## Complete Test File

```python
def longestConsecutive(nums):
    s = set(nums)
    max_length = 0
    for num in s:
        if num - 1 not in s:
            current = num
            count = 1
            while current + 1 in s:
                current += 1
                count += 1
            max_length = max(max_length, count)
    return max_length

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = longestConsecutive([100, 4, 200, 1, 3, 2])
        assert result == 4, f"Test 1 failed: got {result}, expected {4}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = longestConsecutive([0, 3, 7, 2, 5, 8, 4, 6, 1])
        assert result == 9, f"Test 2 failed: got {result}, expected {9}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = longestConsecutive([1, 2, 0])
        assert result == 3, f"Test 3 failed: got {result}, expected {3}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = longestConsecutive([])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = longestConsecutive([10])
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
