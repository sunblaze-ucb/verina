# Coverage Report

Total executable lines: 13
Covered lines: 13
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def findFirstOccurrence(arr, target):
2: ✓     left = 0
3: ✓     right = len(arr) - 1
4: ✓     result = -1
5: ✓     while left <= right:
6: ✓         mid = (left + right) // 2
7: ✓         if arr[mid] == target:
8: ✓             result = mid
9: ✓             right = mid - 1
10: ✓         elif arr[mid] < target:
11: ✓             left = mid + 1
12: ✓         else:
13: ✓             right = mid - 1
14: ✓     return result
```

## Complete Test File

```python
def findFirstOccurrence(arr, target):
    left = 0
    right = len(arr) - 1
    result = -1
    while left <= right:
        mid = (left + right) // 2
        if arr[mid] == target:
            result = mid
            right = mid - 1
        elif arr[mid] < target:
            left = mid + 1
        else:
            right = mid - 1
    return result

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = findFirstOccurrence([1, 2, 2, 3, 4, 5], 2)
        assert result == 1, f"Test 1 failed: got {result}, expected {1}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = findFirstOccurrence([1, 2, 2, 3, 4, 5], 6)
        assert result == -1, f"Test 2 failed: got {result}, expected {-1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = findFirstOccurrence([1, 2, 3, 4, 5], 1)
        assert result == 0, f"Test 3 failed: got {result}, expected {0}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = findFirstOccurrence([1, 2, 3, 4, 5], 5)
        assert result == 4, f"Test 4 failed: got {result}, expected {4}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = findFirstOccurrence([1, 2, 3, 4, 5], 0)
        assert result == -1, f"Test 5 failed: got {result}, expected {-1}"
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
