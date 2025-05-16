# Coverage Report

Total executable lines: 12
Covered lines: 12
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def lastPosition(arr, elem):
2: ✓     low, high = 0, len(arr) - 1
3: ✓     pos = -1
4: ✓     while low <= high:
5: ✓         mid = (low + high) // 2
6: ✓         if arr[mid] < elem:
7: ✓             low = mid + 1
8: ✓         elif arr[mid] > elem:
9: ✓             high = mid - 1
10: ✓         else:
11: ✓             pos = mid
12: ✓             low = mid + 1
13: ✓     return pos
```

## Complete Test File

```python
def lastPosition(arr, elem):
    low, high = 0, len(arr) - 1
    pos = -1
    while low <= high:
        mid = (low + high) // 2
        if arr[mid] < elem:
            low = mid + 1
        elif arr[mid] > elem:
            high = mid - 1
        else:
            pos = mid
            low = mid + 1
    return pos

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = lastPosition([1, 2, 2, 3, 4, 5], 2)
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = lastPosition([1, 2, 2, 3, 4, 5], 6)
        assert result == -1, f"Test 2 failed: got {result}, expected {-1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = lastPosition([1, 2, 2, 3, 4, 5], 5)
        assert result == 5, f"Test 3 failed: got {result}, expected {5}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = lastPosition([1], 1)
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = lastPosition([1, 1, 1, 1], 1)
        assert result == 3, f"Test 5 failed: got {result}, expected {3}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = lastPosition([2, 2, 3, 3, 3], 3)
        assert result == 4, f"Test 6 failed: got {result}, expected {4}"
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
