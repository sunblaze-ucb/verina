# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def searchInsert(xs, target):
2: ✓     low, high = 0, len(xs)
3: ✓     while low < high:
4: ✓         mid = (low + high) // 2
5: ✓         if xs[mid] < target:
6: ✓             low = mid + 1
7: ✓         else:
8: ✓             high = mid
9: ✓     return low
```

## Complete Test File

```python
def searchInsert(xs, target):
    low, high = 0, len(xs)
    while low < high:
        mid = (low + high) // 2
        if xs[mid] < target:
            low = mid + 1
        else:
            high = mid
    return low

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = searchInsert([1, 3, 5, 6], 5)
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = searchInsert([1, 3, 5, 6], 2)
        assert result == 1, f"Test 2 failed: got {result}, expected {1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = searchInsert([1, 3, 5, 6], 7)
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = searchInsert([1, 3, 5, 6], 0)
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = searchInsert([], 3)
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = searchInsert([10], 5)
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = searchInsert([10], 15)
        assert result == 1, f"Test 7 failed: got {result}, expected {1}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
