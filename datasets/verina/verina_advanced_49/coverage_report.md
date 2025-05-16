# Coverage Report

Total executable lines: 14
Covered lines: 14
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def mergeSortedLists(arr1, arr2):
2: ✓     i, j = 0, 0
3: ✓     merged = []
4: ✓     while i < len(arr1) and j < len(arr2):
5: ✓         if arr1[i] <= arr2[j]:
6: ✓             merged.append(arr1[i])
7: ✓             i += 1
8: ✓         else:
9: ✓             merged.append(arr2[j])
10: ✓             j += 1
11: ✓     if i < len(arr1):
12: ✓         merged.extend(arr1[i:])
13: ✓     if j < len(arr2):
14: ✓         merged.extend(arr2[j:])
15: ✓     return merged
```

## Complete Test File

```python
def mergeSortedLists(arr1, arr2):
    i, j = 0, 0
    merged = []
    while i < len(arr1) and j < len(arr2):
        if arr1[i] <= arr2[j]:
            merged.append(arr1[i])
            i += 1
        else:
            merged.append(arr2[j])
            j += 1
    if i < len(arr1):
        merged.extend(arr1[i:])
    if j < len(arr2):
        merged.extend(arr2[j:])
    return merged

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = mergeSortedLists([1, 3, 5], [2, 4, 6])
        assert result == [1, 2, 3, 4, 5, 6], f"Test 1 failed: got {result}, expected {[1, 2, 3, 4, 5, 6]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = mergeSortedLists([], [])
        assert result == [], f"Test 2 failed: got {result}, expected {[]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = mergeSortedLists([-2, 0, 1], [-3, -1])
        assert result == [-3, -2, -1, 0, 1], f"Test 3 failed: got {result}, expected {[-3, -2, -1, 0, 1]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = mergeSortedLists([10, 20, 30], [5, 25, 35])
        assert result == [5, 10, 20, 25, 30, 35], f"Test 4 failed: got {result}, expected {[5, 10, 20, 25, 30, 35]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = mergeSortedLists([1, 2, 2], [2, 3, 3])
        assert result == [1, 2, 2, 2, 3, 3], f"Test 5 failed: got {result}, expected {[1, 2, 2, 2, 3, 3]}"
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
