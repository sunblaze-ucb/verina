# Coverage Report

Total executable lines: 12
Covered lines: 12
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def mergeSorted(a, b):
2: ✓     i, j = 0, 0
3: ✓     merged = []
4: ✓     while i < len(a) and j < len(b):
5: ✓         if a[i] <= b[j]:
6: ✓             merged.append(a[i])
7: ✓             i += 1
8: ✓         else:
9: ✓             merged.append(b[j])
10: ✓             j += 1
11: ✓     merged.extend(a[i:])
12: ✓     merged.extend(b[j:])
13: ✓     return merged
```

## Complete Test File

```python
def mergeSorted(a, b):
    i, j = 0, 0
    merged = []
    while i < len(a) and j < len(b):
        if a[i] <= b[j]:
            merged.append(a[i])
            i += 1
        else:
            merged.append(b[j])
            j += 1
    merged.extend(a[i:])
    merged.extend(b[j:])
    return merged

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = mergeSorted([1, 3, 5], [2, 4, 6])
        assert result == [1, 2, 3, 4, 5, 6], f"Test 1 failed: got {result}, expected {[1, 2, 3, 4, 5, 6]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = mergeSorted([1, 2], [1, 2, 3])
        assert result == [1, 1, 2, 2, 3], f"Test 2 failed: got {result}, expected {[1, 1, 2, 2, 3]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = mergeSorted([], [4, 5])
        assert result == [4, 5], f"Test 3 failed: got {result}, expected {[4, 5]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = mergeSorted([0, 3, 4], [])
        assert result == [0, 3, 4], f"Test 4 failed: got {result}, expected {[0, 3, 4]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = mergeSorted([1, 4, 6], [2, 3, 5])
        assert result == [1, 2, 3, 4, 5, 6], f"Test 5 failed: got {result}, expected {[1, 2, 3, 4, 5, 6]}"
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
