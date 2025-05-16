# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def CanyonSearch(a, b):
2: ✓     i, j = 0, 0
3: ✓     min_diff = abs(a[0] - b[0])
4: ✓     while i < len(a) and j < len(b):
5: ✓         current_diff = abs(a[i] - b[j])
6: ✓         if current_diff < min_diff:
7: ✓             min_diff = current_diff
8: ✓         if a[i] < b[j]:
9: ✓             i += 1
10: ✓         else:
11: ✓             j += 1
12: ✓     return min_diff
```

## Complete Test File

```python
def CanyonSearch(a, b):
    i, j = 0, 0
    min_diff = abs(a[0] - b[0])
    while i < len(a) and j < len(b):
        current_diff = abs(a[i] - b[j])
        if current_diff < min_diff:
            min_diff = current_diff
        if a[i] < b[j]:
            i += 1
        else:
            j += 1
    return min_diff

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = CanyonSearch([1, 3, 5], [2, 4, 6])
        assert result == '1', f"Test 1 failed: got {result}, expected {'1'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = CanyonSearch([-5, -2, 0], [1, 3])
        assert result == '1', f"Test 2 failed: got {result}, expected {'1'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = CanyonSearch([10, 20, 30], [5, 15, 25])
        assert result == '5', f"Test 3 failed: got {result}, expected {'5'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = CanyonSearch([1, 2, 3, 4, 5], [3])
        assert result == '0', f"Test 4 failed: got {result}, expected {'0'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = CanyonSearch([-10, -5, 0, 5, 10], [-3, 2, 8])
        assert result == '2', f"Test 5 failed: got {result}, expected {'2'}"
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
