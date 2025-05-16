# Coverage Report

Total executable lines: 12
Covered lines: 12
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def SlopeSearch(a, key):
2: ✓     rows = len(a)
3: ✓     cols = len(a[0])
4: ✓     i = 0
5: ✓     j = cols - 1
6: ✓     while i < rows and j >= 0:
7: ✓         if a[i][j] == key:
8: ✓             return (i, j)
9: ✓         elif a[i][j] > key:
10: ✓             j -= 1
11: ✓         else:
12: ✓             i += 1
13: ✓     return (-1, -1)
```

## Complete Test File

```python
def SlopeSearch(a, key):
    rows = len(a)
    cols = len(a[0])
    i = 0
    j = cols - 1
    while i < rows and j >= 0:
        if a[i][j] == key:
            return (i, j)
        elif a[i][j] > key:
            j -= 1
        else:
            i += 1
    return (-1, -1)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = SlopeSearch([[1, 2, 3], [4, 5, 6], [7, 8, 9]], 5)
        assert result == [1, 1], f"Test 1 failed: got {result}, expected {[1, 1]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = SlopeSearch([[1, 2, 3], [4, 5, 6], [7, 8, 9]], 3)
        assert result == [0, 2], f"Test 2 failed: got {result}, expected {[0, 2]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = SlopeSearch([[1, 2, 3], [4, 5, 6], [7, 8, 9]], 10)
        assert result == [-1, -1], f"Test 3 failed: got {result}, expected {[-1, -1]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = SlopeSearch([[1, 2, 3, 4]], 4)
        assert result == [0, 3], f"Test 4 failed: got {result}, expected {[0, 3]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = SlopeSearch([[1], [2], [3], [4]], 3)
        assert result == [2, 0], f"Test 5 failed: got {result}, expected {[2, 0]}"
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
