# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def rotate(a, offset):
2: ✓     n = len(a)
3: ✓     if n == 0:
4: ✓         return a
5: ✓     offset %= n
6: ✓     return a[offset:] + a[:offset]
```

## Complete Test File

```python
def rotate(a, offset):
    n = len(a)
    if n == 0:
        return a
    offset %= n
    return a[offset:] + a[:offset]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = rotate([1, 2, 3, 4, 5], 2)
        assert result == [3, 4, 5, 1, 2], f"Test 1 failed: got {result}, expected {[3, 4, 5, 1, 2]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = rotate([10, 20, 30, 40], 1)
        assert result == [20, 30, 40, 10], f"Test 2 failed: got {result}, expected {[20, 30, 40, 10]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = rotate([], 5)
        assert result == [], f"Test 3 failed: got {result}, expected {[]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = rotate([7], 0)
        assert result == [7], f"Test 4 failed: got {result}, expected {[7]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = rotate([-1, -2, -3, -4], 3)
        assert result == [-4, -1, -2, -3], f"Test 5 failed: got {result}, expected {[-4, -1, -2, -3]}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = rotate([5, 10, 15], 5)
        assert result == [15, 5, 10], f"Test 6 failed: got {result}, expected {[15, 5, 10]}"
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
