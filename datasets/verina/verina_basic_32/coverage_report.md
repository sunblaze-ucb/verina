# Coverage Report

Total executable lines: 4
Covered lines: 4
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def swapFirstAndLast(a):
2: ✓     res = a.copy()
3: ✓     res[0], res[-1] = res[-1], res[0]
4: ✓     return res
```

## Complete Test File

```python
def swapFirstAndLast(a):
    res = a.copy()
    res[0], res[-1] = res[-1], res[0]
    return res

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = swapFirstAndLast([1, 2, 3, 4, 5])
        assert result == [5, 2, 3, 4, 1], f"Test 1 failed: got {result}, expected {[5, 2, 3, 4, 1]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = swapFirstAndLast([10])
        assert result == [10], f"Test 2 failed: got {result}, expected {[10]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = swapFirstAndLast([1, 2])
        assert result == [2, 1], f"Test 3 failed: got {result}, expected {[2, 1]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = swapFirstAndLast([1, 2, 3])
        assert result == [3, 2, 1], f"Test 4 failed: got {result}, expected {[3, 2, 1]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
