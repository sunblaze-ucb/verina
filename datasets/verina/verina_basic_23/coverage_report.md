# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def differenceMinMax(a):
2: ✓     return max(a) - min(a)
```

## Complete Test File

```python
def differenceMinMax(a):
    return max(a) - min(a)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = differenceMinMax([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5])
        assert result == 8, f"Test 1 failed: got {result}, expected {8}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = differenceMinMax([10, 20, 30, 40, 50])
        assert result == 40, f"Test 2 failed: got {result}, expected {40}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = differenceMinMax([-10, -20, -30, -40, -50])
        assert result == 40, f"Test 3 failed: got {result}, expected {40}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = differenceMinMax([7])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = differenceMinMax([5, 5, 5, 5])
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = differenceMinMax([1, -1, 2, -2])
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
