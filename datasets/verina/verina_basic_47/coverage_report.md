# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def arraySum(a):
2: ✓     return sum(a)
```

## Complete Test File

```python
def arraySum(a):
    return sum(a)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = arraySum([1, 2, 3, 4, 5])
        assert result == 15, f"Test 1 failed: got {result}, expected {15}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = arraySum([13, 14, 15, 16, 17])
        assert result == 75, f"Test 2 failed: got {result}, expected {75}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = arraySum([-1, -2, -3])
        assert result == -6, f"Test 3 failed: got {result}, expected {-6}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = arraySum([10, -10])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
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
