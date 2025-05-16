# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def ComputeAvg(a, b):
2: ✓     return (a + b) // 2
```

## Complete Test File

```python
def ComputeAvg(a, b):
    return (a + b) // 2

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = ComputeAvg(4, 6)
        assert result == 5, f"Test 1 failed: got {result}, expected {5}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = ComputeAvg(3, 5)
        assert result == 4, f"Test 2 failed: got {result}, expected {4}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = ComputeAvg(3, 4)
        assert result == 3, f"Test 3 failed: got {result}, expected {3}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = ComputeAvg(-3, 7)
        assert result == 2, f"Test 4 failed: got {result}, expected {2}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = ComputeAvg(-5, 5)
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
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
