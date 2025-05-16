# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def arraySum(a, b):
2: ✓     return [x + y for x, y in zip(a, b)]
```

## Complete Test File

```python
def arraySum(a, b):
    return [x + y for x, y in zip(a, b)]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = arraySum([1, 2, 3], [4, 5, 6])
        assert result == [5, 7, 9], f"Test 1 failed: got {result}, expected {[5, 7, 9]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = arraySum([0, 0, 0], [0, 0, 0])
        assert result == [0, 0, 0], f"Test 2 failed: got {result}, expected {[0, 0, 0]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = arraySum([-1, 2, 3], [1, -2, 4])
        assert result == [0, 0, 7], f"Test 3 failed: got {result}, expected {[0, 0, 7]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = arraySum([10], [-10])
        assert result == [0], f"Test 4 failed: got {result}, expected {[0]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = arraySum([100, 200, 300], [100, 200, 300])
        assert result == [200, 400, 600], f"Test 5 failed: got {result}, expected {[200, 400, 600]}"
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
