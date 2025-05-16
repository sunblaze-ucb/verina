# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def arrayProduct(a, b):
2: ✓     n = max(len(a), len(b))
3: ✓     result = []
4: ✓     for i in range(n):
5: ✓         x = a[i] if i < len(a) else 0
6: ✓         y = b[i] if i < len(b) else 0
7: ✓         result.append(x * y)
8: ✓     return result
```

## Complete Test File

```python
def arrayProduct(a, b):
    n = max(len(a), len(b))
    result = []
    for i in range(n):
        x = a[i] if i < len(a) else 0
        y = b[i] if i < len(b) else 0
        result.append(x * y)
    return result

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = arrayProduct([1, 2, 3], [4, 5, 6])
        assert result == [4, 10, 18], f"Test 1 failed: got {result}, expected {[4, 10, 18]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = arrayProduct([0, 0, 0], [1, 2, 3])
        assert result == [0, 0, 0], f"Test 2 failed: got {result}, expected {[0, 0, 0]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = arrayProduct([-1, 2, -3], [3, -4, 5])
        assert result == [-3, -8, -15], f"Test 3 failed: got {result}, expected {[-3, -8, -15]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = arrayProduct([2], [10])
        assert result == [20], f"Test 4 failed: got {result}, expected {[20]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = arrayProduct([1, 2, 3, 4], [2, 2, 2, 2])
        assert result == [2, 4, 6, 8], f"Test 5 failed: got {result}, expected {[2, 4, 6, 8]}"
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
