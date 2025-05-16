# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def elementWiseModulo(a, b):
2: ✓     return [x % y for x, y in zip(a, b)]
```

## Complete Test File

```python
def elementWiseModulo(a, b):
    return [x % y for x, y in zip(a, b)]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = elementWiseModulo([10, 20, 30], [3, 7, 5])
        assert result == [1, 6, 0], f"Test 1 failed: got {result}, expected {[1, 6, 0]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = elementWiseModulo([100, 200, 300, 400], [10, 20, 30, 50])
        assert result == [0, 0, 0, 0], f"Test 2 failed: got {result}, expected {[0, 0, 0, 0]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = elementWiseModulo([-10, -20, 30], [3, -7, 5])
        assert result == [2, 1, 0], f"Test 3 failed: got {result}, expected {[2, 1, 0]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
