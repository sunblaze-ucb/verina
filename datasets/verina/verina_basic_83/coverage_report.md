# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def concat(a, b):
2: ✓     return a + b
```

## Complete Test File

```python
def concat(a, b):
    return a + b

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = concat([1, 2, 3], [4, 5])
        assert result == [1, 2, 3, 4, 5], f"Test 1 failed: got {result}, expected {[1, 2, 3, 4, 5]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = concat([], [])
        assert result == [], f"Test 2 failed: got {result}, expected {[]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = concat([10], [20, 30, 40])
        assert result == [10, 20, 30, 40], f"Test 3 failed: got {result}, expected {[10, 20, 30, 40]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = concat([-1, -2], [0])
        assert result == [-1, -2, 0], f"Test 4 failed: got {result}, expected {[-1, -2, 0]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = concat([7, 8, 9], [])
        assert result == [7, 8, 9], f"Test 5 failed: got {result}, expected {[7, 8, 9]}"
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
