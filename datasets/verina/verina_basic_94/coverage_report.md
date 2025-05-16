# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def iter_copy(s):
2: ✓     return s.copy()
```

## Complete Test File

```python
def iter_copy(s):
    return s.copy()

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = iter_copy([1, 2, 3])
        assert result == [1, 2, 3], f"Test 1 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = iter_copy([10, 20, 30, 40])
        assert result == [10, 20, 30, 40], f"Test 2 failed: got {result}, expected {[10, 20, 30, 40]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = iter_copy([])
        assert result == [], f"Test 3 failed: got {result}, expected {[]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = iter_copy([-1, -2, -3])
        assert result == [-1, -2, -3], f"Test 4 failed: got {result}, expected {[-1, -2, -3]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = iter_copy([5, 5, 5, 5])
        assert result == [5, 5, 5, 5], f"Test 5 failed: got {result}, expected {[5, 5, 5, 5]}"
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
