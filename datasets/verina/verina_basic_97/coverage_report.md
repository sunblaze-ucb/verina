# Coverage Report

Total executable lines: 3
Covered lines: 3
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def TestArrayElements(a, j):
2: ✓     a[j] = 60
3: ✓     return a
```

## Complete Test File

```python
def TestArrayElements(a, j):
    a[j] = 60
    return a

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = TestArrayElements([1, 2, 3, 4, 5], 2)
        assert result == [1, 2, 60, 4, 5], f"Test 1 failed: got {result}, expected {[1, 2, 60, 4, 5]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = TestArrayElements([60, 30, 20], 1)
        assert result == [60, 60, 20], f"Test 2 failed: got {result}, expected {[60, 60, 20]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = TestArrayElements([10, 20, 30], 0)
        assert result == [60, 20, 30], f"Test 3 failed: got {result}, expected {[60, 20, 30]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = TestArrayElements([5, 10, 15], 2)
        assert result == [5, 10, 60], f"Test 4 failed: got {result}, expected {[5, 10, 60]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = TestArrayElements([0], 0)
        assert result == [60], f"Test 5 failed: got {result}, expected {[60]}"
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
