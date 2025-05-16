# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def reverse(a):
2: ✓     return a[::-1]
```

## Complete Test File

```python
def reverse(a):
    return a[::-1]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = reverse([1, 2, 3, 4, 5])
        assert result == [5, 4, 3, 2, 1], f"Test 1 failed: got {result}, expected {[5, 4, 3, 2, 1]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = reverse([10, 20, 30, 40])
        assert result == [40, 30, 20, 10], f"Test 2 failed: got {result}, expected {[40, 30, 20, 10]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = reverse([])
        assert result == [], f"Test 3 failed: got {result}, expected {[]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = reverse([7])
        assert result == [7], f"Test 4 failed: got {result}, expected {[7]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = reverse([-1, 0, 1])
        assert result == [1, 0, -1], f"Test 5 failed: got {result}, expected {[1, 0, -1]}"
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
