# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def kthElement(arr, k):
2: ✓     return arr[k-1]
```

## Complete Test File

```python
def kthElement(arr, k):
    return arr[k-1]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = kthElement([10, 20, 30, 40, 50], 1)
        assert result == 10, f"Test 1 failed: got {result}, expected {10}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = kthElement([10, 20, 30, 40, 50], 3)
        assert result == 30, f"Test 2 failed: got {result}, expected {30}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = kthElement([10, 20, 30, 40, 50], 5)
        assert result == 50, f"Test 3 failed: got {result}, expected {50}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = kthElement([5], 1)
        assert result == 5, f"Test 4 failed: got {result}, expected {5}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = kthElement([1, 2, 3], 3)
        assert result == 3, f"Test 5 failed: got {result}, expected {3}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = kthElement([1, 2, 3], 2)
        assert result == 2, f"Test 6 failed: got {result}, expected {2}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = kthElement([9, 9, 9], 2)
        assert result == 9, f"Test 7 failed: got {result}, expected {9}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = kthElement([0, -1, -2], 1)
        assert result == 0, f"Test 8 failed: got {result}, expected {0}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    # Test case 9
    try:
        result = kthElement([0, -1, -2], 2)
        assert result == -1, f"Test 9 failed: got {result}, expected {-1}"
        print(f"Test 9 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 9 failed: {e}")
        test_results.append(False)

    # Test case 10
    try:
        result = kthElement([0, -1, -2], 3)
        assert result == -2, f"Test 10 failed: got {result}, expected {-2}"
        print(f"Test 10 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 10 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
