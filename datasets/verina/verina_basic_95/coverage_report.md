# Coverage Report

Total executable lines: 3
Covered lines: 3
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def swap(arr, i, j):
2: ✓     arr[i], arr[j] = arr[j], arr[i]
3: ✓     return arr
```

## Complete Test File

```python
def swap(arr, i, j):
    arr[i], arr[j] = arr[j], arr[i]
    return arr

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = swap([1, 2, 3, 4, 5], 1, 3)
        assert result == [1, 4, 3, 2, 5], f"Test 1 failed: got {result}, expected {[1, 4, 3, 2, 5]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = swap([10, 20, 30, 40], 0, 3)
        assert result == [40, 20, 30, 10], f"Test 2 failed: got {result}, expected {[40, 20, 30, 10]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = swap([7, 8, 9], 1, 2)
        assert result == [7, 9, 8], f"Test 3 failed: got {result}, expected {[7, 9, 8]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = swap([1, 2, 3, 4], 0, 0)
        assert result == [1, 2, 3, 4], f"Test 4 failed: got {result}, expected {[1, 2, 3, 4]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = swap([-1, -2, -3], 0, 2)
        assert result == [-3, -2, -1], f"Test 5 failed: got {result}, expected {[-3, -2, -1]}"
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
