# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def replace(arr, k):
2: ✓     return [-1 if x > k else x for x in arr]
```

## Complete Test File

```python
def replace(arr, k):
    return [-1 if x > k else x for x in arr]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = replace([1, 5, 3, 10], 4)
        assert result == [1, -1, 3, -1], f"Test 1 failed: got {result}, expected {[1, -1, 3, -1]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = replace([-1, 0, 1, 2], 2)
        assert result == [-1, 0, 1, 2], f"Test 2 failed: got {result}, expected {[-1, 0, 1, 2]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = replace([100, 50, 100], 100)
        assert result == [100, 50, 100], f"Test 3 failed: got {result}, expected {[100, 50, 100]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = replace([-5, -2, 0, 3], -3)
        assert result == [-5, -1, -1, -1], f"Test 4 failed: got {result}, expected {[-5, -1, -1, -1]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = replace([1, 2, 3], 5)
        assert result == [1, 2, 3], f"Test 5 failed: got {result}, expected {[1, 2, 3]}"
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
