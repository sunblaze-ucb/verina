# Coverage Report

Total executable lines: 3
Covered lines: 3
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def missingNumber(nums):
2: ✓     n = len(nums)
3: ✓     return n * (n + 1) // 2 - sum(nums)
```

## Complete Test File

```python
def missingNumber(nums):
    n = len(nums)
    return n * (n + 1) // 2 - sum(nums)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = missingNumber([3, 0, 1])
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = missingNumber([0, 1])
        assert result == 2, f"Test 2 failed: got {result}, expected {2}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = missingNumber([9, 6, 4, 2, 3, 5, 7, 0, 1])
        assert result == 8, f"Test 3 failed: got {result}, expected {8}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = missingNumber([0])
        assert result == 1, f"Test 4 failed: got {result}, expected {1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = missingNumber([1])
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
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
