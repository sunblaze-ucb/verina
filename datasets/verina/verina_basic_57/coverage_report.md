# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def CountLessThan(numbers, threshold):
2: ✓     return sum(1 for num in numbers if num < threshold)
```

## Complete Test File

```python
def CountLessThan(numbers, threshold):
    return sum(1 for num in numbers if num < threshold)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = CountLessThan([1, 2, 3, 4, 5], 3)
        assert result == '2', f"Test 1 failed: got {result}, expected {'2'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = CountLessThan([], 10)
        assert result == '0', f"Test 2 failed: got {result}, expected {'0'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = CountLessThan([-1, 0, 1], 0)
        assert result == '1', f"Test 3 failed: got {result}, expected {'1'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = CountLessThan([5, 6, 7, 2, 1], 5)
        assert result == '2', f"Test 4 failed: got {result}, expected {'2'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = CountLessThan([3, 3, 3, 3], 3)
        assert result == '0', f"Test 5 failed: got {result}, expected {'0'}"
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
