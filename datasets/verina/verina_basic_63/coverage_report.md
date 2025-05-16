# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def has_close_elements(numbers, threshold):
2: ✓     numbers = sorted(numbers)
3: ✓     for i in range(len(numbers) - 1):
4: ✓         if abs(numbers[i+1] - numbers[i]) < threshold:
5: ✓             return True
6: ✓     return False
```

## Complete Test File

```python
def has_close_elements(numbers, threshold):
    numbers = sorted(numbers)
    for i in range(len(numbers) - 1):
        if abs(numbers[i+1] - numbers[i]) < threshold:
            return True
    return False

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = has_close_elements([1.0, 2.0, 3.0], 1.5)
        assert result == True, f"Test 1 failed: got {result}, expected {True}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = has_close_elements([10.0, 12.0, 15.0], 1.5)
        assert result == False, f"Test 2 failed: got {result}, expected {False}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = has_close_elements([5.0, 5.0], 0.1)
        assert result == True, f"Test 3 failed: got {result}, expected {True}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = has_close_elements([], 2.0)
        assert result == False, f"Test 4 failed: got {result}, expected {False}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = has_close_elements([0.0, 0.5, 1.1, 2.2], 0.6)
        assert result == True, f"Test 5 failed: got {result}, expected {True}"
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
