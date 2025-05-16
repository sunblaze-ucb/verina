# Coverage Report

Total executable lines: 10
Covered lines: 10
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def increasingTriplet(nums):
2: ✓     first = float('inf')
3: ✓     second = float('inf')
4: ✓     for num in nums:
5: ✓         if num <= first:
6: ✓             first = num
7: ✓         elif num <= second:
8: ✓             second = num
9: ✓         else:
10: ✓             return True
11: ✓     return False
```

## Complete Test File

```python
def increasingTriplet(nums):
    first = float('inf')
    second = float('inf')
    for num in nums:
        if num <= first:
            first = num
        elif num <= second:
            second = num
        else:
            return True
    return False

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = increasingTriplet([1, 2, 3])
        assert result == True, f"Test 1 failed: got {result}, expected {True}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = increasingTriplet([5, 4, 3, 2, 1])
        assert result == False, f"Test 2 failed: got {result}, expected {False}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = increasingTriplet([2, 1, 5, 0, 4, 6])
        assert result == True, f"Test 3 failed: got {result}, expected {True}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = increasingTriplet([1, 5, 0, 4, 1, 3])
        assert result == True, f"Test 4 failed: got {result}, expected {True}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = increasingTriplet([5, 4, 3])
        assert result == False, f"Test 5 failed: got {result}, expected {False}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = increasingTriplet([])
        assert result == False, f"Test 6 failed: got {result}, expected {False}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
