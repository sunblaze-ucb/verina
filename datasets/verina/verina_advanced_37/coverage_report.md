# Coverage Report

Total executable lines: 10
Covered lines: 10
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def majorityElement(nums):
2: ✓     candidate, count = None, 0
3: ✓     for num in nums:
4: ✓         if count == 0:
5: ✓             candidate = num
6: ✓             count = 1
7: ✓         elif num == candidate:
8: ✓             count += 1
9: ✓         else:
10: ✓             count -= 1
11: ✓     return candidate
```

## Complete Test File

```python
def majorityElement(nums):
    candidate, count = None, 0
    for num in nums:
        if count == 0:
            candidate = num
            count = 1
        elif num == candidate:
            count += 1
        else:
            count -= 1
    return candidate

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = majorityElement([3, 2, 3])
        assert result == 3, f"Test 1 failed: got {result}, expected {3}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = majorityElement([2, 2, 1, 1, 1, 2, 2])
        assert result == 2, f"Test 2 failed: got {result}, expected {2}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = majorityElement([1])
        assert result == 1, f"Test 3 failed: got {result}, expected {1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = majorityElement([4, 4, 4, 4, 4, 2, 2, 3, 3])
        assert result == 4, f"Test 4 failed: got {result}, expected {4}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = majorityElement([9, 8, 9, 9, 7, 9, 6, 9, 9])
        assert result == 9, f"Test 5 failed: got {result}, expected {9}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = majorityElement([0, 0, 0, 0, 1])
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = majorityElement([100000, 100000, 100000, 100000, -100000])
        assert result == 100000, f"Test 7 failed: got {result}, expected {100000}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = majorityElement([-1, -1, -1, -1, 0, 1, 2])
        assert result == -1, f"Test 8 failed: got {result}, expected {-1}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    # Test case 9
    try:
        result = majorityElement([5, 5, 5, 5, 5, 5, 5])
        assert result == 5, f"Test 9 failed: got {result}, expected {5}"
        print(f"Test 9 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 9 failed: {e}")
        test_results.append(False)

    # Test case 10
    try:
        result = majorityElement([1, 2, 3, 3, 3, 3, 3])
        assert result == 3, f"Test 10 failed: got {result}, expected {3}"
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
