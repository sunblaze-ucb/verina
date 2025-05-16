# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def majorityElement(xs):
2: ✓     count = 0
3: ✓     candidate = None
4: ✓     for num in xs:
5: ✓         if count == 0:
6: ✓             candidate = num
7: ✓             count = 1
8: ✓         elif candidate == num:
9: ✓             count += 1
10: ✓         else:
11: ✓             count -= 1
12: ✓     return candidate
```

## Complete Test File

```python
def majorityElement(xs):
    count = 0
    candidate = None
    for num in xs:
        if count == 0:
            candidate = num
            count = 1
        elif candidate == num:
            count += 1
        else:
            count -= 1
    return candidate

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = majorityElement([3, 3, 4, 2, 3, 3, 3])
        assert result == 3, f"Test 1 failed: got {result}, expected {3}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = majorityElement([1, 1, 2, 1, 3, 1, 1])
        assert result == 1, f"Test 2 failed: got {result}, expected {1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = majorityElement([2, 2, 2, 1, 1])
        assert result == 2, f"Test 3 failed: got {result}, expected {2}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = majorityElement([9, 9, 9, 9, 1, 2, 3])
        assert result == 9, f"Test 4 failed: got {result}, expected {9}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = majorityElement([5, 5, 5, 5, 5, 6, 7])
        assert result == 5, f"Test 5 failed: got {result}, expected {5}"
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
