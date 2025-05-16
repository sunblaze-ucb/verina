# Coverage Report

Total executable lines: 12
Covered lines: 12
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def findMajorityElement(lst):
2: ✓     candidate, count = None, 0
3: ✓     for num in lst:
4: ✓         if count == 0:
5: ✓             candidate = num
6: ✓             count = 1
7: ✓         elif num == candidate:
8: ✓             count += 1
9: ✓         else:
10: ✓             count -= 1
11: ✓     if candidate is not None and lst.count(candidate) > len(lst) // 2:
12: ✓         return candidate
13: ✓     return -1
```

## Complete Test File

```python
def findMajorityElement(lst):
    candidate, count = None, 0
    for num in lst:
        if count == 0:
            candidate = num
            count = 1
        elif num == candidate:
            count += 1
        else:
            count -= 1
    if candidate is not None and lst.count(candidate) > len(lst) // 2:
        return candidate
    return -1

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = findMajorityElement([1, 2, 1, 1])
        assert result == 1, f"Test 1 failed: got {result}, expected {1}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = findMajorityElement([1, 2, 3, 4])
        assert result == -1, f"Test 2 failed: got {result}, expected {-1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = findMajorityElement([2, 2, 2, 2, 3, 3])
        assert result == 2, f"Test 3 failed: got {result}, expected {2}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = findMajorityElement([])
        assert result == -1, f"Test 4 failed: got {result}, expected {-1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = findMajorityElement([5, 5, 5, 5, 5, 5])
        assert result == 5, f"Test 5 failed: got {result}, expected {5}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = findMajorityElement([-1, -1, -1, 2, 2])
        assert result == -1, f"Test 6 failed: got {result}, expected {-1}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = findMajorityElement([-3, -3, -3, -3, 1])
        assert result == -3, f"Test 7 failed: got {result}, expected {-3}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
