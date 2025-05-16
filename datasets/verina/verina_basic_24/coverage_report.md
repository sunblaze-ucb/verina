# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def firstEvenOddDifference(a):
2: ✓     first_even = None
3: ✓     first_odd = None
4: ✓     for num in a:
5: ✓         if first_even is None and num % 2 == 0:
6: ✓             first_even = num
7: ✓         if first_odd is None and num % 2 != 0:
8: ✓             first_odd = num
9: ✓         if first_even is not None and first_odd is not None:
10: ✓             break
11: ✓     return first_even - first_odd
```

## Complete Test File

```python
def firstEvenOddDifference(a):
    first_even = None
    first_odd = None
    for num in a:
        if first_even is None and num % 2 == 0:
            first_even = num
        if first_odd is None and num % 2 != 0:
            first_odd = num
        if first_even is not None and first_odd is not None:
            break
    return first_even - first_odd

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = firstEvenOddDifference([2, 3, 4, 5])
        assert result == -1, f"Test 1 failed: got {result}, expected {-1}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = firstEvenOddDifference([1, 4, 6, 8])
        assert result == 3, f"Test 2 failed: got {result}, expected {3}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = firstEvenOddDifference([7, 2, 9, 4])
        assert result == -5, f"Test 3 failed: got {result}, expected {-5}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = firstEvenOddDifference([2, 2, 3, 3])
        assert result == -1, f"Test 4 failed: got {result}, expected {-1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = firstEvenOddDifference([1, 1, 2, 2])
        assert result == 1, f"Test 5 failed: got {result}, expected {1}"
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
