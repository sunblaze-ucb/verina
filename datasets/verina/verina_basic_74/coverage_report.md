# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def maxArray(a):
2: ✓     max_val = a[0]
3: ✓     for num in a:
4: ✓         if num > max_val:
5: ✓             max_val = num
6: ✓     return max_val
```

## Complete Test File

```python
def maxArray(a):
    max_val = a[0]
    for num in a:
        if num > max_val:
            max_val = num
    return max_val

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = maxArray([1, 2, 3, 4, 5])
        assert result == 5, f"Test 1 failed: got {result}, expected {5}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = maxArray([5, 3, 4, 1, 2])
        assert result == 5, f"Test 2 failed: got {result}, expected {5}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = maxArray([7])
        assert result == 7, f"Test 3 failed: got {result}, expected {7}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = maxArray([-1, -5, -3, -4])
        assert result == -1, f"Test 4 failed: got {result}, expected {-1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = maxArray([-10, -20, -30, -5, -15])
        assert result == -5, f"Test 5 failed: got {result}, expected {-5}"
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
