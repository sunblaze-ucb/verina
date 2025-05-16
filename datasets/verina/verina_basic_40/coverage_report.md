# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def secondSmallest(s):
2: ✓     s_copy = s[:]
3: ✓     s_sorted = sorted(s_copy)
4: ✓     smallest = s_sorted[0]
5: ✓     for num in s_sorted:
6: ✓         if num > smallest:
7: ✓             return num
```

## Complete Test File

```python
def secondSmallest(s):
    s_copy = s[:]
    s_sorted = sorted(s_copy)
    smallest = s_sorted[0]
    for num in s_sorted:
        if num > smallest:
            return num

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = secondSmallest([5, 3, 1, 4, 2])
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = secondSmallest([7, 2, 5, 3])
        assert result == 3, f"Test 2 failed: got {result}, expected {3}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = secondSmallest([10, 20])
        assert result == 20, f"Test 3 failed: got {result}, expected {20}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = secondSmallest([20, 10])
        assert result == 20, f"Test 4 failed: got {result}, expected {20}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = secondSmallest([3, 1, 2])
        assert result == 2, f"Test 5 failed: got {result}, expected {2}"
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
