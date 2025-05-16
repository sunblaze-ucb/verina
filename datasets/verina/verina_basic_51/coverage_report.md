# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def BinarySearch(a, key):
2: ✓     low = 0
3: ✓     high = len(a)
4: ✓     while low < high:
5: ✓         mid = (low + high) // 2
6: ✓         if a[mid] < key:
7: ✓             low = mid + 1
8: ✓         else:
9: ✓             high = mid
10: ✓     return low
```

## Complete Test File

```python
def BinarySearch(a, key):
    low = 0
    high = len(a)
    while low < high:
        mid = (low + high) // 2
        if a[mid] < key:
            low = mid + 1
        else:
            high = mid
    return low

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = BinarySearch([1, 3, 5, 7, 9], 5)
        assert result == '2', f"Test 1 failed: got {result}, expected {'2'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = BinarySearch([1, 3, 5, 7, 9], 6)
        assert result == '3', f"Test 2 failed: got {result}, expected {'3'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = BinarySearch([2, 4, 6, 8], 1)
        assert result == '0', f"Test 3 failed: got {result}, expected {'0'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = BinarySearch([2, 4, 6, 8], 10)
        assert result == '4', f"Test 4 failed: got {result}, expected {'4'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = BinarySearch([1, 1, 1, 1], 1)
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
