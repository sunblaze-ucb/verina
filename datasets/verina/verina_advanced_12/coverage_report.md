# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def firstDuplicate(lst):
2: ✓     seen = set()
3: ✓     for num in lst:
4: ✓         if num in seen:
5: ✓             return num
6: ✓         seen.add(num)
7: ✓     return -1
```

## Complete Test File

```python
def firstDuplicate(lst):
    seen = set()
    for num in lst:
        if num in seen:
            return num
        seen.add(num)
    return -1

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = firstDuplicate([1, 2, 3, 2, 4])
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = firstDuplicate([5, 1, 2, 3, 4, 5])
        assert result == 5, f"Test 2 failed: got {result}, expected {5}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = firstDuplicate([1, 2, 3, 4, 5])
        assert result == -1, f"Test 3 failed: got {result}, expected {-1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = firstDuplicate([7, 7, 7, 7])
        assert result == 7, f"Test 4 failed: got {result}, expected {7}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = firstDuplicate([])
        assert result == -1, f"Test 5 failed: got {result}, expected {-1}"
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
