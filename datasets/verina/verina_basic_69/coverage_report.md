# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def LinearSearch(a, e):
2: ✓     def helper(index):
3: ✓         if a[index] == e:
4: ✓             return index
5: ✓         return helper(index + 1)
6: ✓     return helper(0)
```

## Complete Test File

```python
def LinearSearch(a, e):
    def helper(index):
        if a[index] == e:
            return index
        return helper(index + 1)
    return helper(0)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = LinearSearch([1, 2, 3, 4, 5], 3)
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = LinearSearch([10, 20, 30, 40, 50], 10)
        assert result == 0, f"Test 2 failed: got {result}, expected {0}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = LinearSearch([5, 4, 3, 2, 1], 1)
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = LinearSearch([-1, 0, 1, 2], -1)
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = LinearSearch([7, 8, 7, 9, 7], 7)
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
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
