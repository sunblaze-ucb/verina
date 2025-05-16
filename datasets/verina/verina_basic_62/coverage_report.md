# Coverage Report

Total executable lines: 5
Covered lines: 5
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def Find(a, key):
2: ✓     for i, value in enumerate(a):
3: ✓         if value == key:
4: ✓             return i
5: ✓     return -1
```

## Complete Test File

```python
def Find(a, key):
    for i, value in enumerate(a):
        if value == key:
            return i
    return -1

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = Find([1, 2, 3, 4, 5], 3)
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = Find([5, 7, 5, 9], 5)
        assert result == 0, f"Test 2 failed: got {result}, expected {0}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = Find([2, 4, 6, 8], 5)
        assert result == -1, f"Test 3 failed: got {result}, expected {-1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = Find([], 10)
        assert result == -1, f"Test 4 failed: got {result}, expected {-1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = Find([0, -3, -1, -3], -3)
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
