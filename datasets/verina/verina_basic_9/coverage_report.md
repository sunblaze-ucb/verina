# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def hasCommonElement(a, b):
2: ✓     set_b = set(b)
3: ✓     for x in a:
4: ✓         if x in set_b:
5: ✓             return True
6: ✓     return False
```

## Complete Test File

```python
def hasCommonElement(a, b):
    set_b = set(b)
    for x in a:
        if x in set_b:
            return True
    return False

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = hasCommonElement([1, 2, 3], [4, 5, 6])
        assert result == False, f"Test 1 failed: got {result}, expected {False}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = hasCommonElement([1, 2, 3], [3, 4, 5])
        assert result == True, f"Test 2 failed: got {result}, expected {True}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = hasCommonElement([7, 8, 9], [10, 11, 7])
        assert result == True, f"Test 3 failed: got {result}, expected {True}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = hasCommonElement([1, 2, 3, 4], [5, 6, 7, 8])
        assert result == False, f"Test 4 failed: got {result}, expected {False}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = hasCommonElement([1, 2, 3, 4], [4, 5, 6])
        assert result == True, f"Test 5 failed: got {result}, expected {True}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = hasCommonElement([1, 1, 1], [1, 2, 1])
        assert result == True, f"Test 6 failed: got {result}, expected {True}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = hasCommonElement([0], [0])
        assert result == True, f"Test 7 failed: got {result}, expected {True}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = hasCommonElement([0], [-1, 1])
        assert result == False, f"Test 8 failed: got {result}, expected {False}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
