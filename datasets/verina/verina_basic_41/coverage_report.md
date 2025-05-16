# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def hasOnlyOneDistinctElement(a):
2: ✓     return not a or len(set(a)) == 1
```

## Complete Test File

```python
def hasOnlyOneDistinctElement(a):
    return not a or len(set(a)) == 1

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = hasOnlyOneDistinctElement([1, 1, 1])
        assert result == True, f"Test 1 failed: got {result}, expected {True}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = hasOnlyOneDistinctElement([1, 2, 1])
        assert result == False, f"Test 2 failed: got {result}, expected {False}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = hasOnlyOneDistinctElement([3, 4, 5, 6])
        assert result == False, f"Test 3 failed: got {result}, expected {False}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = hasOnlyOneDistinctElement([7])
        assert result == True, f"Test 4 failed: got {result}, expected {True}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = hasOnlyOneDistinctElement([0, 0, 0, 0])
        assert result == True, f"Test 5 failed: got {result}, expected {True}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = hasOnlyOneDistinctElement([0, 0, 1, 0])
        assert result == False, f"Test 6 failed: got {result}, expected {False}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
