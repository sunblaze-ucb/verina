# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def removeElement(lst, target):
2: ✓     return [x for x in lst if x != target]
```

## Complete Test File

```python
def removeElement(lst, target):
    return [x for x in lst if x != target]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = removeElement([1, 2, 3, 2, 4], 2)
        assert result == [1, 3, 4], f"Test 1 failed: got {result}, expected {[1, 3, 4]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = removeElement([5, 5, 5, 5], 5)
        assert result == [], f"Test 2 failed: got {result}, expected {[]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = removeElement([7, 8, 9], 4)
        assert result == [7, 8, 9], f"Test 3 failed: got {result}, expected {[7, 8, 9]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = removeElement([], 3)
        assert result == [], f"Test 4 failed: got {result}, expected {[]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = removeElement([0, 1, 0, 2, 0], 0)
        assert result == [1, 2], f"Test 5 failed: got {result}, expected {[1, 2]}"
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
