# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def findSmallest(s):
2: ✓     if not s:
3: ✓         return None
4: ✓     smallest = s[0]
5: ✓     for num in s[1:]:
6: ✓         if num < smallest:
7: ✓             smallest = num
8: ✓     return smallest
```

## Complete Test File

```python
def findSmallest(s):
    if not s:
        return None
    smallest = s[0]
    for num in s[1:]:
        if num < smallest:
            smallest = num
    return smallest

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = findSmallest([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5])
        assert result == 'some (1)', f"Test 1 failed: got {result}, expected {'some (1)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = findSmallest([0, 1, 2, 3, 4, 5])
        assert result == 'some (0)', f"Test 2 failed: got {result}, expected {'some (0)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = findSmallest([1])
        assert result == 'some (1)', f"Test 3 failed: got {result}, expected {'some (1)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = findSmallest([10, 10, 10])
        assert result == 'some (10)', f"Test 4 failed: got {result}, expected {'some (10)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = findSmallest([3, 2, 2, 2, 2, 2, 2, 1])
        assert result == 'some (1)', f"Test 5 failed: got {result}, expected {'some (1)'}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = findSmallest([0])
        assert result == 'some (0)', f"Test 6 failed: got {result}, expected {'some (0)'}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = findSmallest([100, 99, 98])
        assert result == 'some (98)', f"Test 7 failed: got {result}, expected {'some (98)'}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = findSmallest([])
        assert result == 'none', f"Test 8 failed: got {result}, expected {'none'}"
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
