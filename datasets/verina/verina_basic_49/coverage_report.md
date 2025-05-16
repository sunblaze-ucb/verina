# Coverage Report

Total executable lines: 5
Covered lines: 5
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def findFirstOdd(a):
2: ✓     for i, num in enumerate(a):
3: ✓         if num % 2 != 0:
4: ✓             return (True, i)
5: ✓     return (False, -1)
```

## Complete Test File

```python
def findFirstOdd(a):
    for i, num in enumerate(a):
        if num % 2 != 0:
            return (True, i)
    return (False, -1)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = findFirstOdd([2, 4, 6, 8])
        assert result == 'none', f"Test 1 failed: got {result}, expected {'none'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = findFirstOdd([3, 4, 6, 8])
        assert result == 'some (0)', f"Test 2 failed: got {result}, expected {'some (0)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = findFirstOdd([2, 4, 5, 8])
        assert result == 'some (2)', f"Test 3 failed: got {result}, expected {'some (2)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = findFirstOdd([7])
        assert result == 'some (0)', f"Test 4 failed: got {result}, expected {'some (0)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = findFirstOdd([2])
        assert result == 'none', f"Test 5 failed: got {result}, expected {'none'}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = findFirstOdd([1, 2, 3])
        assert result == 'some (0)', f"Test 6 failed: got {result}, expected {'some (0)'}"
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
