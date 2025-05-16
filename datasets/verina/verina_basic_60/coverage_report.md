# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def FindEvenNumbers(arr):
2: ✓     return [x for x in arr if x % 2 == 0]
```

## Complete Test File

```python
def FindEvenNumbers(arr):
    return [x for x in arr if x % 2 == 0]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = FindEvenNumbers([1, 2, 3, 4, 5, 6])
        assert result == [2, 4, 6], f"Test 1 failed: got {result}, expected {[2, 4, 6]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = FindEvenNumbers([0, -2, 3, -4, 7])
        assert result == [0, -2, -4], f"Test 2 failed: got {result}, expected {[0, -2, -4]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = FindEvenNumbers([1, 3, 5, 7])
        assert result == [], f"Test 3 failed: got {result}, expected {[]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = FindEvenNumbers([2, 4, 8, 10])
        assert result == [2, 4, 8, 10], f"Test 4 failed: got {result}, expected {[2, 4, 8, 10]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = FindEvenNumbers([])
        assert result == [], f"Test 5 failed: got {result}, expected {[]}"
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
