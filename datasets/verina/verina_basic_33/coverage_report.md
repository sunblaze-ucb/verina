# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def smallestMissingNumber(s):
2: ✓     expected = 0
3: ✓     for num in s:
4: ✓         if num != expected:
5: ✓             return expected
6: ✓         expected += 1
7: ✓     return expected
```

## Complete Test File

```python
def smallestMissingNumber(s):
    expected = 0
    for num in s:
        if num != expected:
            return expected
        expected += 1
    return expected

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = smallestMissingNumber([0, 1, 2, 6, 9])
        assert result == 3, f"Test 1 failed: got {result}, expected {3}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = smallestMissingNumber([4, 5, 10, 11])
        assert result == 0, f"Test 2 failed: got {result}, expected {0}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = smallestMissingNumber([0, 1, 2, 3, 4, 5])
        assert result == 6, f"Test 3 failed: got {result}, expected {6}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = smallestMissingNumber([])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = smallestMissingNumber([0, 2, 3, 4])
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
