# Coverage Report

Total executable lines: 5
Covered lines: 5
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def isOddAtIndexOdd(a):
2: ✓     for i in range(len(a)):
3: ✓         if i % 2 == 1 and a[i] % 2 == 0:
4: ✓             return False
5: ✓     return True
```

## Complete Test File

```python
def isOddAtIndexOdd(a):
    for i in range(len(a)):
        if i % 2 == 1 and a[i] % 2 == 0:
            return False
    return True

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = isOddAtIndexOdd([1, 2, 3, 4, 5])
        assert result == False, f"Test 1 failed: got {result}, expected {False}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = isOddAtIndexOdd([1, 3, 5, 7, 9])
        assert result == True, f"Test 2 failed: got {result}, expected {True}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = isOddAtIndexOdd([2, 4, 6, 8, 10])
        assert result == False, f"Test 3 failed: got {result}, expected {False}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = isOddAtIndexOdd([])
        assert result == True, f"Test 4 failed: got {result}, expected {True}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = isOddAtIndexOdd([7])
        assert result == True, f"Test 5 failed: got {result}, expected {True}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = isOddAtIndexOdd([0, 1, 0, 1])
        assert result == True, f"Test 6 failed: got {result}, expected {True}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = isOddAtIndexOdd([0, 2, 4, 6])
        assert result == False, f"Test 7 failed: got {result}, expected {False}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
