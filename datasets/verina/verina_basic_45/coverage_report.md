# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def findProduct(lst):
2: ✓     even = None
3: ✓     odd = None
4: ✓     for num in lst:
5: ✓         if even is None and num % 2 == 0:
6: ✓             even = num
7: ✓         if odd is None and num % 2 != 0:
8: ✓             odd = num
9: ✓         if even is not None and odd is not None:
10: ✓             break
11: ✓     return even * odd
```

## Complete Test File

```python
def findProduct(lst):
    even = None
    odd = None
    for num in lst:
        if even is None and num % 2 == 0:
            even = num
        if odd is None and num % 2 != 0:
            odd = num
        if even is not None and odd is not None:
            break
    return even * odd

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = findProduct([2, 3, 4, 5])
        assert result == 6, f"Test 1 failed: got {result}, expected {6}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = findProduct([2, 4, 3, 6])
        assert result == 6, f"Test 2 failed: got {result}, expected {6}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = findProduct([1, 2, 5, 4])
        assert result == 2, f"Test 3 failed: got {result}, expected {2}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
