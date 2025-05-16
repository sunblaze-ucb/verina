# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def semiOrderedPermutation(nums):
2: ✓     n = len(nums)
3: ✓     pos1 = nums.index(1)
4: ✓     posN = nums.index(n)
5: ✓     swaps = pos1 + (n - 1 - posN)
6: ✓     if pos1 > posN:
7: ✓         swaps -= 1
8: ✓     return swaps
```

## Complete Test File

```python
def semiOrderedPermutation(nums):
    n = len(nums)
    pos1 = nums.index(1)
    posN = nums.index(n)
    swaps = pos1 + (n - 1 - posN)
    if pos1 > posN:
        swaps -= 1
    return swaps

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = semiOrderedPermutation([2, 1, 4, 3])
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = semiOrderedPermutation([2, 4, 1, 3])
        assert result == 3, f"Test 2 failed: got {result}, expected {3}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = semiOrderedPermutation([1, 3, 4, 2, 5])
        assert result == 0, f"Test 3 failed: got {result}, expected {0}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = semiOrderedPermutation([3, 1, 2])
        assert result == 2, f"Test 4 failed: got {result}, expected {2}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = semiOrderedPermutation([2, 3, 1, 5, 4])
        assert result == 3, f"Test 5 failed: got {result}, expected {3}"
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
