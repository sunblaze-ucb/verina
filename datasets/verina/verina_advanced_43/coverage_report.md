# Coverage Report

Total executable lines: 16
Covered lines: 16
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def maxStrength(nums):
2: ✓     from math import prod
3: ✓     if len(nums) == 1:
4: ✓         return nums[0]
5: ✓     pos = [x for x in nums if x > 0]
6: ✓     neg = [x for x in nums if x < 0]
7: ✓     # Build candidate subset if possible.
8: ✓     candidate_product = None
9: ✓     if pos or len(neg) >= 2:
10: ✓         neg_sorted = sorted(neg, key=abs)
11: ✓         if len(neg_sorted) % 2 == 1:
12: ✓             neg_sorted = neg_sorted[:-1]
13: ✓         subset = pos + neg_sorted
14: ✓         if subset:
15: ✓             candidate_product = prod(subset)
16: ✓     candidate_product = candidate_product if candidate_product is not None else float('-inf')
17: ✓     return max(candidate_product, max(nums))
```

## Complete Test File

```python
def maxStrength(nums):
    from math import prod
    if len(nums) == 1:
        return nums[0]
    pos = [x for x in nums if x > 0]
    neg = [x for x in nums if x < 0]
    # Build candidate subset if possible.
    candidate_product = None
    if pos or len(neg) >= 2:
        neg_sorted = sorted(neg, key=abs)
        if len(neg_sorted) % 2 == 1:
            neg_sorted = neg_sorted[:-1]
        subset = pos + neg_sorted
        if subset:
            candidate_product = prod(subset)
    candidate_product = candidate_product if candidate_product is not None else float('-inf')
    return max(candidate_product, max(nums))

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = maxStrength([-2])
        assert result == -2, f"Test 1 failed: got {result}, expected {-2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = maxStrength([3, -1, -5, 2, 5, -9])
        assert result == 1350, f"Test 2 failed: got {result}, expected {1350}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = maxStrength([-4, -5, -4])
        assert result == 20, f"Test 3 failed: got {result}, expected {20}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = maxStrength([0, -3, 4])
        assert result == 4, f"Test 4 failed: got {result}, expected {4}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = maxStrength([1, -1, -1])
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
