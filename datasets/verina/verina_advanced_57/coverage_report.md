# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def nextGreaterElement(nums1, nums2):
2: ✓     next_greater = {}
3: ✓     stack = []
4: ✓     for num in nums2:
5: ✓         while stack and num > stack[-1]:
6: ✓             prev = stack.pop()
7: ✓             next_greater[prev] = num
8: ✓         stack.append(num)
9: ✓     for num in stack:
10: ✓         next_greater[num] = -1
11: ✓     return [next_greater[num] for num in nums1]
```

## Complete Test File

```python
def nextGreaterElement(nums1, nums2):
    next_greater = {}
    stack = []
    for num in nums2:
        while stack and num > stack[-1]:
            prev = stack.pop()
            next_greater[prev] = num
        stack.append(num)
    for num in stack:
        next_greater[num] = -1
    return [next_greater[num] for num in nums1]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = nextGreaterElement([4, 1, 2], [1, 3, 4, 2])
        assert result == [-1, 3, -1], f"Test 1 failed: got {result}, expected {[-1, 3, -1]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = nextGreaterElement([2, 4], [1, 2, 3, 4])
        assert result == [3, -1], f"Test 2 failed: got {result}, expected {[3, -1]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = nextGreaterElement([1], [1, 2])
        assert result == [2], f"Test 3 failed: got {result}, expected {[2]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = nextGreaterElement([5], [5, 4, 3, 2, 1])
        assert result == [-1], f"Test 4 failed: got {result}, expected {[-1]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = nextGreaterElement([1, 3, 5, 2, 4], [6, 5, 4, 3, 2, 1])
        assert result == [-1, -1, -1, -1, -1], f"Test 5 failed: got {result}, expected {[-1, -1, -1, -1, -1]}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = nextGreaterElement([1, 2, 3], [3, 2, 1, 4])
        assert result == [4, 4, 4], f"Test 6 failed: got {result}, expected {[4, 4, 4]}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = nextGreaterElement([4, 3, 2, 1], [4, 3, 2, 1])
        assert result == [-1, -1, -1, -1], f"Test 7 failed: got {result}, expected {[-1, -1, -1, -1]}"
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
