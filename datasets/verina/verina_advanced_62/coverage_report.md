# Coverage Report

Total executable lines: 17
Covered lines: 17
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def rain(heights):
2: ✓     if not heights:
3: ✓         return 0
4: ✓     left, right = 0, len(heights) - 1
5: ✓     left_max, right_max = 0, 0
6: ✓     water = 0
7: ✓     while left <= right:
8: ✓         if heights[left] < heights[right]:
9: ✓             if heights[left] >= left_max:
10: ✓                 left_max = heights[left]
11: ✓             else:
12: ✓                 water += left_max - heights[left]
13: ✓             left += 1
14: ✓         else:
15: ✓             if heights[right] >= right_max:
16: ✓                 right_max = heights[right]
17: ✓             else:
18: ✓                 water += right_max - heights[right]
19: ✓             right -= 1
20: ✓     return water
```

## Complete Test File

```python
def rain(heights):
    if not heights:
        return 0
    left, right = 0, len(heights) - 1
    left_max, right_max = 0, 0
    water = 0
    while left <= right:
        if heights[left] < heights[right]:
            if heights[left] >= left_max:
                left_max = heights[left]
            else:
                water += left_max - heights[left]
            left += 1
        else:
            if heights[right] >= right_max:
                right_max = heights[right]
            else:
                water += right_max - heights[right]
            right -= 1
    return water

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = rain([0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1])
        assert result == 6, f"Test 1 failed: got {result}, expected {6}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = rain([4, 2, 0, 3, 2, 5])
        assert result == 9, f"Test 2 failed: got {result}, expected {9}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = rain([1, 1, 1])
        assert result == 0, f"Test 3 failed: got {result}, expected {0}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = rain([10, 5])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = rain([1, 10, 9, 11])
        assert result == 1, f"Test 5 failed: got {result}, expected {1}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = rain([])
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
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
