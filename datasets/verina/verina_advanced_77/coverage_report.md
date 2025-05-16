# Coverage Report

Total executable lines: 18
Covered lines: 18
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def trapRainWater(height):
2: ✓     n = len(height)
3: ✓     if n == 0:
4: ✓         return 0
5: ✓     left = 0
6: ✓     right = n - 1
7: ✓     left_max = height[left]
8: ✓     right_max = height[right]
9: ✓     water = 0
10: ✓     while left < right:
11: ✓         if left_max < right_max:
12: ✓             left += 1
13: ✓             left_max = max(left_max, height[left])
14: ✓             water += left_max - height[left]
15: ✓         else:
16: ✓             right -= 1
17: ✓             right_max = max(right_max, height[right])
18: ✓             water += right_max - height[right]
19: ✓     return water
```

## Complete Test File

```python
def trapRainWater(height):
    n = len(height)
    if n == 0:
        return 0
    left = 0
    right = n - 1
    left_max = height[left]
    right_max = height[right]
    water = 0
    while left < right:
        if left_max < right_max:
            left += 1
            left_max = max(left_max, height[left])
            water += left_max - height[left]
        else:
            right -= 1
            right_max = max(right_max, height[right])
            water += right_max - height[right]
    return water

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = trapRainWater([0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1])
        assert result == 6, f"Test 1 failed: got {result}, expected {6}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = trapRainWater([4, 2, 0, 3, 2, 5])
        assert result == 9, f"Test 2 failed: got {result}, expected {9}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = trapRainWater([1, 0, 2])
        assert result == 1, f"Test 3 failed: got {result}, expected {1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = trapRainWater([3, 0, 1, 3, 0, 5])
        assert result == 8, f"Test 4 failed: got {result}, expected {8}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = trapRainWater([0, 1, 2, 3, 4, 5])
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = trapRainWater([])
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
