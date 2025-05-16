# Coverage Report

Total executable lines: 5
Covered lines: 5
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def twoSum(nums, target):
2: ✓     for i in range(len(nums)):
3: ✓         for j in range(i + 1, len(nums)):
4: ✓             if nums[i] + nums[j] == target:
5: ✓                 return (i, j)
```

## Complete Test File

```python
def twoSum(nums, target):
    for i in range(len(nums)):
        for j in range(i + 1, len(nums)):
            if nums[i] + nums[j] == target:
                return (i, j)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = twoSum([2, 7, 11, 15], 9)
        assert result == '(0, 1)', f"Test 1 failed: got {result}, expected {'(0, 1)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = twoSum([3, 2, 4], 6)
        assert result == '(1, 2)', f"Test 2 failed: got {result}, expected {'(1, 2)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = twoSum([-1, 0, 1, 2], 1)
        assert result == '(0, 3)', f"Test 3 failed: got {result}, expected {'(0, 3)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = twoSum([5, 75, 25], 100)
        assert result == '(1, 2)', f"Test 4 failed: got {result}, expected {'(1, 2)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = twoSum([1, 2, 3, 4, 5], 9)
        assert result == '(3, 4)', f"Test 5 failed: got {result}, expected {'(3, 4)'}"
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
