# Coverage Report

Total executable lines: 10
Covered lines: 10
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def productExceptSelf(nums):
2: ✓     n = len(nums)
3: ✓     output = [1] * n
4: ✓     for i in range(1, n):
5: ✓         output[i] = output[i - 1] * nums[i - 1]
6: ✓     right_product = 1
7: ✓     for i in range(n - 1, -1, -1):
8: ✓         output[i] *= right_product
9: ✓         right_product *= nums[i]
10: ✓     return output
```

## Complete Test File

```python
def productExceptSelf(nums):
    n = len(nums)
    output = [1] * n
    for i in range(1, n):
        output[i] = output[i - 1] * nums[i - 1]
    right_product = 1
    for i in range(n - 1, -1, -1):
        output[i] *= right_product
        right_product *= nums[i]
    return output

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = productExceptSelf([1, 2, 3, 4])
        assert result == [24, 12, 8, 6], f"Test 1 failed: got {result}, expected {[24, 12, 8, 6]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = productExceptSelf([-1, 1, 0, -3, 3])
        assert result == [0, 0, 9, 0, 0], f"Test 2 failed: got {result}, expected {[0, 0, 9, 0, 0]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = productExceptSelf([2, 3])
        assert result == [3, 2], f"Test 3 failed: got {result}, expected {[3, 2]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = productExceptSelf([5, 5, 5, 5])
        assert result == [125, 125, 125, 125], f"Test 4 failed: got {result}, expected {[125, 125, 125, 125]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = productExceptSelf([0, 1, 2])
        assert result == [2, 0, 0], f"Test 5 failed: got {result}, expected {[2, 0, 0]}"
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
