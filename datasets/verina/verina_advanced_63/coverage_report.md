# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def removeDuplicates(nums):
2: ✓     if not nums:
3: ✓         return 0
4: ✓     count = 1
5: ✓     for i in range(1, len(nums)):
6: ✓         if nums[i] != nums[i - 1]:
7: ✓             count += 1
8: ✓     return count
```

## Complete Test File

```python
def removeDuplicates(nums):
    if not nums:
        return 0
    count = 1
    for i in range(1, len(nums)):
        if nums[i] != nums[i - 1]:
            count += 1
    return count

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = removeDuplicates([1, 1, 2])
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = removeDuplicates([0, 0, 1, 1, 1, 2, 2, 3, 3, 4])
        assert result == 5, f"Test 2 failed: got {result}, expected {5}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = removeDuplicates([-1, -1, 0, 1, 2, 2, 3])
        assert result == 5, f"Test 3 failed: got {result}, expected {5}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = removeDuplicates([1, 2, 3, 4, 5])
        assert result == 5, f"Test 4 failed: got {result}, expected {5}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = removeDuplicates([1, 1, 1, 1])
        assert result == 1, f"Test 5 failed: got {result}, expected {1}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = removeDuplicates([])
        assert result == 0, f"Test 6 failed: got {result}, expected {0}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = removeDuplicates([1])
        assert result == 1, f"Test 7 failed: got {result}, expected {1}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = removeDuplicates([-100, -100, -100])
        assert result == 1, f"Test 8 failed: got {result}, expected {1}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    # Test case 9
    try:
        result = removeDuplicates([-100, -99, -99, -50, 0, 0, 100, 100])
        assert result == 5, f"Test 9 failed: got {result}, expected {5}"
        print(f"Test 9 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 9 failed: {e}")
        test_results.append(False)

    # Test case 10
    try:
        result = removeDuplicates([-1, 0, 0, 0, 1, 2, 2, 3, 4, 4, 5])
        assert result == 7, f"Test 10 failed: got {result}, expected {7}"
        print(f"Test 10 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 10 failed: {e}")
        test_results.append(False)

    # Test case 11
    try:
        result = removeDuplicates([100, 100, 100, 101, 102, 102, 103, 104, 105, 105])
        assert result == 6, f"Test 11 failed: got {result}, expected {6}"
        print(f"Test 11 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 11 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
