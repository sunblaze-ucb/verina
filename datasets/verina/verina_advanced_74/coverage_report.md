# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def solution(nums):
2: ✓     total = 0
3: ✓     n = len(nums)
4: ✓     for i in range(n):
5: ✓         distinct = set()
6: ✓         for j in range(i, n):
7: ✓             distinct.add(nums[j])
8: ✓             total += len(distinct) ** 2
9: ✓     return total
```

## Complete Test File

```python
def solution(nums):
    total = 0
    n = len(nums)
    for i in range(n):
        distinct = set()
        for j in range(i, n):
            distinct.add(nums[j])
            total += len(distinct) ** 2
    return total

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = solution([1])
        assert result == 1, f"Test 1 failed: got {result}, expected {1}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = solution([1, 1, 1])
        assert result == 6, f"Test 2 failed: got {result}, expected {6}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = solution([1, 2, 1])
        assert result == 15, f"Test 3 failed: got {result}, expected {15}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = solution([1, 2, 3, 4])
        assert result == 50, f"Test 4 failed: got {result}, expected {50}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = solution([1, 2, 2, 3, 1])
        assert result == 62, f"Test 5 failed: got {result}, expected {62}"
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
